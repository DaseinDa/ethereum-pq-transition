"""Exclusive, fail-fast coordination for memory-intensive research jobs."""
from contextlib import contextmanager
import json
import os
from pathlib import Path
import socket
import time
import uuid


@contextmanager
def heavy_job(lock_path=Path.home() / "pq-heavy-job.lock", *, owner):
    """Never inherit another job's lock or remove an unrecognized/stale lock."""
    path = Path(lock_path).expanduser().absolute()
    token = str(uuid.uuid4())
    row = {"token": token, "owner": owner, "pid": os.getpid(),
           "host": socket.gethostname(), "started": time.time()}
    try:
        fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    except FileExistsError as exc:
        raise RuntimeError("heavy-job lock is occupied: " + str(path)) from exc
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(row, stream)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        yield row
    finally:
        try:
            current = json.loads(path.read_text(encoding="utf-8"))
            if current.get("token") == token:
                path.unlink()
        except (OSError, ValueError, AttributeError):
            # Missing/replaced locks are never permission to unlink another job.
            pass
