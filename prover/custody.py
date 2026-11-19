"""Anonymous Linux memory artifacts. No temporary files or tmpfs paths."""
import json
import os
from pathlib import Path


class MemoryArtifacts:
    def __init__(self):
        self.fds = {}

    def add(self, name, data=b""):
        key = "/pq-memory/" + name
        if key in self.fds:
            raise ValueError("duplicate memory artifact")
        fd = os.memfd_create("pq-custody", os.MFD_CLOEXEC)
        self.fds[key] = fd
        view = memoryview(data)
        while view:
            view = view[os.write(fd, view):]
        os.lseek(fd, 0, os.SEEK_SET)
        return Path(key)

    def path(self, name):
        return Path("/pq-memory") / name

    def read(self, name):
        fd = self.fds[str(self.path(name))]
        return os.pread(fd, os.fstat(fd).st_size, 0)

    def document(self, name):
        return json.loads(self.read(name))

    def environment(self):
        return {"PQ_CUSTODY_FDS": json.dumps(self.fds)}

    def close(self):
        for fd in self.fds.values():
            os.close(fd)
        self.fds.clear()

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()
