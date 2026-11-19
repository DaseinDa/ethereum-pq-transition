"""Small public-input and provenance helpers for the fixed four-owner C profile."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

from build_provenance import file_path, sha

C_KEY = "3f84335f8b7301181f37e3080cb81fc5d8444952574e0e90cd2a277d12bd2825"
VERSION = 0x80000008
HEADER = bytes.fromhex("000480000008")
MAX_CARRIER = 196608
BINARIES = ["bin/pq-migrate-tree", "bin/aggregate-verify", "bin/aggregate-corpus",
            "bin/aggregate-periodic-check", "lib/libpq_migrate_tree.so"]


def verify_package(root):
    root = Path(root)
    package = root / "prover/aggregate"
    manifest = json.loads((package / "SOURCE.json").read_text(encoding="utf-8"))
    if manifest.get("format") != 1 or manifest["identities"]["aggregateC"] != C_KEY:
        raise ValueError("aggregate source identity mismatch")
    for relative, row in manifest["imports"].items():
        path = file_path(package, relative)
        if not path.is_file() or path.stat().st_size != row["bytes"] or sha(path) != row["sha256"]:
            raise ValueError("imported aggregate source mismatch: " + relative)
    imported = {p.relative_to(package).as_posix() for p in (package / "src").rglob("*") if p.is_file()}
    expected = {p for p in manifest["imports"] if p.startswith("src/")}
    if imported != expected or len(imported) != 58:
        raise ValueError("aggregate source inventory mismatch")
    for relative, digest in manifest["sharedInputs"].items():
        if sha(file_path(root, relative)) != digest:
            raise ValueError("aggregate shared input mismatch: " + relative)
    for relative, row in manifest["fixture"].items():
        path = file_path(package / "fixtures/four-owner", relative)
        if sha(path) != row["sha256"] or path.stat().st_size != row["bytes"]:
            raise ValueError("aggregate fixture mismatch: " + relative)
    return manifest


def statement_from_pis(pis):
    if len(pis) != 4:
        raise ValueError("the aggregate profile requires exactly four owners")
    owners = set()
    for pi in pis:
        if len(pi) != 198:
            raise ValueError("each public input must be exactly 198 bytes")
        if int.from_bytes(pi[125:129], "big") != VERSION:
            raise ValueError("each F proof must use aggregate research version 0x80000008")
        owners.add(pi[64:84])
    if len(owners) != 4:
        raise ValueError("the aggregate profile requires four distinct owners")
    return HEADER + b"".join(pis)


def read_owner(path):
    """Read only exported F and PI; never copy an owner's witness or diagnostic tree."""
    path = Path(path)
    pi_path = path / "statement/pi198.hex"
    if pi_path.stat().st_size > 400:
        raise ValueError("oversized PI hex file")
    pi = bytes.fromhex(pi_path.read_text(encoding="ascii").strip())
    proof_path = path / "f/proof.postcard"
    size = proof_path.stat().st_size
    if not 0 < size <= MAX_CARRIER:
        raise ValueError("F proof exceeds the public carrier limit")
    proof = proof_path.read_bytes()
    record_path = path / "PROOF.json"
    public = False
    if record_path.exists():
        if record_path.stat().st_size > 1024 * 1024:
            raise ValueError("oversized owner proof record")
        public = json.loads(record_path.read_text(encoding="utf-8")).get("publicTestOnly") is True
    return pi, proof, public


def available_gib():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) / 1024 ** 2
    raise RuntimeError("MemAvailable is unavailable")


def clean_environment(**extra):
    env = dict(os.environ)
    for key in list(env):
        if key.startswith(("PQ_", "CARGO_", "RUST", "LD_")):
            env.pop(key)
    env.update(PYTHONDONTWRITEBYTECODE="1", **extra)
    return env


def run_logged(argv, *, cwd, env, log, memory_gib=1):
    """Linux subprocess with an address-space cap and group cleanup on cancellation."""
    if sys.platform != "linux":
        raise RuntimeError("aggregate native commands require Linux")
    import resource
    def limits():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        cap = int(memory_gib * 1024 ** 3)
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
    start = time.monotonic()
    with Path(str(log) + ".out").open("xb") as stdout, Path(str(log) + ".err").open("xb") as stderr:
        proc = subprocess.Popen(list(map(str, argv)), cwd=cwd, env=env, stdout=stdout, stderr=stderr,
                                stdin=subprocess.DEVNULL, start_new_session=True, preexec_fn=limits)
        try:
            code = proc.wait()
        except BaseException:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()
            raise
    result = {"argv": list(map(str, argv)), "exit": code, "seconds": time.monotonic() - start,
              "addressSpaceLimitGiB": memory_gib}
    if code:
        raise RuntimeError("aggregate command failed (" + str(code) + "); see " + str(log))
    return result
