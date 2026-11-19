#!/usr/bin/env python3
"""Reconstruct pinned client sources using local archives only."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from audit_text import check_patch


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def prepare(name, cache, destination):
    definition = ROOT / "client" / name
    pin = json.loads((definition / "source.json").read_text())
    archive = cache / pin["archive"]
    if digest(archive) != pin["sha256"]:
        raise ValueError(f"{name}: upstream archive hash mismatch")
    manifest = definition / "files.sha256.json"
    if digest(manifest) != pin["treeManifestSHA256"]:
        raise ValueError(f"{name}: source manifest hash mismatch")
    destination.mkdir(parents=True, exist_ok=False)
    with tarfile.open(archive) as stream:
        stream.extractall(destination, filter="data")
    for patch in pin["patches"]:
        source = definition / patch["file"]
        if digest(source) != patch["sha256"]:
            raise ValueError(f"{name}: patch hash mismatch")
        check_patch(source)
        subprocess.run(["git", "apply", "--check", str(source)], cwd=destination, check=True)
        subprocess.run(["git", "apply", str(source)], cwd=destination, check=True)
    actual = {str(p.relative_to(destination)): digest(p)
              for p in destination.rglob("*") if p.is_file()}
    if actual != json.loads(manifest.read_text()):
        raise ValueError(f"{name}: reconstructed source differs from manifest")
    return {"client": name, "upstreamCommit": pin["commit"], "files": len(actual),
            "sourceManifestSHA256": pin["treeManifestSHA256"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    for name in ("geth", "ream"):
        print(json.dumps(prepare(name, args.cache.resolve(), args.out.resolve() / name)))


if __name__ == "__main__":
    main()
