#!/usr/bin/env python3
"""Build single-owner tools from an attested copy and authenticated offline cache."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from build_provenance import capture_source, copy_tracked, verify_source, sha
from dependency_integrity import verify_bundle
from heavy_job import heavy_job

ROOT = Path(__file__).resolve().parents[1]


def builder_command(builder, output, jobs, dependencies, expected_cache_sha256):
    """Bind the underlying builder to the same separately authenticated bundle."""
    return [sys.executable, "-B", str(builder), "--out", str(output), "--jobs", str(jobs),
            "--dependencies", str(dependencies), "--expect-cache-sha256", expected_cache_sha256]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--dependencies", type=Path, required=True)
    ap.add_argument("--expect-cache-sha256", required=True)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    args = ap.parse_args()
    if args.jobs < 1:
        ap.error("--jobs must be positive")
    out, deps = args.out.resolve(), args.dependencies.resolve()
    with heavy_job(args.lock, owner="pq-migrate-verified-prover-build"):
        identity = capture_source(ROOT)
        verify_bundle(deps, expected_manifest_sha256=args.expect_cache_sha256)
        out.mkdir(parents=True, exist_ok=False)
        source = out / "source"
        copy_tracked(ROOT, "", source, identity)
        command = builder_command(source / "tools/build_prover.py", out / "compiled",
                                  args.jobs, deps, args.expect_cache_sha256.lower())
        env = dict(os.environ, CARGO_NET_OFFLINE="true")
        for key in ("LD_PRELOAD", "LD_AUDIT", "CARGO_TARGET_DIR", "RUSTFLAGS"):
            env.pop(key, None)
        # The underlying builder remains independently maintained. Its products
        # are eligible for assembly only after this wrapper binds their inputs.
        subprocess.run(command, env=env, check=True)
        record = json.loads((out / "compiled/BUILD.json").read_text())
        if record.get("status") != "PASS":
            raise ValueError("prover build did not pass")
        verify_source(ROOT, identity)
        # Check copied inputs again: build scripts must not mutate their source.
        from build_provenance import check_files
        check_files(source, identity)
        shutil.copytree(out / "compiled/bin", out / "bin")
        for name, digest in record["binaries"].items():
            if sha(out / "bin" / name) != digest:
                raise ValueError("prover output changed: " + name)
        record.update(sourceIdentity=identity,
                      dependencyManifestSHA256=args.expect_cache_sha256.lower(),
                      buildEntrypoint="tools/build_verified_prover.py")
        (out / "BUILD.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
