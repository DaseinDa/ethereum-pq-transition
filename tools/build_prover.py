#!/usr/bin/env python3
"""Compile the public-test prover and wallet tools offline from a verified dependency bundle, without changing fixed keys."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from dependency_integrity import verify_bundle, verify_git


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dependencies", type=Path, required=True, help="tools/cache.py output")
    ap.add_argument("--expect-cache-sha256", required=True, help="separately trusted CACHE-SHA256.json digest")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--jobs", type=int, default=2)
    a = ap.parse_args()
    if a.jobs < 1:
        ap.error("--jobs must be positive")
    root = Path(__file__).resolve().parents[1]
    out, deps = a.out.resolve(), a.dependencies.resolve()
    # Check the bundle and the AIR sources before creating any output.
    verify_bundle(deps, expected_manifest_sha256=a.expect_cache_sha256)
    for rel, digest in json.loads((root / "prover/air-source.sha256.json").read_text()).items():
        if hashlib.sha256((root / rel).read_bytes()).hexdigest() != digest:
            raise ValueError("AIR source identity changed: " + rel)
    out.mkdir(parents=True, exist_ok=False)
    (out / "logs").mkdir()
    (out / "bin").mkdir()
    # Build from a private copy of the verified Cargo cache; the input bundle is never handed to Cargo.
    cargo = out / "cargo"
    shutil.copytree(deps / "cargo", cargo)
    verify_git(deps, cargo_override=cargo)
    env = dict(os.environ, CARGO_HOME=str(cargo), CARGO_NET_OFFLINE="true", RUSTUP_TOOLCHAIN="1.98.0",
               CARGO_BUILD_JOBS=str(a.jobs), CARGO_TARGET_DIR=str(out / "target"),
               RUSTFLAGS=f"-C target-cpu=native --remap-path-prefix={root}=/src --remap-path-prefix={out}=/build --remap-path-prefix={cargo}=/cargo")
    record = {"status": "RUNNING", "commands": [], "binaries": {},
              "review": "loop-internal self-review; not independently reviewed",
              "dependencyManifestSHA256": hashlib.sha256((deps / "CACHE-SHA256.json").read_bytes()).hexdigest(),
              "gitCratesManifestSHA256": hashlib.sha256((deps / "GIT-CRATES.json").read_bytes()).hexdigest(),
              "toolchain": subprocess.check_output(["rustc", "--version"], env=env, text=True).strip(),
              "cargoLocks": {rel: hashlib.sha256((root / rel / "Cargo.lock").read_bytes()).hexdigest()
                             for rel in ["prover/leaf", "prover/tree", "wallet/crypto", "prover/final-verifier"]},
              "airSourceManifestSHA256": hashlib.sha256((root / "prover/air-source.sha256.json").read_bytes()).hexdigest()}
    try:
        for rel, binary, profile in [("prover/leaf", "pq-migrate-leaf", "optimized"),
                                     ("prover/tree", "pq-migrate-tree", "optimized"),
                                     ("wallet/crypto", "pq-test-crypto", "release"),
                                     ("prover/final-verifier", "pq-final-verify", "release")]:
            start = time.monotonic()
            with (out / "logs" / (binary + ".out")).open("xb") as stdout, (out / "logs" / (binary + ".err")).open("xb") as stderr:
                process = subprocess.run(["cargo", "build", "--locked", "--offline", "--profile", profile, "--bin", binary],
                                         cwd=root / rel, env=env, stdout=stdout, stderr=stderr)
            record["commands"].append({"binary": binary, "exit": process.returncode,
                                       "seconds": time.monotonic() - start})
            print(binary, process.returncode, flush=True)
            if process.returncode:
                raise RuntimeError(binary + " build failed")
            target = out / "bin" / binary
            shutil.copy2(out / "target" / profile / binary, target)
            record["binaries"][binary] = hashlib.sha256(target.read_bytes()).hexdigest()
        record["status"] = "PASS"
    except BaseException as error:
        record.update(status="FAIL", failure=str(error))
        raise
    finally:
        (out / "BUILD.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
