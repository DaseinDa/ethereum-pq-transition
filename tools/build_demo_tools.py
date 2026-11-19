#!/usr/bin/env python3
"""Build provisioning and signature-audit helpers against the pinned client sources."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from dependency_integrity import verify_bundle, verify_git
from build_provenance import capture_source, verify_build, verify_source
from heavy_job import heavy_job


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", type=Path, required=True)
    ap.add_argument("--dependencies", type=Path, required=True)
    ap.add_argument("--expect-cache-sha256", required=True)
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    a = ap.parse_args()
    with heavy_job(a.lock, owner="pq-migrate-demo-tools-build"):
        build_tools(a)


def build_tools(a):
    verify_bundle(a.dependencies.resolve(), expected_manifest_sha256=a.expect_cache_sha256)
    root = Path(__file__).resolve().parents[1]
    source_identity = capture_source(root)
    build = a.build.resolve()
    verify_git(a.dependencies.resolve(), cargo_override=build / "cargo")
    client = json.loads((build / "BUILD.json").read_text())
    verify_build(root, client, ["bin/geth", "bin/ream", "lib/libpq_final_native.so", "lib/libpq_migrate_tree.so"], build, identity=source_identity)
    if client.get("dependencyManifestSHA256") != a.expect_cache_sha256.lower():
        raise ValueError("client build used a different dependency bundle")
    for name in ("geth", "ream"):
        expected = json.loads((root / "client" / name / "files.sha256.json").read_text())
        actual = {p.relative_to(build / name).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in (build / name).rglob("*") if p.is_file() and ".git" not in p.relative_to(build / name).parts}
        if actual != expected:
            raise ValueError("client source changed after validation: " + name)
    logs = build / "demo-tool-logs"
    logs.mkdir(exist_ok=False)
    flags = f"-C target-cpu=x86-64-v3 -C target-feature=+pclmulqdq --remap-path-prefix={build}=/build"
    env = dict(os.environ, CARGO_HOME=str(build / "cargo"), CARGO_NET_OFFLINE="true",
               RUSTUP_TOOLCHAIN="1.98.0", CARGO_TARGET_DIR=str(build / "ream-target"),
               CARGO_BUILD_JOBS="2", RUSTFLAGS=flags, GOTOOLCHAIN="local", GOMAXPROCS="2",
               GOMODCACHE=str(build / "go-mod"), GOCACHE=str(build / "go-build"),
               GOPROXY=(a.dependencies.resolve() / "go-proxy").as_uri(), GOSUMDB="off",
               GOFLAGS="-mod=readonly")
    commands = [
        ("chain-tools", ["cargo", "build", "--release", "--locked", "--offline", "-p", "ream-chain-lean", "--features", "reth",
                         "--example", "profile_tool", "--example", "profile_tool_three", "--example", "export_signed"], build / "ream"),
        ("key-tools", ["cargo", "build", "--release", "--locked", "--offline", "-p", "ream-post-quantum-crypto",
                       "--example", "fresh_public_keys", "--example", "audit_history"], build / "ream"),
        ("carrier-tool", ["go", "build", "-p", "2", "-trimpath", "-buildvcs=false", "-o", str(build / "bin/pqlean-txs"), str(root / "demo/transactions.go")], build / "geth"),
        ("n1-carrier-tool", ["go", "build", "-p", "2", "-trimpath", "-buildvcs=false", "-o", str(build / "bin/pq-n1-txs"), str(root / "demo/n1_transactions.go")], build / "geth"),
    ]
    result = {"status": "RUNNING", "commands": [], "binaries": {}, "sourceIdentity": source_identity,
              "dependencyManifestSHA256": a.expect_cache_sha256.lower()}
    try:
        for name, argv, cwd in commands:
            start = time.monotonic()
            with (logs / (name + ".out")).open("xb") as stdout, (logs / (name + ".err")).open("xb") as stderr:
                p = subprocess.run(argv, cwd=cwd, env=env, stdout=stdout, stderr=stderr)
            result["commands"].append({"name": name, "exit": p.returncode, "seconds": time.monotonic() - start})
            if p.returncode:
                raise RuntimeError(name + " failed")
        for name in ["profile_tool", "profile_tool_three", "export_signed", "fresh_public_keys", "audit_history"]:
            target = build / "bin" / name.replace("_", "-")
            shutil.copy2(build / "ream-target/release/examples" / name, target)
        for name in ["profile-tool", "profile-tool-three", "export-signed", "fresh-public-keys", "audit-history", "pqlean-txs", "pq-n1-txs"]:
            result["binaries"][name] = hashlib.sha256((build / "bin" / name).read_bytes()).hexdigest()
        verify_source(root, source_identity)
        result["status"] = "PASS"
    except BaseException as error:
        result.update(status="FAIL", failure=str(error))
        raise
    finally:
        (build / "DEMO-TOOLS.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
