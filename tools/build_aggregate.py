#!/usr/bin/env python3
"""Build the fixed four-owner C prover and native verifier from committed sources."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

from aggregate_support import BINARIES, C_KEY, clean_environment, run_logged, verify_package
from build_provenance import capture_source, copy_tracked, sha, verify_source
from dependency_integrity import verify_bundle, verify_git
from heavy_job import heavy_job

ROOT = Path(__file__).resolve().parents[1]


def build(a):
    if sys.platform != "linux":
        raise RuntimeError("native aggregate builds require Linux")
    identity = capture_source(ROOT)
    source = verify_package(ROOT)
    deps, out = a.dependencies.resolve(), a.out.resolve()
    verify_bundle(deps, expected_manifest_sha256=a.expect_cache_sha256)
    out.mkdir(parents=True, exist_ok=False)
    for name in ("bin", "lib", "logs"):
        (out / name).mkdir()
    record = {"status": "RUNNING", "sourceIdentity": identity, "commands": [],
              "aggregateSourceManifestSHA256": sha(ROOT / "prover/aggregate/SOURCE.json"),
              "dependencyManifestSHA256": sha(deps / "CACHE-SHA256.json"),
              "aggregateProfile": source["profile"], "aggregateKey": C_KEY}
    def save():
        (out / "BUILD.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    save()
    try:
        copy_tracked(ROOT, "prover", out / "source/prover", identity)
        shutil.copytree(deps / "cargo", out / "cargo")
        verify_git(deps, cargo_override=out / "cargo")
        env = clean_environment(CARGO_HOME=str(out / "cargo"), CARGO_NET_OFFLINE="true",
                                CARGO_TARGET_DIR=str(out / "target"), CARGO_BUILD_JOBS=str(a.jobs),
                                RUSTUP_TOOLCHAIN=a.toolchain,
                                RUSTFLAGS="-C target-cpu=x86-64 --remap-path-prefix=" + str(out) + "=/build",
                                RAYON_NUM_THREADS="2")
        compiler = subprocess.check_output(["rustc", "-vV"], env=env, text=True)
        if "release: 1.96.0\n" not in compiler or "commit-hash: " + source["profile"]["rustcCommit"] not in compiler:
            raise ValueError("aggregate sources require the recorded Rust 1.96.0 compiler")
        record["toolchains"] = {"rust": compiler}
        cwd = out / "source/prover/aggregate"
        def run(name, argv):
            result = run_logged(argv, cwd=cwd, env=env, log=out / "logs" / name, memory_gib=a.memory_gib)
            record["commands"].append({"name": name, **result})
            save()
        args = ["cargo", "build", "--profile", "optimized", "--locked", "--offline", "--lib"]
        for name in BINARIES[:-1]:
            args += ["--bin", Path(name).name]
        run("aggregate-build", args)
        for name in BINARIES:
            shutil.copyfile(out / "target/optimized" / Path(name).name, out / name)
            if name.startswith("bin/"):
                (out / name).chmod(0o755)
        fixture = cwd / "fixtures/four-owner"
        run("aggregate-periodic", [out / "bin/aggregate-periodic-check"])
        run("aggregate-genuine-fixture", [out / "bin/aggregate-verify", fixture / "carrier.bin", fixture / "statement.bin", "1"])
        run("aggregate-native-boundary", [sys.executable, "-B", ROOT / "tools/check_aggregate_native.py",
                                          "--library", out / "lib/libpq_migrate_tree.so", "--fixture", fixture,
                                          "--out", out / "native-check.json"])
        verify_source(ROOT, identity)
        verify_package(ROOT)
        record["binaries"] = {name: sha(out / name) for name in BINARIES}
        record["nativeCheckSHA256"] = sha(out / "native-check.json")
        record["status"] = "PASS"
    except BaseException as exc:
        record["status"], record["error"] = "FAIL", str(exc)
        raise
    finally:
        save()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dependencies", type=Path, required=True)
    ap.add_argument("--expect-cache-sha256", required=True, help="trusted hash of CACHE-SHA256.json")
    ap.add_argument("--out", type=Path, required=True, help="new build directory")
    ap.add_argument("--toolchain", default="1.96.0")
    ap.add_argument("--jobs", type=int, default=2, choices=range(1, 3))
    ap.add_argument("--memory-gib", type=int, default=8, choices=range(1, 41),
                    help="per-process address-space limit; raise only within the approved resource budget")
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    a = ap.parse_args()
    with heavy_job(a.lock, owner="pq-migrate-aggregate-build"):
        build(a)


if __name__ == "__main__":
    main()
