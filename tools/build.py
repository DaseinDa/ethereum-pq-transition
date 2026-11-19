#!/usr/bin/env python3
"""Build pinned Linux clients offline and run the selected migration regressions."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from dependency_integrity import verify_bundle, verify_git
from build_provenance import capture_source, copy_tracked, verify_build, verify_source
from heavy_job import heavy_job

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("sources", ROOT / "client/sources.py")
sources = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sources)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cache", type=Path, required=True, help="pinned upstream tar archives")
    ap.add_argument("--dependencies", type=Path, required=True, help="tools/cache.py output")
    ap.add_argument("--expect-cache-sha256", required=True, help="trusted SHA-256 of CACHE-SHA256.json")
    ap.add_argument("--aggregate-build", type=Path, help="verified tools/build_aggregate.py output; required for geth")
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    ap.add_argument("--out", type=Path, required=True, help="new build directory")
    ap.add_argument("--clients", choices=["geth", "ream", "all"], default="all")
    ap.add_argument("--proof", type=Path, help="optional newly generated F proof")
    ap.add_argument("--pi", type=Path, help="matching PI198 hex file")
    a = ap.parse_args()
    if bool(a.proof) != bool(a.pi):
        ap.error("--proof and --pi must be supplied together")
    if a.clients in ("geth", "all") and a.aggregate_build is None:
        ap.error("--aggregate-build is required for the four-owner batch verifier")
    with heavy_job(a.lock, owner="pq-migrate-client-build"):
        build(a)


def build(a):
    out, deps = a.out.resolve(), a.dependencies.resolve()
    source_identity = capture_source(ROOT)
    verify_bundle(deps, expected_manifest_sha256=a.expect_cache_sha256)
    if a.aggregate_build is not None:
        aggregate = a.aggregate_build.resolve()
        aggregate_record = json.loads((aggregate / "BUILD.json").read_text())
        verify_build(ROOT, aggregate_record, ["lib/libpq_migrate_tree.so"], aggregate, identity=source_identity)
        if aggregate_record.get("dependencyManifestSHA256") != a.expect_cache_sha256.lower():
            raise ValueError("aggregate build used a different dependency bundle")
    out.mkdir(parents=True, exist_ok=False)
    (out / "logs").mkdir()
    (out / "bin").mkdir()
    (out / "lib").mkdir()
    # Recreate a local Cargo cache; never give a build permission to mutate the input bundle.
    shutil.copytree(deps / "cargo", out / "cargo")
    verify_git(deps, cargo_override=out / "cargo")
    env = dict(os.environ, CARGO_HOME=str(out / "cargo"), CARGO_NET_OFFLINE="true",
               RUSTUP_TOOLCHAIN="1.98.0", CARGO_BUILD_JOBS="2", GOMAXPROCS="2",
               GOTOOLCHAIN="local", GOMODCACHE=str(out / "go-mod"), GOCACHE=str(out / "go-build"),
               GOPROXY=(deps / "go-proxy").as_uri(), GOSUMDB="off", GOFLAGS="-mod=readonly",
               CGO_ENABLED="1")
    for key in ("LD_PRELOAD", "LD_AUDIT", "CARGO_TARGET_DIR", "RUSTFLAGS"):
        env.pop(key, None)
    record = {"status": "RUNNING", "sourceIdentity": source_identity,
              "commands": [], "sources": [], "proofProvided": bool(a.proof),
              "dependencyManifestSHA256": sources.digest(deps / "CACHE-SHA256.json"),
              "gitCratesManifestSHA256": sources.digest(deps / "GIT-CRATES.json"),
              "toolchains": {key: subprocess.check_output(cmd, env=env, text=True).strip()
                             for key, cmd in [("go", ["go", "version"]), ("rust", ["rustc", "--version"])]}}
    if "go1.25.14 " not in record["toolchains"]["go"]:
        raise ValueError("this profile requires Go 1.25.14")
    if not record["toolchains"]["rust"].startswith("rustc 1.98.0 "):
        raise ValueError("this profile requires Rust 1.98.0")

    def save():
        (out / "BUILD.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(name, argv, cwd, extra=None):
        start = time.monotonic()
        with (out / "logs" / (name + ".out")).open("xb") as stdout, (out / "logs" / (name + ".err")).open("xb") as stderr:
            result = subprocess.run(list(map(str, argv)), cwd=cwd, env=dict(env, **(extra or {})), stdout=stdout, stderr=stderr)
        record["commands"].append({"name": name, "exit": result.returncode,
                                   "seconds": time.monotonic() - start})
        save()
        print(name, result.returncode, flush=True)
        if result.returncode:
            raise RuntimeError(name + " failed; see logs")

    try:
        names = ("geth", "ream") if a.clients == "all" else (a.clients,)
        for name in names:
            record["sources"].append(sources.prepare(name, a.cache.resolve(), out / name))
        if "geth" in names:
            copy_tracked(ROOT, "prover", out / "prover", source_identity)
            flags = "-C target-cpu=x86-64 --remap-path-prefix=" + str(out) + "=/build"
            native_env = {"CARGO_TARGET_DIR": str(out / "native-target"), "RUSTFLAGS": flags}
            run("native-build", ["cargo", "build", "--release", "--locked", "--offline"], out / "prover/native", native_env)
            run("native-test", ["cargo", "test", "--release", "--locked", "--offline", "--", "--test-threads=1"], out / "prover/native", native_env)
            shutil.copyfile(out / "native-target/release/libpq_final_native.so", out / "lib/libpq_final_native.so")
            shutil.copyfile(aggregate / "lib/libpq_migrate_tree.so", out / "lib/libpq_migrate_tree.so")
            record["aggregateBuild"] = aggregate_record
            go_env = {"CGO_LDFLAGS": "-L" + str(out / "lib"), "LD_LIBRARY_PATH": str(out / "lib")}
            go_env.update(PQ_BATCH_CARRIER=str(ROOT / "prover/aggregate/fixtures/four-owner/carrier.bin"),
                          PQ_BATCH_STATEMENT=str(ROOT / "prover/aggregate/fixtures/four-owner/statement.bin"),
                          PQ_BATCH_GATES_CARRIER=str(ROOT / "prover/aggregate/fixtures/four-owner-gates/carrier.bin"),
                          PQ_BATCH_GATES_STATEMENT=str(ROOT / "prover/aggregate/fixtures/four-owner-gates/statement.bin"))
            fixtures = out / "prover/final-verifier/fixtures"
            go_env.update(PQ_F_FIXTURES=str(fixtures),
                          PQ_F_PROOF=str(fixtures / "mode0/proof.postcard"),
                          PQ_F_PI=str(fixtures / "mode0/pi198.hex"))
            if a.proof:
                go_env.update(PQ_F_PROOF=str(a.proof.resolve()), PQ_F_PI=str(a.pi.resolve()))
            run("geth-build", ["go", "build", "-p", "2", "-tags", "pq_final,pq_aggregate", "-trimpath", "-buildvcs=false", "-o", out / "bin/geth", "./cmd/geth"], out / "geth", go_env)
            run("geth-test", ["go", "test", "-p", "2", "-tags", "pq_final,pq_aggregate", "-count=1", "-json",
                              "./core", "./core/vm", "./core/types", "./core/txpool/...", "./miner", "./eth", "./eth/catalyst", "./eth/fetcher", "./eth/protocols/eth", "./internal/ethapi", "./graphql",
                              "-run", "PQ|Batch|SponsorStrike|Displacement|ECDSA|Migration|SigningFence|ResetOrphanMarginPrecedesReplacement|ResetCandidateMarginEqualityAndOverflow|HeldRetryNeverChargesPureFailureOrRecordsStrike"], out / "geth", go_env)
            run("geth-research-test", ["go", "test", "-p", "2", "-tags", "pq_final,pq_aggregate,pq_research_order", "-count=1", "-json", "./miner", "-run", "PQ|Research"], out / "geth", go_env)
            run("geth-no-verifier-test", ["go", "test", "-p", "2", "-count=1", "-json", "./core", "-run", "^TestPQ(Final|Aggregate)Unavailable$"], out / "geth", go_env)
            counts = {}
            for name in ["geth-test", "geth-research-test", "geth-no-verifier-test"]:
                rows = [json.loads(line) for line in (out / "logs" / (name + ".out")).read_text().splitlines()]
                counts[name] = {action: sum(r.get("Action") == action and bool(r.get("Test")) for r in rows)
                                for action in ["pass", "fail", "skip"]}
            record["gethTestCasesIncludingSubtests"] = counts
        if "ream" in names:
            flags = "-C target-cpu=x86-64-v3 -C target-feature=+pclmulqdq --remap-path-prefix=" + str(out) + "=/build"
            ream_env = {"CARGO_TARGET_DIR": str(out / "ream-target"), "RUSTFLAGS": flags}
            run("ream-build", ["cargo", "build", "--release", "--locked", "--offline", "--features", "reth", "--bin", "ream"], out / "ream", ream_env)
            shutil.copy2(out / "ream-target/release/ream", out / "bin/ream")
            run("ream-test", ["cargo", "test", "--release", "--locked", "--offline", "--features", "reth",
                              "-p", "ream-chain-lean", "-p", "ream-validator-lean", "-p", "ream-fork-choice-lean", "-p", "ream-consensus-lean",
                              "-p", "ream-reth-engine",
                              "--", "--test-threads=1"], out / "ream", ream_env)
            run("ream-cl-unit-test", ["cargo", "test", "--lib", "--release", "--locked", "--offline",
                              "-p", "ream-chain-lean", "-p", "ream-validator-lean", "-p", "ream-fork-choice-lean", "-p", "ream-consensus-lean",
                              "--", "--test-threads=1"], out / "ream", ream_env)
            run("ream-history-provisioning-test", ["cargo", "test", "--release", "--locked", "--offline",
                              "-p", "ream-chain-lean", "--example", "profile_tool_three",
                              "--", "--test-threads=1"], out / "ream", ream_env)
        verify_source(ROOT, source_identity)
        record["status"] = "PASS"
        record["binaries"] = {str(p.relative_to(out)): sources.digest(p)
                              for parent in [out / "bin", out / "lib"] for p in parent.iterdir() if p.is_file()}
    except BaseException as error:
        record.update(status="FAIL", failure=str(error))
        raise
    finally:
        save()


if __name__ == "__main__":
    main()
