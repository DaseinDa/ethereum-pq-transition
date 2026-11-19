#!/usr/bin/env python3
"""Aggregate four exported F proofs into the fixed research C carrier."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "tools"))
from aggregate_support import (BINARIES, C_KEY, MAX_CARRIER, available_gib, clean_environment,
                               read_owner, run_logged, statement_from_pis, verify_package)
from build_provenance import capture_source, sha, verify_build, verify_source
from heavy_job import heavy_job


def verify_runtime(build):
    record = json.loads((build / "BUILD.json").read_text(encoding="utf-8"))
    if (ROOT / "manifest.json").exists():
        from install import require_installed
        installed = require_installed(ROOT)
        identity = json.loads((ROOT / "share/build/source-identity.json").read_text(encoding="utf-8"))
        if installed.get("sourceIdentity") != identity:
            raise ValueError("installed aggregate source identity mismatch")
        if build != (ROOT / "aggregate-runtime").resolve():
            raise ValueError("installed launcher requires its checked aggregate-runtime build")
    else:
        identity = capture_source(ROOT)
        verify_source(ROOT, identity)
        verify_package(ROOT)
        if record.get("aggregateSourceManifestSHA256") != sha(ROOT / "prover/aggregate/SOURCE.json"):
            raise ValueError("aggregate source manifest mismatch")
    verify_build(ROOT, record, BINARIES, build, identity=identity)
    if record.get("aggregateKey") != C_KEY:
        raise ValueError("aggregate build key mismatch")
    return record


def aggregate(a):
    if sys.platform != "linux":
        raise RuntimeError("aggregate proving requires Linux")
    build = a.build.resolve()
    manifest = verify_runtime(build)
    owners = [read_owner(p.resolve()) for p in a.owner]
    statement = statement_from_pis([owner[0] for owner in owners])
    public_test = all(owner[2] for owner in owners)
    if a.keep_inner and not (a.public_test_data and public_test):
        raise ValueError("inner export requires --public-test-data and four publicTestOnly owner records")
    if a.public_test_data and not public_test:
        raise ValueError("all four owner PROOF.json records must mark publicTestOnly")
    if available_gib() < 48:
        raise RuntimeError("aggregate proving requires at least 48 GiB available RAM")
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "logs").mkdir()
    inputs = out / "inputs"
    inputs.mkdir()
    for index, (pi, proof, _) in enumerate(owners):
        target = inputs / str(index)
        (target / "statement").mkdir(parents=True)
        (target / "f").mkdir()
        (target / "statement/pi198.hex").write_text(pi.hex() + "\n", encoding="ascii")
        (target / "f/proof.postcard").write_bytes(proof)
    (out / "statement.bin").write_bytes(statement)
    record = {"status": "RUNNING", "commands": [], "aggregateKey": C_KEY,
              "sourceIdentity": manifest["sourceIdentity"],
              "aggregateBuildSHA256": sha(build / "BUILD.json"), "publicTestOnly": public_test,
              "keepInner": a.keep_inner, "ownerOrder": [pi[64:84].hex() for pi, _, _ in owners],
              "inputs": [{"piSHA256": sha(inputs / str(i) / "statement/pi198.hex"),
                          "fSHA256": sha(inputs / str(i) / "f/proof.postcard")} for i in range(4)],
              "custody": "only exported F proofs and PI198 enter; AG stays in memory by default"}
    def save():
        (out / "AGGREGATE.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    save()
    env = clean_environment(RAYON_NUM_THREADS="8")
    try:
        argv = [build / "bin/pq-migrate-tree", "prove", out / "c", inputs]
        if a.keep_inner:
            argv += ["--keep-inner", "--public-test-data"]
        record["commands"].append({"name": "aggregate-prove", **run_logged(
            argv, cwd=out, env=env, log=out / "logs/aggregate-prove", memory_gib=40)})
        save()
        if (out / "c/statement.bin").read_bytes() != statement:
            raise ValueError("generated aggregate statement differs from the ordered input PIs")
        if not 256 < (out / "c/carrier.bin").stat().st_size <= MAX_CARRIER:
            raise ValueError("generated carrier length is invalid")
        if not a.keep_inner and (out / "c/ag.postcard").exists():
            raise ValueError("unexpected inner AG proof export")
        record["commands"].append({"name": "aggregate-verify", **run_logged(
            [build / "bin/aggregate-verify", out / "c/carrier.bin", out / "statement.bin", "1"],
            cwd=out, env=env, log=out / "logs/aggregate-verify", memory_gib=1)})
        verify_runtime(build)
        record.update(status="PASS", carrierSHA256=sha(out / "c/carrier.bin"),
                      statementSHA256=sha(out / "statement.bin"), carrierBytes=(out / "c/carrier.bin").stat().st_size)
    except BaseException as exc:
        record["status"], record["error"] = "FAIL", str(exc)
        raise
    finally:
        save()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", type=Path, required=True)
    ap.add_argument("--owner", type=Path, action="append", required=True,
                    help="exported F run directory, repeated four times in transaction order")
    ap.add_argument("--out", type=Path, required=True, help="new output directory")
    ap.add_argument("--keep-inner", action="store_true")
    ap.add_argument("--public-test-data", action="store_true")
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    a = ap.parse_args()
    if len(a.owner) != 4:
        ap.error("exactly four --owner arguments are required")
    if a.keep_inner and not a.public_test_data:
        ap.error("--keep-inner requires --public-test-data")
    with heavy_job(a.lock, owner="pq-migrate-four-owner-prove"):
        aggregate(a)


if __name__ == "__main__":
    main()
