#!/usr/bin/env python3
"""Repeat the fixed public-statement benchmark using the packaged source and tools."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("action", choices=["prepare", "prove", "geth"])
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--prover-build", type=Path, required=True)
    ap.add_argument("--client-build", type=Path)
    ap.add_argument("--dependencies", type=Path)
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    ap.add_argument("--keep-inner", action="store_true", help="retain inner proofs for this public-test benchmark")
    a = ap.parse_args()
    work = a.work.resolve()
    prover = a.prover_build.resolve()
    if a.action == "prepare":
        work.mkdir(parents=True, exist_ok=False)
        (work / "logs").mkdir()
        sponsor = json.loads((ROOT / "demo/public-sponsor.json").read_text())
        (work / "PUBLIC-sponsor.json").write_text(json.dumps(sponsor, indent=2) + "\n")
        expiry = int(time.time()) + 3 * 86400
        samples = []
        for mode, count in [(0, 10), (1, 1), (2, 1), (3, 1)]:
            for rep in range(1, count + 1):
                name = f"mode{mode}-{rep:02}"
                inp = json.loads((ROOT / "demo/public-input.json").read_text())
                inp["pi"].update(migration_nonce=0, fee_mode=mode,
                    max_account_fee_wei=str(88 * 10**15 if mode == 0 else 0 if mode == 2 else 10**15),
                    fee_sponsor=sponsor["address"] if mode == 1 else "00" * 20,
                    fee_auth_until=expiry if mode in (1, 3) else 0)
                (work / (name + ".json")).write_text(json.dumps(inp, indent=2) + "\n")
                samples.append({"name": name, "mode": mode, "rep": rep})
        plan = {"expiry": expiry, "samples": samples, "primary": "10 fresh mode-0 proofs of the identical PI",
                "auxiliary": "One proof per sponsor mode; ten fresh-state executions of each carrier",
                "review": "loop-internal self-review; not independently reviewed"}
        (work / "PLAN.json").write_text(json.dumps(plan, indent=2) + "\n")
        (work / "hardware.json").write_text(subprocess.check_output(["lscpu", "--json"], text=True))
        (work / "memory.txt").write_text(Path("/proc/meminfo").read_text())
        return
    plan = json.loads((work / "PLAN.json").read_text())
    if a.action == "prove":
        for row in plan["samples"]:
            subprocess.run([sys.executable, "-B", ROOT / "prover/prove.py", "--build", prover,
                "--input", work / (row["name"] + ".json"), "--out", work / row["name"],
                "--expiry", str(plan["expiry"]), "--lock", a.lock, *(["--keep-inner"] if a.keep_inner else [])], check=True)
        return
    if not a.client_build or not a.dependencies:
        ap.error("geth requires --client-build and --dependencies")
    client = a.client_build.resolve()
    record_path = next((client / name for name in ["VALIDATION.json", "RECHECK.json", "BUILD.json"] if (client / name).exists()))
    record = json.loads(record_path.read_text())
    if record["status"] != "PASS":
        raise ValueError("client build is not verified")
    for rel, digest in record["binaries"].items():
        if hashlib.sha256((client / rel).read_bytes()).hexdigest() != digest:
            raise ValueError("client binary changed: " + rel)
    for row in plan["samples"]:
        if json.loads((work / row["name"] / "PROOF.json").read_text())["status"] != "PASS":
            raise ValueError("all proof samples must pass")
    token = str(uuid.uuid4())
    owned = False
    try:
        while not owned:
            try:
                with a.lock.open("x") as f:
                    json.dump({"owner": "pq-migrate-lab-bench", "pid": os.getpid(), "token": token}, f)
                owned = True
            except FileExistsError:
                time.sleep(10)
        shutil.copytree(client / "geth", work / "geth")
        shutil.copyfile(ROOT / "bench/pq_bench_test.go", work / "geth/core/pq_bench_test.go")
        genesis = json.loads((ROOT / "demo/templates/migration-genesis.json").read_text())
        now = int(time.time())
        cfg = genesis["config"]["pqMigrate"]
        cfg.update(t0=now - 24, receivingTime=now - 24, t=now - 12)
        cfg["fullResearch"]["activation"] = now - 24
        (work / "genesis.json").write_text(json.dumps(genesis, indent=2) + "\n")
        env = dict(os.environ, GOTOOLCHAIN="local", GOMAXPROCS="2", CGO_ENABLED="1", GOFLAGS="-mod=readonly",
            GOMODCACHE=str(client / "go-mod"), GOCACHE=str(client / "go-build"), GOSUMDB="off",
            GOPROXY=(a.dependencies.resolve() / "go-proxy").as_uri(), LD_LIBRARY_PATH=str(client / "lib"),
            CGO_LDFLAGS="-L" + str(client / "lib"), PQ_BENCH_ROOT=str(work), PQ_BENCH_OUT=str(work))
        commands = [("compile", ["go", "test", "-c", "-p", "2", "-tags", "pq_final", "-trimpath", "-buildvcs=false", "-o", str(work / "geth-bench"), "./core"], {})]
        commands.append(("carriers", [sys.executable, "-B", str(ROOT / "bench/carriers.py"), "--root", str(work), "--build", str(prover)], {}))
        commands += [(f"verify-{i:02}", [str(work / "geth-bench"), "-test.run=^TestPQPaperVerifier$", "-test.v"], {"PQ_BENCH_REP": str(i)}) for i in range(1, 11)]
        commands.append(("gas", [str(work / "geth-bench"), "-test.run=^TestPQPaperGas$", "-test.v"], {}))
        results = []
        for name, argv, extra in commands:
            started = time.monotonic()
            with (work / "logs" / (name + ".out")).open("xb") as out, (work / "logs" / (name + ".err")).open("xb") as err:
                p = subprocess.run(argv, cwd=work / "geth", env=dict(env, **extra), stdout=out, stderr=err)
            results.append({"name": name, "exit": p.returncode, "seconds": time.monotonic() - started})
            (work / "CLIENT.json").write_text(json.dumps(results, indent=2) + "\n")
            if p.returncode:
                raise RuntimeError(name + " failed; see logs")
            print(name + ": PASS", flush=True)
    finally:
        if owned and a.lock.exists() and json.loads(a.lock.read_text()).get("token") == token:
            a.lock.unlink()


if __name__ == "__main__":
    main()
