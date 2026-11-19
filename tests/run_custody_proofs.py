#!/usr/bin/env python3
"""Two serial, full-parameter custody regressions; public synthetic credentials only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "prover"))
import statement


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    inp = json.loads((ROOT / "demo/public-input.json").read_text())
    markers = [inp["credential"]["mnemonic"].encode(),
               statement.bip39_seed(inp["credential"]["mnemonic"], "").hex().encode(), b"seed64_hex", b"xi_hex"]
    results = []
    for name, keep in [("owner-default", False), ("public-keep-inner", True)]:
        inp["credential"]["public"] = keep
        out = args.out / name
        cmd = [sys.executable, "-B", ROOT / "prover/prove.py", "--build", args.build, "--input", "-", "--out", out]
        if keep:
            cmd.append("--keep-inner")
        seen = set()
        start = time.monotonic()
        with (args.out / (name + ".log")).open("wb") as log:
            process = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=log, stderr=subprocess.STDOUT)
            process.stdin.write(json.dumps(inp).encode()); process.stdin.close()
            while process.poll() is None:
                seen.update(p.relative_to(out).as_posix() for p in out.rglob("*") if p.is_file())
                time.sleep(0.2)
            code = process.wait()
        if code:
            raise RuntimeError(name + " did not complete; inspect the non-secret log")
        record = json.loads((out / "PROOF.json").read_text())
        assert record["status"] == "PASS" and record["keepInner"] == keep
        assert {c["name"]: c["exit"] for c in record["commands"]}["reject-changed-pi"] == 1
        assert {c["name"]: c["exit"] for c in record["commands"]}["reject-changed-proof"] == 1
        files = {p.relative_to(out).as_posix(): p for p in out.rglob("*") if p.is_file()}
        if not keep:
            assert not (out / "leaf").exists() and not (out / "b").exists()
            assert not any(p.split("/")[0] in ("inputs", "leaf", "b") for p in seen | set(files))
            assert set(files) == {"PROOF.json", "statement/pi198.hex", "statement/statement.json", "statement/pq-key.json", "f/proof.postcard"} | {
                "logs/" + c["name"] + ".time" for c in record["commands"]}
        else:
            assert (out / "leaf/l0p2.postcard").is_file() and (out / "b/proof.postcard").is_file()
        for p in files.values():
            data = p.read_bytes()
            assert not any(marker in data for marker in markers), "credential persisted in " + p.name
        results.append({"case": name, "status": "PASS", "seconds": time.monotonic() - start,
            "proofBytes": record["proofBytes"], "proofSHA256": record["proofSHA256"],
            "filesObserved": sorted(seen | set(files)), "sha256": {k: hashlib.sha256(p.read_bytes()).hexdigest() for k,p in files.items()}})
        print(name + ": PASS", flush=True)
    (args.out / "SUMMARY.json").write_text(json.dumps({"status": "PASS", "review": "loop-internal self-review; not independently reviewed", "runs": results}, indent=2) + "\n")


if __name__ == "__main__":
    main()
