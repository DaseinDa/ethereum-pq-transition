#!/usr/bin/env python3
"""Replay an existing public measurement cohort through the no-inner-report format."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cohort", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=False)
    for p in [a.cohort / "PLAN.json", a.cohort / "geth-gas.json", *a.cohort.glob("geth-verifier-*.json")]:
        shutil.copyfile(p, a.out / p.name)
    plan = json.loads((a.cohort / "PLAN.json").read_text())
    for row in plan["samples"]:
        if row["mode"]:
            continue
        src, dest = a.cohort / row["name"], a.out / row["name"]
        (dest / "logs").mkdir(parents=True)
        record = json.loads((src / "PROOF.json").read_text())
        record["layers"] = {}
        for layer, filename in [("leaf", "metrics.json"), ("b", "report.json"), ("f", "report.json")]:
            report = json.loads((src / layer / filename).read_text())
            verdict = json.loads((src / layer / "verification.json").read_text())["verdict"]
            record["layers"][layer] = {"prove_ms": report.get("prove_ms", report.get("timings_ms", {}).get("prove")),
                "proof_bytes": report["proof_bytes"], "fresh_verdict": verdict}
            shutil.copyfile(src / "logs" / (layer + "-prove.time"), dest / "logs" / (layer + "-prove.time"))
        (dest / "PROOF.json").write_text(json.dumps(record))
    subprocess.run([sys.executable, "-B", Path(__file__).resolve().parents[1] / "bench/summarize.py", "--work", a.out], check=True)
    old = json.loads((a.cohort / "SUMMARY.json").read_text())
    new = json.loads((a.out / "SUMMARY.json").read_text())
    assert new == old
    (a.out / "REPLAY.json").write_text(json.dumps({"status": "PASS", "summaryExactlyEqual": True,
        "scope": "format compatibility only; existing measurements reused, no additional performance samples"}, indent=2) + "\n")
    print("PASS: summary unchanged without inner reports")


if __name__ == "__main__":
    main()
