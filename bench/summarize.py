#!/usr/bin/env python3
"""Statistics from observed proof/client outputs; capacity is explicitly a model."""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import re
import statistics


def stats(xs):
    if len(xs) < 10:
        raise ValueError("at least ten samples required")
    return {"n": len(xs), "mean": statistics.mean(xs), "sd": statistics.stdev(xs), "min": min(xs), "max": max(xs)}


def main(root):
    load = lambda path: json.loads(path.read_text())
    layers, rows = {}, []
    for row in load(root / "PLAN.json")["samples"]:
        if row["mode"]:
            continue
        d = root / row["name"]
        if load(d / "PROOF.json")["status"] != "PASS":
            raise ValueError("failed proof sample")
        for layer, command, filename in [("leaf", "leaf", "metrics.json"), ("b", "b", "report.json"), ("f", "f", "report.json")]:
            proof_record = load(d / "PROOF.json")
            report = proof_record["layers"][layer] if "layers" in proof_record else load(d / layer / filename)
            tm = (d / "logs" / (command + "-prove.time")).read_text()
            elapsed = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.*)", tm).group(1)
            seconds = 0
            for part in elapsed.split(":"):
                seconds = 60 * seconds + float(part)
            if not re.search(r"Exit status: 0\s*$", tm):
                raise ValueError("unsuccessful timed command")
            verdict = report["fresh_verdict"] if "layers" in proof_record else load(d / layer / "verification.json")["verdict"]
            if verdict != "ACCEPTED":
                raise ValueError("fresh verification failed")
            rows.append(dict(sample=row["name"], layer=layer, commandSeconds=seconds,
                proveSeconds=report.get("prove_ms", report.get("timings_ms", {}).get("prove")) / 1000,
                peakRSSKiB=int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", tm).group(1)),
                proofBytes=report["proof_bytes"]))
    for layer in ["leaf", "b", "f"]:
        sample = [r for r in rows if r["layer"] == layer]
        layers[layer] = {key: stats([r[key] for r in sample]) for key in ["proveSeconds", "commandSeconds", "peakRSSKiB", "proofBytes"]}
    proofs = [load(root / f"mode0-{i:02}/PROOF.json") for i in range(1, 11)]
    if len({p["proofSHA256"] for p in proofs}) != 10 or len({p["piSHA256"] for p in proofs}) != 1:
        raise ValueError("cohort must have distinct proofs for the same PI")
    gas = load(root / "geth-gas.json")
    tx = {}
    for name in sorted({r["name"] for r in gas["rows"]}):
        rs = [r for r in gas["rows"] if r["name"] == name]
        if not all(r["status"] == 1 for r in rs):
            raise ValueError("failed execution")
        tx[name] = {key: stats([r[key] for r in rs]) for key in ["gas", "bytes", "executionNs"]}
    verify = [load(root / f"geth-verifier-{i:02}.json") for i in range(1, 11)]
    if not all(r["mutationControls"] == "PI and proof rejected" for r in verify):
        raise ValueError("missing mutation controls")
    if len({r["verifyGas"] for r in verify}) != 1 or gas.get("verifyGas", verify[0]["verifyGas"]) != verify[0]["verifyGas"]:
        raise ValueError("inconsistent verifier pricing across measurements")
    capacity = []
    G, L, slot = gas["blockGasLimit"], 16000000, 12
    for name in ["recovery", "sponsored-mode1", "sponsored-mode2", "sponsored-mode3"]:
        g = tx[name]["gas"]["max"]
        n = 1 + (G - L) // g if G >= L else 0
        capacity.append({"scenario": name, "basis": "maximum observed single-transaction gas", "measuredMaxGas": g, "declaredGasLimit": L,
            "currentPerBlock": n, "currentPerDay": n * 86400 // slot, "idealTightLimitPerBlock": G // g})
    lifecycle_gas = sum(tx[name]["gas"]["max"] for name in ["recovery", "activation", "first-spend"])
    lifecycle_count = 1 + (G - L) // lifecycle_gas if G >= L else 0
    capacity.append({"scenario": "recovery+activation+first-spend", "basis": "sum of observed maxima; steady pipeline model, not measured network throughput",
        "measuredMaxGas": lifecycle_gas, "declaredGasLimit": L,
        "currentPerBlock": lifecycle_count, "currentPerDay": lifecycle_count * 86400 // slot,
        "idealTightLimitPerBlock": G // lifecycle_gas})
    population = [{"accounts": n, "allocatedBlockFraction": share,
                   "days": math.ceil(n / lifecycle_count) * slot / share / 86400}
                  for n in [1000, 10000, 100000, 1000000, 10000000, 100000000] for share in [1, 0.1]]
    result = {"status": "PASS", "scope": "Measurement harness, not protocol acceptance",
        "review": "loop-internal self-review; not independently reviewed", "layers": layers, "transactions": tx,
        "gethWarmMeanMs": stats([statistics.mean(r["verifyNs"]) / 1e6 for r in verify]),
        "gethColdKeyMs": stats([r["keyInitNs"] / 1e6 for r in verify]), "capacity": capacity, "population": population,
        "populationBasis": "Recovery, ordinary activation and first spend; steady state with different accounts at successive stages",
        "parameters": {"blockGasLimit": G, "txGasCap": gas["txGasCap"], "slotSeconds": slot, "verifyGas": verify[0]["verifyGas"]},
        "limitations": ["One public credential and machine; sponsor executions reuse a fixed carrier per mode.",
            "Capacity is arithmetic, excluding missed blocks, other traffic, consensus/network load and prover supply.",
            "Measured maxima are not cryptographic or worst-case execution bounds. No security gate is promoted."]}
    (root / "SUMMARY.json").write_text(json.dumps(result, indent=2) + "\n")
    for name, data in [("proof-samples", rows), ("transaction-samples", gas["rows"]), ("capacity", capacity), ("population", population)]:
        with (root / (name + ".csv")).open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(data[0])); w.writeheader(); w.writerows(data)
    files = [p for p in root.rglob("*") if p.is_file() and "geth" not in p.relative_to(root).parts and p.name != "SHA256.json"]
    (root / "SHA256.json").write_text(json.dumps({str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}, sort_keys=True, indent=2) + "\n")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    main(ap.parse_args().work)
