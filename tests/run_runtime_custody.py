#!/usr/bin/env python3
"""Check the installed adapters/ABI without starting a new consensus run."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runtime", type=Path, required=True)
    ap.add_argument("--proof", type=Path, required=True, help="new public-test proof output")
    ap.add_argument("--legacy-proofs", type=Path, required=True, help="three already verified, unexpired public sponsor outputs")
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=False)
    mixed = a.out / "mixed"; mixed.mkdir()
    (mixed / "recovery").symlink_to(a.proof.resolve(), target_is_directory=True)
    for name in ("mode1", "mode2", "mode3"):
        (mixed / name).symlink_to((a.legacy_proofs / name).resolve(), target_is_directory=True)
    spec = importlib.util.spec_from_file_location("run_demo", a.runtime / "tools/run_demo.py")
    demo = importlib.util.module_from_spec(spec); spec.loader.exec_module(demo)
    inputs = a.out / "inputs"
    demo.prepare_inputs(mixed, inputs)
    commands = [
        ("abi", [sys.executable, "-B", a.runtime / "tools/install.py", "selfcheck", "--prefix", a.runtime, "--inputs", inputs]),
        ("wallet", [sys.executable, "-B", a.runtime / "wallet/cli.py", "recover", "--proof-run", a.proof, "--out", a.out / "wallet.bin"]),
        ("go-carriers", [a.runtime / "bin/pqlean-txs", "--config", inputs / "recovery/config.json", "--root", inputs / "recovery/proof.postcard", "--out", a.out / "go"]),
    ]
    rows = []
    for name, cmd in commands:
        result = subprocess.run(cmd, capture_output=True)
        (a.out / (name + ".out")).write_bytes(result.stdout)
        (a.out / (name + ".err")).write_bytes(result.stderr)
        rows.append({"name": name, "exit": result.returncode})
        if result.returncode:
            raise RuntimeError(name + " failed")
    raw = (a.out / "wallet.bin").read_bytes()
    assert raw == (a.out / "go/migrate.bin").read_bytes()
    for name in ("recovery", "mode1", "mode2", "mode3"):
        assert (inputs / name / "proof.postcard").read_bytes() == (mixed / name / "f/proof.postcard").read_bytes()
    abi = json.loads((a.out / "abi.out").read_text())
    assert abi["report"]["realProofChecked"] and abi["status"] == "OK"
    report = {"status": "PASS", "commands": rows, "abi": abi["report"]["abi"], "carrierBytes": len(raw),
        "carrierSHA256": hashlib.sha256(raw).hexdigest(), "walletEqualsGoCarrier": True,
        "publicMetadataAdapter": "new recovery plus unchanged legacy public sponsor outputs",
        "scope": "packaged adapters and native verifier; no fresh consensus/network run",
        "review": "loop-internal self-review; not independently reviewed"}
    (a.out / "SUMMARY.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
