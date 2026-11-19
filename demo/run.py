#!/usr/bin/env python3
"""Run the installed public-test migration demo with fresh proofs and signing keys."""
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

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from install import require_installed


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare_inputs(proofs, dest, names=None):
    """Adapt authenticated proof outputs without changing their statement bytes."""
    # Only this public-test demo reconstructs its test signing seed. The prover
    # deliberately exports no xi, seed64 or mnemonic.
    sys.path.insert(0, str(ROOT / "prover"))
    sys.path.insert(0, str(ROOT / "wallet"))
    from statement import bip39_seed, parse_path
    import wallet_epochs
    public_input = json.loads((ROOT / "share/public-input.json").read_text())
    credential = public_input["credential"]
    if credential.get("public") is not True:
        raise ValueError("demo requires the installed public test credential")
    seed = bip39_seed(credential["mnemonic"], credential.get("passphrase", ""))
    xi = wallet_epochs.derive_epoch_seed(seed, "ML-DSA-44", tuple(parse_path(public_input["path"])), public_input["pq_key"]["epoch"])
    from statement import Crypto, pq_key
    build = json.loads((ROOT / "prover-runtime/BUILD.json").read_text())
    crypto = Crypto(ROOT / "prover-runtime/bin/pq-test-crypto", build["binaries"]["pq-test-crypto"])
    try:
        expected = pq_key(xi, crypto)
    finally:
        crypto.close()
    dest.mkdir(exist_ok=False)
    for name in (names or ["recovery", "mode1", "mode2", "mode3"]):
        source = proofs / name
        record = json.loads((source / "PROOF.json").read_text())
        statement = json.loads((source / "statement/statement.json").read_text())
        key = json.loads((source / "statement/pq-key.json").read_text())
        proof = source / "f/proof.postcard"
        pi = bytes.fromhex(statement["pi198_hex"])
        if (record["status"] != "PASS" or digest(proof) != record["proofSHA256"]
                or hashlib.sha256(pi).hexdigest() != record["piSHA256"]
                or len(pi) != 198 or int.from_bytes(pi[:32], "big") != 13378
                or not int(time.time()) + 3600 < int.from_bytes(pi[129:137], "big") <= int(time.time()) + 604800):
            raise ValueError("proof identity or current expiry check failed: " + name)
        public_test = statement.get("publicTestOnly") is True or (
            statement.get("schema") == "pq-proof-pipeline/statement/v1"
            and statement.get("input", {}).get("credential", {}).get("public") is True)
        if (not public_test or key.get("publicTestOnly", public_test) is not True
                or key["public_key_hex"] != expected["pk"].hex() or pi[93:125] != expected["commit"]):
            raise ValueError("demo proof does not bind the installed public test key")
        target = dest / name
        target.mkdir()
        shutil.copyfile(proof, target / "proof.postcard")
        (target / "pi198.hex").write_text(pi.hex() + "\n")
        (target / "pi.bin").write_bytes(pi)
        fields = {k: (v["value"] if "value" in v else "0x" + v["hex"]) for k, v in statement["fields"].items()}
        (target / "config.json").write_text(json.dumps({"pi198_hex": pi.hex(), "fields": fields,
            "xi_hex": xi.hex(), "public_key_hex": key["public_key_hex"]}, indent=2) + "\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True, help="new run directory outside the installation")
    ap.add_argument("--proofs", type=Path, help="resume from four verified, unexpired public proof outputs")
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    ap.add_argument("--scenario", choices=["migration", "n1-requests"], default="migration")
    a = ap.parse_args()
    manifest = require_installed(ROOT)
    work = a.work.resolve()
    if work.is_relative_to(ROOT) or ROOT.is_relative_to(work):
        raise ValueError("run and installation directories must be disjoint")
    work.mkdir(parents=True, exist_ok=False)
    (work / "logs").mkdir()
    record = {"status": "RUNNING", "publicTestOnly": True, "commands": [],
              "review": "loop-internal self-review; not independently reviewed",
              "manifestSHA256": digest(ROOT / "manifest.json")}
    token = str(uuid.uuid4())
    owned = False

    def run(name, argv):
        print(name + ": starting", flush=True)
        started = time.monotonic()
        with (work / "logs" / (name + ".out")).open("xb") as stdout, (work / "logs" / (name + ".err")).open("xb") as stderr:
            env = dict(os.environ)
            if name.startswith("keys-"):
                env["RAYON_NUM_THREADS"] = "2"
            result = subprocess.run(list(map(str, argv)), stdout=stdout, stderr=stderr, env=env)
        record["commands"].append({"name": name, "exit": result.returncode, "seconds": time.monotonic() - started})
        (work / "RUN.json").write_text(json.dumps(record, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(name + " failed; see logs")
        print(name + ": PASS", flush=True)

    try:
        proofs = a.proofs.resolve() if a.proofs else work / "proofs"
        if not a.proofs:
            proofs.mkdir()
            sponsor = json.loads((ROOT / "share/l1/PUBLIC-sponsor.json").read_text())["address"]
            for mode in range(1 if a.scenario == "n1-requests" else 4):
                inp = json.loads((ROOT / "share/public-input.json").read_text())
                name = "recovery" if mode == 0 else "mode" + str(mode)
                if mode:
                    inp["pi"].update(migration_nonce=mode, fee_mode=mode,
                        max_account_fee_wei=str(0 if mode == 2 else 10**15),
                        fee_sponsor=sponsor if mode == 1 else "00" * 20,
                        fee_auth_until="expiry" if mode in (1, 3) else 0)
                source = proofs / (name + "-input.json")
                source.write_text(json.dumps(inp, indent=2) + "\n")
                run("prove-" + name, [sys.executable, "-B", ROOT / "prover/prove.py", "--build", ROOT / "prover-runtime",
                    "--input", source, "--out", proofs / name, "--lock", a.lock])
        prepare_inputs(proofs, work / "inputs", ["recovery"] if a.scenario == "n1-requests" else None)
        while not owned:
            try:
                with a.lock.open("x") as file:
                    json.dump({"owner": "pq-migrate-lab-demo", "pid": os.getpid(), "token": token}, file)
                owned = True
            except FileExistsError:
                print("Waiting for the shared heavy-job lock", flush=True)
                time.sleep(10)
        # New seeds and new histories for every new genesis; restart reuses the
        # same append-only histories inside run_network, never this provisioning.
        for name in ["A", "B", "C"]:
            seed = work / (name + "-PUBLIC-seeds.bin")
            seed.write_bytes(os.urandom(64))
            run("keys-" + name, [ROOT / "bin/fresh-public-keys", work / ("keys-" + name), seed])
        network_script = "n1_requests.py" if a.scenario == "n1-requests" else "run_network.py"
        run("lean-network", [sys.executable, "-B", ROOT / "tools/lean" / network_script, "--work", work / "network",
            "--run-id", uuid.uuid4().hex, "--keys", work / "keys-A", "--keys-b", work / "keys-B",
            "--keys-c", work / "keys-C", "--inputs", work / "inputs"])
        for name in ["A", "B"]:
            run("history-" + name, [ROOT / "bin/audit-history", work / "network" / (name + "-final-signing-history.bin")])
            audit = json.loads((work / "logs" / ("history-" + name + ".out")).read_text())
            if audit["status"] != "PASS" or audit["verifiedSignatures"] == 0:
                raise ValueError("no verified signatures in " + name + " history")
        record["status"] = "PASS"
    except BaseException as error:
        record.update(status="FAIL", failure=str(error))
        raise
    finally:
        (work / "RUN.json").write_text(json.dumps(record, indent=2) + "\n")
        if owned and a.lock.exists() and json.loads(a.lock.read_text()).get("token") == token:
            a.lock.unlink()
        if a.scenario == "migration":
            subprocess.run([sys.executable, "-B", ROOT / "tools/report.py", "--run", work], check=False)


if __name__ == "__main__":
    main()
