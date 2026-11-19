#!/usr/bin/env python3
"""Public-test transaction construction and local account queries; not a production wallet."""
import argparse
import ctypes
import hashlib
import ipaddress
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace
import urllib.parse
import urllib.request

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "wallet"))
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "prover"))
import wallet as w
import statement
from install import require_installed


def query(url, method, params):
    u = urllib.parse.urlsplit(url)
    if u.scheme != "http" or not u.hostname or u.username or u.password:
        raise ValueError("use a local HTTP RPC without credentials")
    if u.hostname != "localhost" and not ipaddress.ip_address(u.hostname).is_loopback:
        raise ValueError("only loopback RPC is allowed in this public-key demo")
    req = urllib.request.Request(url, json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode(), {"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=10) as response:
        result = json.load(response)
    if "error" in result:
        raise ValueError(result["error"])
    return result["result"]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="command", required=True)
    q = sub.add_parser("query")
    q.add_argument("--rpc", required=True)
    q.add_argument("--address", required=True)
    watch = sub.add_parser("watch-enrollment", help="alert on an enrollment absent from the wallet's local transaction record")
    watch.add_argument("--rpc", required=True)
    watch.add_argument("--address", required=True)
    watch.add_argument("--own-enrollment", action="append", default=[], help="transaction hash recorded by this wallet; repeatable")
    watch.add_argument("--from-block", type=int, default=0)
    watch.add_argument("--state", type=Path, required=True, help="observer cursor outside the installation")
    watch.add_argument("--once", action="store_true")
    watch.add_argument("--interval", type=float, default=2)
    d = sub.add_parser("derive")
    d.add_argument("--epoch", type=int, default=0)
    for command in ["recover", "pq"]:
        p = sub.add_parser(command)
        p.add_argument("--out", type=Path, required=True)
        if command == "recover":
            p.add_argument("--proof-run", type=Path, required=True)
            p.add_argument("--consent-account-reimbursement", action="store_true")
        else:
            p.add_argument("--nonce", type=int, required=True)
            p.add_argument("--epoch", type=int, default=0)
            p.add_argument("--activate", action="store_true")
            p.add_argument("--to", default="0x" + "00" * 18 + "beef")
            p.add_argument("--value", type=int, default=0)
    a = ap.parse_args()
    require_installed(ROOT)
    if a.command == "watch-enrollment":
        if a.state.resolve().is_relative_to(ROOT.resolve()):
            raise ValueError("keep the observer cursor outside the immutable installation")
        from enrollment_watch import run
        run(query, a.rpc, a.address, a.own_enrollment, a.from_block, a.state, a.once, a.interval)
        return
    if a.command == "query":
        if int(query(a.rpc, "eth_chainId", []), 16) != 13378:
            raise ValueError("this wallet is restricted to local chain 13378")
        print(json.dumps({"account": query(a.rpc, "eth_getPQAccount", [a.address, "latest"]),
            "nonce": query(a.rpc, "eth_getTransactionCount", [a.address, "latest"]),
            "balance": query(a.rpc, "eth_getBalance", [a.address, "latest"])}))
        return
    build = json.loads((ROOT / "prover-runtime/BUILD.json").read_text())
    helper = ROOT / "prover-runtime/bin/pq-test-crypto"
    if hashlib.sha256(helper.read_bytes()).hexdigest() != build["binaries"]["pq-test-crypto"]:
        raise ValueError("crypto helper changed")
    cr = w.wire.Worker(helper)
    try:
        public_input = json.loads((ROOT / "share/public-input.json").read_text())
        credential = public_input["credential"]
        if credential["public"] is not True:
            raise ValueError("only the installed public test credential is supported")
        seed = statement.bip39_seed(credential["mnemonic"], credential["passphrase"])
        path = tuple(statement.parse_path(public_input["path"]))
        epoch = getattr(a, "epoch", 0)
        xi = w.derive_epoch_seed(seed, "ML-DSA-44", path, epoch)
        pk = cr("pk", xi)
        commit = cr("hash", b"\x01" + pk)
        owner = statement.derive(seed, path, SimpleNamespace(keccak=lambda data: cr("hash", data)))["address"]
        if a.command == "derive":
            print(json.dumps({"publicTestOnly": True, "path": public_input["path"], "owner": "0x" + owner.hex(),
                "epoch": epoch, "publicKey": pk.hex(), "commitment": commit.hex(), "publicTestSeed": xi.hex()}))
            return
        cfg = dict(chain_id=13378, registry="0x" + "00" * 18 + "0800", max_priority_fee_per_gas=10**9,
                   max_fee_per_gas=2 * 10**9, migration_gas_limit=16000000, pq_transaction_gas_limit=1500000)
        if a.command == "recover":
            run = a.proof_run.resolve()
            doc = json.loads((run / "statement/statement.json").read_text())
            public_test = doc.get("publicTestOnly") is True or (
                doc.get("schema") == "pq-proof-pipeline/statement/v1"
                and doc.get("input", {}).get("credential", {}).get("public") is True)
            if not public_test:
                raise ValueError("proof is not explicitly a public fixture")
            pi = bytes.fromhex(doc["pi198_hex"])
            proof = (run / "f/proof.postcard").read_bytes()
            if len(pi) != 198 or int.from_bytes(pi[:32], "big") != 13378 or pi[64:84] != owner or pi[93:125] != commit or not int(time.time()) <= int.from_bytes(pi[129:137], "big") <= int(time.time()) + 604800:
                raise ValueError("proof owner, key or current expiry differs")
            lib = ctypes.CDLL(str(ROOT / "lib/libpq_final_native.so"))
            lib.pq_f_verify_v1.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.c_char_p, ctypes.c_size_t]
            lib.pq_f_verify_v1.restype = ctypes.c_int32
            if lib.pq_f_verify_v1(proof, len(proof), pi, len(pi)) != 0:
                raise ValueError("proof rejected by the fixed native verifier")
            mode, cap, until = pi[169], int.from_bytes(pi[137:169], "big"), int.from_bytes(pi[190:198], "big")
            if mode == 3 and not a.consent_account_reimbursement:
                raise ValueError("mode 3 requires explicit --consent-account-reimbursement")
            consent = w.fee_consent(layout=2, max_account_fee=cap, verifier_version=0x80000008, fee_auth_until=until) if mode == 3 else None
            fee = w.FeeChoice(fee_mode=mode, fee_sponsor=pi[170:190].hex(), fee_auth_until=until, consent=consent["token"] if consent else None)
            sponsor = None
            if mode:
                s = json.loads((ROOT / "share/l1/PUBLIC-sponsor.json").read_text())
                sponsor = w.Sponsor(s["address"], int.from_bytes(pi[129:137], "big"),
                    lambda message, context: cr("sign", bytes.fromhex(s["xi"]), message, context), bytes.fromhex(s["pk"]))
            raw = w._encode_0x7e(SimpleNamespace(chain_id=13378, legacy_address=owner.hex()), int.from_bytes(pi[84:92], "big"), pi, proof, cfg, fee, sponsor=sponsor, crypto=cr)
        else:
            if a.nonce < 0 or a.value < 0:
                raise ValueError("nonce and value must be nonnegative")
            cfg["recipient"] = a.to.removeprefix("0x")
            if len(bytes.fromhex(cfg["recipient"])) != 20:
                raise ValueError("recipient must be an address")
            raw, _ = w.wire.signed_pq(cr, cfg, owner, {"public_key": pk.hex(), "public_test_seed": xi.hex()}, a.nonce, a.value, a.activate)
        with a.out.open("xb") as f:
            f.write(raw)
        print(json.dumps({"publicTestOnly": True, "bytes": len(raw), "hash": "0x" + cr("hash", raw).hex(),
            "sha256": hashlib.sha256(raw).hexdigest(), "scope": "Public carrier demo; no production wallet recovery/tracking acceptance"}))
    finally:
        cr.close()


if __name__ == "__main__":
    main()
