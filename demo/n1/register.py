"""N1 registration tool: build, sign and send a SignedN1Registration (312 bytes) to the genesis registry contract.

  register.py build  --profile P.json --snapshot S.json --index I --keys DIR --signer-interop K --out REG.json
                     [--bls-pubkey-interop K2] [--chain-id N] [--scheme-id 0xHEX] [--activation A] [--num-active N]
                     [--attestation-hex 0x..] [--proposal-hex 0x..]
  register.py send   --reg REG.json --rpc URL [--rpc URL ...] --sender ACCOUNT [--nonce N] [--chain-id 13378]
  register.py verify --reg REG.json --profile P.json --snapshot S.json

Message (SSZ, design note section 3.2): el_chain_id, validator_index, bls_pubkey, lean_attestation_pubkey, lean_proposal_pubkey,
lean_scheme_id, activation_epoch, num_active_epochs; signing_root = hash_tree_root(SigningData(hash_tree_root(message),
compute_domain(0x4e310001, genesis fork version, genesis_validators_root))). BLS keys are interop keys (public test
material); the override flags exist only to build the negative controls. Senders are public test accounts
m/44'/60'/0'/0/ACCOUNT of the BIP-39 'abandon x11 about' vector; this happens before T, so ECDSA senders are fine.
research lab; not production validation.
"""
import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import n1lib as L  # noqa: E402


def domain_of(profile):
    return L.compute_domain(bytes.fromhex(profile["domainType"][2:]), bytes.fromhex(profile["genesisForkVersion"][2:]),
                            bytes.fromhex(profile["genesisValidatorsRoot"][2:]))


def build(profile, snapshot, index, att, prop, signer_sk, *, bls_pubkey=None, chain_id=None, scheme_id=None,
          activation=0, num_active=None):
    """Return (payload bytes, message dict). bls_pubkey defaults to the snapshot's key of `index` (if any)."""
    snap = {v["index"]: v for v in snapshot["validators"]}
    if bls_pubkey is None:
        bls_pubkey = bytes.fromhex(snap[index]["pubkey"][2:]) if index in snap else L.bls_pk(signer_sk)
    m = {"el_chain_id": profile["elChainId"] if chain_id is None else chain_id, "validator_index": index,
         "bls_pubkey": bls_pubkey, "lean_attestation_pubkey": att, "lean_proposal_pubkey": prop,
         "lean_scheme_id": bytes.fromhex(profile["leanSchemeId"][2:]) if scheme_id is None else scheme_id,
         "activation_epoch": activation, "num_active_epochs": profile["leanHorizon"] if num_active is None else num_active}
    root = L.signing_root(L.message_root(m), domain_of(profile))
    sig = L.bls_sign(signer_sk, root)
    payload = L.encode_message(m) + sig
    assert len(payload) == L.PAYLOAD_BYTES
    return payload, m


def send(urls, payload, account, nonce, chain_id, to=L.REGISTRY_ADDRESS, gas=200_000):
    """Sign an EIP-1559 call to the registry from public test account `account`; submit to every node (no EL peering)."""
    priv, addr = L.test_account(account)
    raw, txhash = L.sign_1559(priv, chain_id, nonce, to, payload, gas=gas)
    answers = {}
    for url in urls:
        res = L.rpc_raw(url, "eth_sendRawTransaction", ["0x" + raw.hex()])
        answers[url] = res.get("result", res.get("error"))
    return {"hash": txhash, "from": addr, "nonce": nonce, "raw": "0x" + raw.hex(), "answers": answers}


def keys_of(d):
    return tuple((Path(d) / (r + ".pub")).read_bytes() for r in ("attestation", "proposal"))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build")
    for x in ("--profile", "--snapshot", "--out"):
        b.add_argument(x, type=Path, required=True)
    b.add_argument("--index", type=int, required=True)
    b.add_argument("--keys", type=Path)
    b.add_argument("--attestation-hex")
    b.add_argument("--proposal-hex")
    b.add_argument("--signer-interop", type=int, required=True)
    b.add_argument("--bls-pubkey-interop", type=int)
    b.add_argument("--chain-id", type=int)
    b.add_argument("--scheme-id")
    b.add_argument("--activation", type=int, default=0)
    b.add_argument("--num-active", type=int)
    s = sub.add_parser("send")
    s.add_argument("--reg", type=Path, required=True)
    s.add_argument("--rpc", action="append", required=True)
    s.add_argument("--sender", type=int, required=True)
    s.add_argument("--nonce", type=int)
    s.add_argument("--chain-id", type=int, default=13378)
    v = sub.add_parser("verify")
    for x in ("--reg", "--profile", "--snapshot"):
        v.add_argument(x, type=Path, required=True)
    a = ap.parse_args()
    if a.cmd == "build":
        profile, snapshot = json.loads(a.profile.read_text()), json.loads(a.snapshot.read_text())
        att, prop = keys_of(a.keys) if a.keys else (None, None)
        att = bytes.fromhex(a.attestation_hex[2:]) if a.attestation_hex else att
        prop = bytes.fromhex(a.proposal_hex[2:]) if a.proposal_hex else prop
        sk = L.interop_sk(a.signer_interop)
        pk = L.bls_pk(L.interop_sk(a.bls_pubkey_interop)) if a.bls_pubkey_interop is not None else None
        payload, m = build(profile, snapshot, a.index, att, prop, sk, bls_pubkey=pk, chain_id=a.chain_id,
                           scheme_id=bytes.fromhex(a.scheme_id[2:]) if a.scheme_id else None, activation=a.activation,
                           num_active=a.num_active)
        rec = {"payload": "0x" + payload.hex(), "message": L.message_json(m), "signerInterop": a.signer_interop,
               "note": "public interop BLS test key; lab only"}
        a.out.write_text(json.dumps(rec, indent=1) + "\n")
        print(json.dumps({"bytes": len(payload), "index": a.index}))
    elif a.cmd == "send":
        reg = json.loads(a.reg.read_text())
        payload = bytes.fromhex(reg["payload"][2:])
        nonce = a.nonce
        if nonce is None:
            nonce = int(L.rpc(a.rpc[0], "eth_getTransactionCount", [L.test_account(a.sender)[1], "pending"]), 16)
        print(json.dumps({k: v for k, v in send(a.rpc, payload, a.sender, nonce, a.chain_id).items() if k != "raw"}))
    else:
        import checkpoint
        reg, profile, snapshot = (json.loads(p.read_text()) for p in (a.reg, a.profile, a.snapshot))
        m, sig = L.decode_payload(bytes.fromhex(reg["payload"][2:]))
        reasons, problems = checkpoint.validate(m, sig, profile, {v["index"]: v for v in snapshot["validators"]},
                                                domain_of(profile))
        print(json.dumps({"valid": not reasons, "reasons": reasons, "leanKeyProblems": problems}))
        raise SystemExit(1 if reasons else 0)


if __name__ == "__main__":
    main()
