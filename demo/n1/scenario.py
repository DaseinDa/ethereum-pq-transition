"""N1 lab scenario (design note section 3.8): the beacon snapshot, the checkpoint profile, A's lab labels, the leanXMSS key
material of the honest owners (node H) and of the attacker A (node X), and the registration plan.

  scenario.py snapshot --out SNAPSHOT.json
  scenario.py keys     --prefix INSTALL --root WORK --public-out PUBLIC.json   (never overwrites a key directory)
  scenario.py labels   --public PUBLIC.json --out LABELS.json

Snapshot: N = 10 interop BLS keys (sk_i = SHA-256(i as 32-byte LE) mod r), 32 ETH each, 0x01 credentials to public
test accounts m/44'/60'/0'/0/(100 + i); validator 7's credential is the fixture owner 0x9858...da94 (the late path);
validator 9 has a 0x00 credential (T9). The lab's synthetic beacon chain has these validators at genesis, so the
domain's genesis_validators_root is the root of List[Validator, 2**40] over them (phase0 container, genesis values).
A holds BLS keys 6, 7, 8 (labelled by the harness; the tool cannot know).
Key stores, exactly as Ream loads them (registry YAML next to hash-sig-keys/, privkey_file relative to it):
  <root>/nodes/H/hash-sig-keys/H<i>/{attestation,proposal}.{pub,ssz}     honest owners i = 0..9
  <root>/nodes/X/hash-sig-keys/{A5x,A6,A7,A8,A9x}/...                    A's registrations (5x, 9x: invalid-signature entries)
Seeds stay in <root>/keys/seeds (public test material; never committed). Every key covers Lean slots 0..2^18. These are disposable lab keys.
research lab; not production validation.
"""
import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import n1lib as L  # noqa: E402

N = 10
A_BROKEN = [6, 7, 8]
HONEST_LABELS = ["H%d" % i for i in range(N)]
ATTACKER_LABELS = ["A5x", "A6", "A7", "A8", "A9x"]
HONEST_SENDER, ATTACKER_SENDER = 40, 41      # public test accounts that pay for the registry calls
LEAN_HORIZON = 2**18

# The registration plan of section 3.8 (rows in submission order; 'block' groups calls into blocks so that the two conflict
# orders are fixed by block order). kind: valid | invalid-signature (A signs with key 6) | after-dreg | tail | malformed.
PLAN = [
    {"block": 1, "actor": "H", "index": 0, "keys": "H0", "kind": "valid"},
    {"block": 1, "actor": "H", "index": 1, "keys": "H1", "kind": "valid"},
    {"block": 1, "actor": "H", "index": 2, "keys": "H2", "kind": "valid"},
    {"block": 2, "actor": "H", "index": 3, "keys": "H3", "kind": "valid"},
    {"block": 2, "actor": "H", "index": 4, "keys": "H4", "kind": "valid"},
    {"block": 2, "actor": "H", "index": 5, "keys": "H5", "kind": "valid"},
    {"block": 2, "actor": "H", "index": 5, "keys": "H5", "kind": "valid", "note": "same tuple again"},
    {"block": 2, "actor": "A", "index": 5, "keys": "A5x", "kind": "invalid-signature"},
    {"block": 3, "actor": "A", "index": 6, "keys": "A6", "kind": "valid", "note": "owner of 6 missed D_reg"},
    {"block": 3, "actor": "A", "index": 7, "keys": "A7", "kind": "valid", "note": "A first"},
    {"block": 3, "actor": "A", "index": None, "keys": None, "kind": "malformed", "note": "311 bytes: 'N1: length'"},
    {"block": 4, "actor": "H", "index": 7, "keys": "H7", "kind": "valid", "note": "then the owner"},
    {"block": 4, "actor": "H", "index": 8, "keys": "H8", "kind": "valid", "note": "owner first"},
    {"block": 5, "actor": "A", "index": 8, "keys": "A8", "kind": "valid", "note": "then A"},
    {"block": 5, "actor": "A", "index": 9, "keys": "A9x", "kind": "invalid-signature"},
    {"block": 5, "actor": "H", "index": 9, "keys": "H9", "kind": "withdrawal-credentials", "note": "valid signature, 0x00 credential"},
    {"block": 7, "actor": "H", "index": 6, "keys": "H6", "kind": "tail", "note": "after B_ck, before D_reg: dropped"},
    {"block": 9, "actor": "H", "index": 9, "keys": "H9", "kind": "after-dreg", "note": "reverts: 'N1: after D_reg'"},
]
EXPECTED = {"leanSet": [0, 1, 2, 3, 4, 5, 6], "excluded": {7: "conflict", 8: "conflict", 9: "withdrawal-credentials-0x00"}, "fA": "1/7",
            "aValidForged": "3/10", "included": "7/10"}


def withdrawal_credentials(i, pk):
    if i == 7:
        return "0x01" + "00" * 11 + L.FIXTURE_OWNER[2:]
    if i == 9:
        return "0x00" + L.sha(pk)[1:].hex()
    return "0x01" + "00" * 11 + L.test_account(100 + i)[1][2:]


def make_snapshot():
    vals = []
    for i in range(N):
        pk = L.bls_pk(L.interop_sk(i))
        vals.append({"index": i, "pubkey": "0x" + pk.hex(), "withdrawalCredentials": withdrawal_credentials(i, pk),
                     "effectiveBalanceGwei": 32 * 10**9, "slashed": False, "activationEligibilityEpoch": 0, "activationEpoch": 0,
                     "exitEpoch": L.FAR_FUTURE_EPOCH, "withdrawableEpoch": L.FAR_FUTURE_EPOCH})
    gvr = L.validators_list_root(vals)
    return {"description": "N1 lab beacon snapshot: 10 interop validators (public test keys), 32 ETH each; the lab's "
                           "synthetic beacon chain has them at genesis", "genesisForkVersion": "0x" + L.GENESIS_FORK_VERSION.hex(),
            "genesisValidatorsRoot": "0x" + gvr.hex(), "interopSecretKeys": "sk_i = SHA-256(i as 32-byte LE) mod r",
            "validators": vals}


def make_profile(snapshot, dreg, s_time, run_id, registry_keccak):
    if dreg != s_time:
        raise ValueError("this profile requires S = T0 = D_reg")
    return {"description": "N1 checkpoint profile (lab)", "runId": run_id, "elChainId": 13378, "verifierVersion": "0x80000008",
            "registry": L.REGISTRY_ADDRESS, "registryRuntimeKeccak": registry_keccak, "dReg": dreg, "S": s_time, "T0": s_time,
            "secondsPerSlot": 12, "justificationLookbackSlots": 3, "leanHorizon": LEAN_HORIZON,
            "leanSchemeName": L.LEAN_SCHEME_NAME.decode(), "leanSchemeId": "0x" + L.LEAN_SCHEME_ID.hex(),
            "domainType": "0x" + L.DOMAIN_N1_REGISTRATION.hex(), "genesisForkVersion": snapshot["genesisForkVersion"],
            "genesisValidatorsRoot": snapshot["genesisValidatorsRoot"]}


def store_dir(root, label):
    return Path(root) / "nodes" / ("H" if label.startswith("H") else "X") / "hash-sig-keys" / label


def gen_keys(root, public_out, prefix):
    root = Path(root)
    seeds = root / "keys" / "seeds"
    seeds.mkdir(parents=True, exist_ok=True)
    os.chmod(root / "keys", 0o700)
    tool = Path(prefix) / "bin/fresh-public-keys"
    pub = {}
    for label in HONEST_LABELS + ATTACKER_LABELS:
        d = store_dir(root, label)
        if d.exists():
            raise SystemExit("refusing to overwrite key directory " + str(d))
        d.parent.mkdir(parents=True, exist_ok=True)
        seed = seeds / (label + "-PUBLIC-seeds.bin")
        seed.write_bytes(os.urandom(64))
        seed.chmod(0o600)
        t = time.time()
        q = subprocess.run([str(tool), str(d), str(seed)], capture_output=True, text=True, timeout=900)
        (root / "keys" / (label + "-keygen.log")).write_text(q.stdout + q.stderr)
        assert q.returncode == 0, (label, q.stderr[-400:])
        gen = {r: dict(line.split("=", 1) for line in (d / (r + "-generation.txt")).read_text().split()) for r in ("attestation", "proposal")}
        holder = "H" if label.startswith("H") else "X"
        index = int(label[1]) if label[1:].isdigit() or label[1].isdigit() else None
        pub[label] = {"attestation": "0x" + (d / "attestation.pub").read_bytes().hex(),
                      "proposal": "0x" + (d / "proposal.pub").read_bytes().hex(), "holder": holder, "beaconIndex": index,
                      "role": "honest owner" if holder == "H" else ("A: invalid-signature entry" if label.endswith("x") else "A: forged registration"),
                      "activation": gen["attestation"]["activation"], "prepared": gen["attestation"]["prepared"],
                      "keygenSeconds": round(time.time() - t, 2), "storeDir": str(d)}
        for r in ("attestation", "proposal"):
            assert not L.lean_key_problems(bytes.fromhex(pub[label][r][2:])), (label, r)
    rec = {"description": "N1 lab leanXMSS public keys (packaged fresh-public-keys, leanSig 15cbdd43, activation 0..2^18); "
                          "secret keys and seeds stay in the private work directory", "publicTestOnly": True,
           "tool": str(tool), "toolSHA256": L.file_sha256(Path(prefix) / "libexec/fresh-public-keys"), "keys": pub}
    Path(public_out).write_text(json.dumps(rec, indent=1) + "\n")
    return rec


def make_labels(public):
    keys = public["keys"]
    return {"note": "lab-only labels: A holds BLS keys 6, 7, 8 and the leanXMSS keys of its registrations; the tool cannot "
                    "know them", "attacker": {"brokenIndices": A_BROKEN,
                                             "leanKeys": sorted(keys[x][r] for x in ATTACKER_LABELS for r in ("attestation", "proposal"))}}


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("snapshot")
    s.add_argument("--out", type=Path, required=True)
    k = sub.add_parser("keys")
    k.add_argument("--root", type=Path, required=True)
    k.add_argument("--prefix", type=Path, required=True)
    k.add_argument("--public-out", type=Path, required=True)
    b = sub.add_parser("labels")
    b.add_argument("--public", type=Path, required=True)
    b.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    if a.cmd == "snapshot":
        a.out.write_text(json.dumps(make_snapshot(), indent=1) + "\n")
    elif a.cmd == "keys":
        rec = gen_keys(a.root, a.public_out, a.prefix)
        print(json.dumps({x: v["keygenSeconds"] for x, v in rec["keys"].items()}))
    else:
        a.out.write_text(json.dumps(make_labels(json.loads(a.public.read_text())), indent=1) + "\n")


if __name__ == "__main__":
    main()
