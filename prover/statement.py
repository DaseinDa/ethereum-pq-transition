"""Build public PI198 metadata; receive owner credentials through stdin only."""
import argparse
import resource
import datetime
import hashlib
import hmac
import json
import subprocess
import sys
import unicodedata
from pathlib import Path

sys.dont_write_bytecode = True
P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798, 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
HARDENED = 1 << 31
REVIEW = "loop-internal self-review; not independently reviewed"
TIER = "research packaging; loop-internal self-review; not independently reviewed"


class Crypto:
    """The pinned ML-DSA-44 and Keccak-256 public-test helper, one
    process, one request per line: `pk XI`, `sign XI MSG CTX`, `verify PK MSG CTX SIG`, `hash DATA` (hex; `-` for empty)."""

    def __init__(self, path: Path, expected_sha256: str):
        got = hashlib.sha256(path.read_bytes()).hexdigest()
        if got != expected_sha256:
            raise SystemExit(f"crypto helper {path} has SHA-256 {got}, not the pinned {expected_sha256}")
        self.path = path
        self.proc = subprocess.Popen([str(path)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1)

    def __call__(self, op: str, *args: bytes) -> str:
        self.proc.stdin.write(" ".join([op, *[(a.hex() or "-") for a in args]]) + "\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline().strip()
        if not line:
            raise RuntimeError(self.proc.stderr.read())
        return line

    def keccak(self, data: bytes) -> bytes:
        return bytes.fromhex(self("hash", data))

    def close(self):
        self.proc.stdin.close()
        try:
            assert self.proc.wait(timeout=10) == 0
        finally:
            self.proc.stdout.close()
            self.proc.stderr.close()


# ---------- secp256k1 and BIP-32 (pure Python; public test credentials only, not constant time) ----------

def ec_add(a, b):
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0] and (a[1] + b[1]) % P == 0:
        return None
    if a == b:
        lam = 3 * a[0] * a[0] * pow(2 * a[1], -1, P) % P
    else:
        lam = (b[1] - a[1]) * pow(b[0] - a[0], -1, P) % P
    x = (lam * lam - a[0] - b[0]) % P
    return (x, (lam * (a[0] - x) - a[1]) % P)


def ec_mul(k: int):
    r, q = None, G
    while k:
        if k & 1:
            r = ec_add(r, q)
        q = ec_add(q, q)
        k >>= 1
    return r


def ser_p(pt) -> bytes:
    return bytes([2 + (pt[1] & 1)]) + pt[0].to_bytes(32, "big")


def parse_path(text: str) -> list:
    parts = text.split("/")
    if parts[0] != "m":
        raise SystemExit("a path starts with m/")
    out = []
    for p in parts[1:]:
        hard = p.endswith("'") or p.endswith("h")
        i = int(p.rstrip("'h"))
        if not 0 <= i < HARDENED:
            raise SystemExit(f"path index {p} out of range")
        out.append(i | HARDENED if hard else i)
    return out


def path_text(path: list) -> str:
    return "m/" + "/".join(f"{i & ~HARDENED}'" if i & HARDENED else str(i) for i in path)


def check_shape(path: list) -> None:
    """The five-level shape of spec section 16.3: 44', 60', a' (hardened), c in {0, 1}, i < 2^31."""
    ok = len(path) == 5 and path[0] == 44 | HARDENED and path[1] == 60 | HARDENED and path[2] >= HARDENED and path[3] in (0, 1) and path[4] < HARDENED
    if not ok:
        raise SystemExit(f"the path {path_text(path)} does not have the five-level shape m/44'/60'/a'/c/i of spec section 16.3")


def bip39_seed(mnemonic: str, passphrase: str) -> bytes:
    m = unicodedata.normalize("NFKD", mnemonic).encode()
    s = unicodedata.normalize("NFKD", "mnemonic" + passphrase).encode()
    return hashlib.pbkdf2_hmac("sha512", m, s, 2048, 64)


def derive(seed64: bytes, path: list, crypto: Crypto) -> dict:
    """BIP-32 CKDpriv along the path (spec section 16.3: an invalid child aborts, no retry), the final public key and
    the address keccak256(x || y)[12:]."""
    i = hmac.digest(b"Bitcoin seed", seed64, "sha512")
    k, c = int.from_bytes(i[:32], "big"), i[32:]
    if not 0 < k < N:
        raise SystemExit("invalid master key")
    for idx in path:
        data = (b"\x00" + k.to_bytes(32, "big")) if idx >= HARDENED else ser_p(ec_mul(k))
        i = hmac.digest(c, data + idx.to_bytes(4, "big"), "sha512")
        il = int.from_bytes(i[:32], "big")
        child = (il + k) % N
        if il >= N or child == 0:
            raise SystemExit("invalid child key on this path")
        k, c = child, i[32:]
    pub = ec_mul(k)
    uncompressed = pub[0].to_bytes(32, "big") + pub[1].to_bytes(32, "big")
    return {"address": crypto.keccak(uncompressed)[12:], "public_key_uncompressed": b"\x04" + uncompressed}


# ---------- PI198, layout 2 ----------

FIELDS = [("chain_id", 0, 32), ("DOMAIN_TAG", 32, 32), ("legacy_address", 64, 20), ("migration_nonce", 84, 8), ("alg_id", 92, 1),
          ("pq_pk_commit", 93, 32), ("verifier_version", 125, 4), ("expiry", 129, 8), ("max_account_fee", 137, 32),
          ("fee_mode", 169, 1), ("fee_sponsor", 170, 20), ("fee_auth_until", 190, 8)]
INTEGERS = {"chain_id", "migration_nonce", "alg_id", "verifier_version", "expiry", "max_account_fee", "fee_mode", "fee_auth_until"}


def domain_tag(chain_id: int, crypto: Crypto) -> bytes:
    return crypto.keccak(b"PQ-MIGRATE-v1" + chain_id.to_bytes(32, "big"))


def encode_pi(f: dict) -> bytes:
    out = bytearray(198)
    for name, off, width in FIELDS:
        v = f[name]
        b = v.to_bytes(width, "big") if name in INTEGERS else bytes(v)
        assert len(b) == width, name
        out[off:off + width] = b
    return bytes(out)


def decode_pi(pi: bytes) -> dict:
    assert len(pi) == 198
    return {name: (int.from_bytes(pi[off:off + w], "big") if name in INTEGERS else pi[off:off + w]) for name, off, w in FIELDS}


def utc(t: int) -> str:
    return datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def canonical_checks(f: dict, crypto: Crypto) -> dict:
    """The rules every node-computed layout-2 PI meets (the verifier crate's Pi198::check_canonical), plus one builder
    policy that the verifier does not check: the verifier version lies in the reserved research range (>= 0x80000000)."""
    zero = f["fee_sponsor"] == bytes(20)
    mode = f["fee_mode"]
    checks = {
        "domain_tag_is_keccak256_of_PQ-MIGRATE-v1_and_u256_chain_id": f["DOMAIN_TAG"] == domain_tag(f["chain_id"], crypto),
        "pq_pk_commit_nonzero": f["pq_pk_commit"] != bytes(32),
        "fee_mode_in_0_to_3": mode in (0, 1, 2, 3),
        "fee_fields_fit_the_mode": (mode in (0, 2) and zero and f["fee_auth_until"] == 0)
        or (mode == 1 and not zero and f["fee_auth_until"] <= f["expiry"]) or (mode == 3 and zero and f["fee_auth_until"] <= f["expiry"]),
        "verifier_version_in_the_reserved_research_range": f["verifier_version"] >= 0x80000000,
    }
    return checks


def fields_json(f: dict) -> dict:
    out = {}
    for name, off, width in FIELDS:
        v = f[name]
        out[name] = {"offset": off, "bytes": width, "hex": (v.to_bytes(width, "big") if name in INTEGERS else bytes(v)).hex()}
        if name in INTEGERS:
            out[name]["value"] = str(v) if v >= 2**53 else v
    out["verifier_version"]["display"] = f"{f['verifier_version']:#010x}"
    out["expiry"]["utc"] = utc(f["expiry"])
    out["legacy_address"]["display"] = "0x" + bytes(f["legacy_address"]).hex()
    return out


def pq_key(xi: bytes, crypto: Crypto) -> dict:
    pk = bytes.fromhex(crypto("pk", xi))
    assert len(pk) == 1312, "ML-DSA-44 public keys have 1,312 bytes"
    commit = crypto.keccak(b"\x01" + pk)
    msg, ctx = b"pq-proof-pipeline key-pair self-check", b"ETH-PQ-TEST/v1"
    sig = bytes.fromhex(crypto("sign", xi, msg, ctx))
    ok = crypto("verify", pk, msg, ctx, sig) == "true"
    bad = crypto("verify", pk, msg + b"!", ctx, sig) == "true"
    return {"xi": xi, "pk": pk, "commit": commit, "self_check": {"message_hex": msg.hex(), "context": ctx.decode(), "signature_bytes": len(sig),
            "signature_sha256": hashlib.sha256(sig).hexdigest(), "verifies": ok, "other_message_verifies": bad}}


# ---------- modes ----------

def read_input(source):
    inp = json.load(sys.stdin) if str(source) == "-" else json.loads(Path(source).read_text())
    if str(source) != "-" and inp.get("credential", {}).get("public") is not True:
        raise ValueError("owner credentials must be supplied on stdin; files are public-test input only")
    return inp


def prepare(inp, repo, crypto_path, crypto_sha256):
    """Return the witness in memory and a separate, allowlisted public description."""
    crypto = Crypto(Path(crypto_path), crypto_sha256)
    try:
        sys.path.insert(0, str(Path(repo) / "wallet"))
        import wallet_epochs  # read-only: the wallet component's key-derivation rule
        cred = inp["credential"]
        if "mnemonic" in cred:
            seed64 = bip39_seed(cred["mnemonic"], cred.get("passphrase", ""))
        else:
            seed64 = bytes.fromhex(cred["seed64_hex"])
        if len(seed64) != 64:
            raise SystemExit("seed64 must have 64 bytes")
        path = parse_path(inp["path"])
        check_shape(path)
        d = derive(seed64, path, crypto)
        pin = inp["pi"]
        if "pq_key" in inp and "xi_hex" in inp["pq_key"]:
            xi = bytes.fromhex(inp["pq_key"]["xi_hex"])
            rule = "the given ML-DSA-44 seed xi"
        else:
            epoch = inp.get("pq_key", {}).get("epoch", pin.get("migration_nonce", 0))
            xi = wallet_epochs.derive_epoch_seed(seed64, "ML-DSA-44", tuple(path), epoch)
            msg = wallet_epochs.key_derivation_message("ML-DSA-44", tuple(path), epoch)
            rule = (f"the wallet component's rule, wallet_epochs.derive_epoch_seed(seed64, 'ML-DSA-44', path, {epoch}): "
                    f"HMAC-SHA512(seed64, m)[0:32], m = ASCII('PQ-MIGRATE-v1/ML-DSA-44/') || ser32 of the five path indices"
                    f"{' || / || ser32(epoch)' if epoch else ''} = 0x{msg.hex()}")
        key = pq_key(xi, crypto)
        if "expiry_utc" in pin:
            expiry = int(datetime.datetime.strptime(pin["expiry_utc"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=datetime.timezone.utc).timestamp())
            if "expiry" in pin and pin["expiry"] != expiry:
                raise SystemExit("expiry and expiry_utc differ")
        else:
            expiry = int(pin["expiry"])
        chain_id = int(pin["chain_id"])
        f = {
            "chain_id": chain_id,
            "DOMAIN_TAG": domain_tag(chain_id, crypto),
            "legacy_address": d["address"],
            "migration_nonce": int(pin.get("migration_nonce", 0)),
            "alg_id": int(pin.get("alg_id", 1)),
            "pq_pk_commit": key["commit"],
            "verifier_version": int(str(pin["verifier_version"]), 0),
            "expiry": expiry,
            "max_account_fee": int(str(pin["max_account_fee_wei"]), 0),
            "fee_mode": int(pin.get("fee_mode", 0)),
            "fee_sponsor": bytes.fromhex(str(pin.get("fee_sponsor", "0x" + "00" * 20)).removeprefix("0x")),
            "fee_auth_until": int(pin.get("fee_auth_until", 0)),
        }
        if f["alg_id"] != 1:
            raise SystemExit("this pipeline derives ML-DSA-44 keys only (alg_id 1)")
        if "legacy_address" in pin and bytes.fromhex(pin["legacy_address"].removeprefix("0x")) != d["address"]:
            raise SystemExit("the given legacy_address is not the credential's address on this path")
        pi = encode_pi(f)
        assert decode_pi(pi) == f
        checks = canonical_checks(f, crypto)
        if not all(checks.values()):
            raise SystemExit(f"the PI is not canonical: {checks}")
        public = {"schema": "pq-proof-pipeline/statement/v2", "review": REVIEW,
                  "publicTestOnly": cred.get("public") is True, "pi198_hex": pi.hex(),
                  "pi198_sha256": hashlib.sha256(pi).hexdigest(), "fields": fields_json(f),
                  "canonical_checks": checks, "derivation": {"legacy_address": "0x" + d["address"].hex()}}
        public_key = {"alg_id": 1, "publicTestOnly": cred.get("public") is True,
                      "public_key_hex": key["pk"].hex(), "public_key_bytes": len(key["pk"]),
                      "public_key_sha256": hashlib.sha256(key["pk"]).hexdigest(),
                      "pq_pk_commit": key["commit"].hex()}
        witness = {"seed64_hex": seed64.hex(), "path": path, "pi198_hex": pi.hex()}
        return witness, public, public_key
    finally:
        crypto.close()


def save_public(out, public, public_key):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    (out / "pi198.hex").write_text(public["pi198_hex"] + "\n")
    (out / "statement.json").write_text(json.dumps(public, indent=2) + "\n")
    (out / "pq-key.json").write_text(json.dumps(public_key, indent=2) + "\n")


def build(args) -> None:
    _, public, public_key = prepare(read_input(args.input), args.repo, args.crypto, args.crypto_sha256)
    save_public(args.out, public, public_key)
    print(json.dumps({"pi198_sha256": public["pi198_sha256"], "publicTestOnly": public["publicTestOnly"]}))


DECODE_KEYS = {"mnemonic", "passphrase", "path", "xi"}


def read_decode_credentials() -> dict:
    """Read the decoder's credentials as one JSON object on stdin, never from argv: `mnemonic` with its `path` (and an
    optional BIP-39 `passphrase`) to check the address, and/or `xi` (hex) to check the ML-DSA-44 key commitment."""
    doc = json.load(sys.stdin)
    if not isinstance(doc, dict) or not doc or set(doc) - DECODE_KEYS or not all(isinstance(v, str) for v in doc.values()):
        raise ValueError("decode credentials must be a JSON object of strings with keys among mnemonic, passphrase, path, xi")
    if ("mnemonic" in doc) != ("path" in doc) or ("passphrase" in doc and "mnemonic" not in doc):
        raise ValueError("a mnemonic needs its path, and a path or passphrase needs a mnemonic")
    return doc


def decode(args) -> None:
    crypto = Crypto(Path(args.crypto), args.crypto_sha256)
    pi = bytes.fromhex("".join(Path(args.pi).read_text().split()))
    if len(pi) != 198:
        raise SystemExit("PI198 must have 198 bytes")
    f = decode_pi(pi)
    doc = {"pi198_hex": pi.hex(), "pi198_sha256": hashlib.sha256(pi).hexdigest(), "fields": fields_json(f), "canonical_checks": canonical_checks(f, crypto),
           "domain_tag_recomputed": domain_tag(f["chain_id"], crypto).hex()}
    if args.credentials_stdin:
        cred = read_decode_credentials()
        if "mnemonic" in cred:
            # The same derivation as `build`: the mnemonic as given, its passphrase, and the five-level path shape.
            path = parse_path(cred["path"])
            check_shape(path)
            d = derive(bip39_seed(cred["mnemonic"], cred.get("passphrase", "")), path, crypto)
            doc["address_from_credential"] = {"legacy_address": "0x" + d["address"].hex(),
                                              "equals_pi_field": d["address"] == f["legacy_address"]}
        if "xi" in cred:
            key = pq_key(bytes.fromhex(cred["xi"]), crypto)
            doc["pq_key"] = {"public_key_sha256": hashlib.sha256(key["pk"]).hexdigest(), "public_key_hex": key["pk"].hex(),
                             "pq_pk_commit": key["commit"].hex(), "equals_pi_field": key["commit"] == f["pq_pk_commit"],
                             "key_pair_self_check": key["self_check"]}
    crypto.close()
    print(json.dumps(doc, indent=1))


class CustodyParser(argparse.ArgumentParser):
    def error(self, message):
        self.exit(2, "invalid arguments; credentials must be supplied on stdin\n")


def main() -> None:
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    ap = CustodyParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="mode", required=True)
    b = sub.add_parser("build")
    b.add_argument("input")
    b.add_argument("out")
    d = sub.add_parser("decode")
    d.add_argument("pi")
    d.add_argument("--credentials-stdin", action="store_true",
                   help="read {mnemonic, passphrase, path, xi} as one JSON object from stdin (never argv)")
    for p in (b, d):
        p.add_argument("--repo", required=True)
        p.add_argument("--crypto", required=True)
        p.add_argument("--crypto-sha256", required=True)
    args = ap.parse_args()
    try:
        build(args) if args.mode == "build" else decode(args)
    except (Exception, SystemExit):
        raise SystemExit("statement processing failed; credential details suppressed") from None


if __name__ == "__main__":
    main()
