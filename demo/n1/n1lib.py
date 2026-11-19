"""N1 checkpoint path (lab): shared library.

SSZ registration message and signing domain, interop BLS12-381 keys, the synthetic beacon snapshot, leanXMSS key
checks, a minimal RLP and EIP-1559 signer for public BIP-39 test accounts, JSON-RPC and Engine API helpers.
Public test material only; offline; no personal data. Needs py_ecc 8.0.0, eth_hash and pycryptodome (the pinned tool-specific Python environment). research lab; not production validation.
"""
import base64
import hashlib
import hmac
import json
import struct
import time
import urllib.error
import urllib.request

from eth_hash.auto import keccak
from py_ecc.bls import G2ProofOfPossession as bls
from py_ecc.optimized_bls12_381 import curve_order
from py_ecc.secp256k1 import secp256k1 as k1

# ---------------------------------------------------------------- constants
KOALABEAR_P = 0x7F000001                 # leanSig field modulus; every key element is a canonical u32 < p
LEAN_KEY_BYTES = 52                      # SSZ GeneralizedXMSSPublicKey {root: 8 elements, parameter: 5 elements}
LEAN_SCHEME_NAME = b"leanSig@15cbdd43/SIGAbortingTargetSumLifetime32Dim46Base8"
LEAN_SCHEME_ID = hashlib.sha256(LEAN_SCHEME_NAME).digest()
DOMAIN_N1_REGISTRATION = bytes.fromhex("4e310001")   # lab-only, application class
GENESIS_FORK_VERSION = bytes.fromhex("4e310000")     # lab-only fork version of the synthetic beacon snapshot
FAR_FUTURE_EPOCH = 2**64 - 1
MESSAGE_BYTES, SIGNATURE_BYTES = 216, 96
PAYLOAD_BYTES = MESSAGE_BYTES + SIGNATURE_BYTES      # 312
REGISTRY_ADDRESS = "0x0000000000000000000000000000000000004e31"
REGISTERED_TOPIC = "0x" + keccak(b"Registered(uint64,uint64,bytes32,bytes)").hex()
GWEI = 10**9
ETH = 10**18
ZERO32 = b"\x00" * 32
MNEMONIC = " ".join(["abandon"] * 11 + ["about"])  # the public BIP-39 test vector
FIXTURE_OWNER = "0x9858effd232b4033e47d90003d41ec34ecaeda94"  # m/44'/60'/0'/0/0 of MNEMONIC; the lab fixture owner


def sha(b):
    return hashlib.sha256(b).digest()


# ---------------------------------------------------------------- SSZ (fixed-size types only)
def merkleize(chunks, limit=None):
    n = len(chunks) if limit is None else limit
    size = 1
    while size < max(n, 1):
        size *= 2
    layer = list(chunks) + [ZERO32] * (size - len(chunks))
    while len(layer) > 1:
        layer = [sha(layer[i] + layer[i + 1]) for i in range(0, len(layer), 2)]
    return layer[0]


def pack(b):
    return [(b[i:i + 32] + ZERO32)[:32] for i in range(0, len(b), 32)] or [ZERO32]


def u64(v):
    return int(v).to_bytes(8, "little")


def root_u64(v):
    return (u64(v) + ZERO32)[:32]


def root_bool(v):
    return (bytes([1 if v else 0]) + ZERO32)[:32]


def root_bytes(b):
    return merkleize(pack(b))


def compute_domain(domain_type, fork_version, genesis_validators_root):
    fork_data_root = merkleize([(fork_version + ZERO32)[:32], genesis_validators_root])
    return domain_type + fork_data_root[:28]


def signing_root(object_root, domain):
    return sha(object_root + domain)          # hash_tree_root(SigningData(object_root, domain))


# Beacon phase0 Validator container (genesis values); the lab's synthetic beacon chain has these validators at its
# genesis, so its genesis_validators_root is the root of List[Validator, 2**40] over them.
def validator_root(v):
    return merkleize([root_bytes(bytes.fromhex(v["pubkey"][2:])), bytes.fromhex(v["withdrawalCredentials"][2:]),
                      root_u64(v["effectiveBalanceGwei"]), root_bool(v.get("slashed", False)),
                      root_u64(v.get("activationEligibilityEpoch", 0)), root_u64(v.get("activationEpoch", 0)),
                      root_u64(v.get("exitEpoch", FAR_FUTURE_EPOCH)), root_u64(v.get("withdrawableEpoch", FAR_FUTURE_EPOCH))])


def validators_list_root(validators, depth=40):
    layer = [validator_root(v) for v in validators]
    zero = ZERO32
    for _ in range(depth):
        if len(layer) % 2:
            layer = layer + [zero]
        layer = [sha(layer[i] + layer[i + 1]) for i in range(0, len(layer), 2)] or [sha(zero + zero)]
        zero = sha(zero + zero)
    return sha(layer[0] + len(validators).to_bytes(32, "little"))


# ---------------------------------------------------------------- registration message
FIELDS = [("el_chain_id", "u64"), ("validator_index", "u64"), ("bls_pubkey", 48), ("lean_attestation_pubkey", 52),
          ("lean_proposal_pubkey", 52), ("lean_scheme_id", 32), ("activation_epoch", "u64"), ("num_active_epochs", "u64")]


def encode_message(m):
    out = b""
    for name, kind in FIELDS:
        v = m[name]
        if kind == "u64":
            out += u64(v)
        else:
            assert isinstance(v, (bytes, bytearray)) and len(v) == kind, (name, len(v))
            out += bytes(v)
    assert len(out) == MESSAGE_BYTES
    return out


def decode_payload(payload):
    """312 bytes -> (message dict, signature). Raises ValueError on a wrong length."""
    if len(payload) != PAYLOAD_BYTES:
        raise ValueError("payload length %d != %d" % (len(payload), PAYLOAD_BYTES))
    m, off = {}, 0
    for name, kind in FIELDS:
        if kind == "u64":
            m[name] = int.from_bytes(payload[off:off + 8], "little")
            off += 8
        else:
            m[name] = bytes(payload[off:off + kind])
            off += kind
    return m, bytes(payload[off:])


def message_root(m):
    roots = []
    for name, kind in FIELDS:
        roots.append(root_u64(m[name]) if kind == "u64" else root_bytes(m[name]))
    return merkleize(roots)


def message_json(m):
    return {k: (v if isinstance(v, int) else "0x" + v.hex()) for k, v in m.items()}


# ---------------------------------------------------------------- BLS (interop keys: public test material)
def interop_sk(i):
    return int.from_bytes(sha(int(i).to_bytes(32, "little")), "little") % curve_order


def bls_pk(sk):
    return bls.SkToPk(sk)


def bls_sign(sk, root):
    return bls.Sign(sk, root)


def bls_verify(pk, root, sig):
    try:
        return bool(bls.Verify(pk, root, sig))
    except Exception:   # malformed points are invalid signatures, never tool failures
        return False


# ---------------------------------------------------------------- leanXMSS public keys
def lean_key_problems(key):
    """Structural check Ream does not do (probe 3): 52 bytes = 13 little-endian u32, each a canonical KoalaBear element."""
    if len(key) != LEAN_KEY_BYTES:
        return ["length %d != 52" % len(key)]
    vals = struct.unpack("<13I", key)
    return ["element %d = 0x%08x >= p" % (i, x) for i, x in enumerate(vals) if x >= KOALABEAR_P]


# ---------------------------------------------------------------- RLP, EIP-1559, BIP-32 (public test accounts)
def _int_bytes(n):
    return n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""


def rlp(x):
    if isinstance(x, int):
        x = _int_bytes(x)
    if isinstance(x, (bytes, bytearray)):
        x = bytes(x)
        if len(x) == 1 and x[0] < 0x80:
            return x
        return _rlp_len(len(x), 0x80) + x
    body = b"".join(rlp(i) for i in x)
    return _rlp_len(len(body), 0xC0) + body


def _rlp_len(n, offset):
    if n < 56:
        return bytes([offset + n])
    b = _int_bytes(n)
    return bytes([offset + 55 + len(b)]) + b


def bip39_seed(mnemonic=MNEMONIC, passphrase=""):
    return hashlib.pbkdf2_hmac("sha512", mnemonic.encode(), b"mnemonic" + passphrase.encode(), 2048)


def _compressed(priv):
    x, y = k1.privtopub(priv.to_bytes(32, "big"))
    return bytes([2 + (y & 1)]) + x.to_bytes(32, "big")


def bip32_priv(path, seed=None):
    seed = seed or bip39_seed()
    i = hmac.new(b"Bitcoin seed", seed, hashlib.sha512).digest()
    k, c = int.from_bytes(i[:32], "big"), i[32:]
    for part in path.split("/")[1:]:
        hard = part.endswith("'")
        idx = int(part.rstrip("'")) + (2**31 if hard else 0)
        data = (b"\x00" + k.to_bytes(32, "big") if hard else _compressed(k)) + idx.to_bytes(4, "big")
        i = hmac.new(c, data, hashlib.sha512).digest()
        k, c = (int.from_bytes(i[:32], "big") + k) % k1.N, i[32:]
    return k


def address_of(priv):
    x, y = k1.privtopub(priv.to_bytes(32, "big"))
    return "0x" + keccak(x.to_bytes(32, "big") + y.to_bytes(32, "big"))[12:].hex()


def test_account(i):
    """Public test account m/44'/60'/0'/0/i of the BIP-39 'abandon x11 about' vector."""
    priv = bip32_priv("m/44'/60'/0'/0/%d" % i)
    return priv, address_of(priv)


def sign_1559(priv, chain_id, nonce, to, data=b"", value=0, gas=200_000, max_fee=20 * GWEI, max_prio=GWEI):
    fields = [chain_id, nonce, max_prio, max_fee, gas, bytes.fromhex(to[2:]), value, data, []]
    digest = keccak(b"\x02" + rlp(fields))
    v, r, s = k1.ecdsa_raw_sign(digest, priv.to_bytes(32, "big"))
    raw = b"\x02" + rlp(fields + [v - 27, r, s])
    return raw, "0x" + keccak(raw).hex()


# ---------------------------------------------------------------- JSON-RPC and Engine API
class RPCError(Exception):
    def __init__(self, method, error):
        super().__init__("%s: %s" % (method, json.dumps(error)[:400]))
        self.error = error


_ids = [0]


def rpc_raw(url, method, params, headers=None, timeout=20):
    _ids[0] += 1
    body = json.dumps({"jsonrpc": "2.0", "id": _ids[0], "method": method, "params": params}).encode()
    h = {"Content-Type": "application/json"}
    h.update(headers or {})
    with urllib.request.urlopen(urllib.request.Request(url, body, h), timeout=timeout) as r:
        return json.load(r)


def rpc(url, method, params, timeout=20):
    res = rpc_raw(url, method, params, timeout=timeout)
    if "error" in res:
        raise RPCError(method, res["error"])
    return res["result"]


def _b64(b):
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()


def engine(url, secret_hex, method, params, timeout=60):
    secret = bytes.fromhex(secret_hex.strip().removeprefix("0x"))
    head = _b64(json.dumps({"alg": "HS256", "typ": "JWT"}).encode())
    body = _b64(json.dumps({"iat": int(time.time())}).encode())
    sig = _b64(hmac.new(secret, (head + "." + body).encode(), hashlib.sha256).digest())
    res = rpc_raw(url, method, params, {"Authorization": "Bearer " + head + "." + body + "." + sig}, timeout)
    if "error" in res:
        raise RPCError(method, res["error"])
    return res["result"]


def wait_for(fn, timeout, interval=0.25, what="condition"):
    end = time.monotonic() + timeout
    last = None
    while time.monotonic() < end:
        try:
            v = fn()
            if v:
                return v
        except (OSError, ValueError, AssertionError, RPCError) as e:
            last = repr(e)
        time.sleep(interval)
    raise TimeoutError(what + " timeout; last=" + str(last))


def file_sha256(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()
