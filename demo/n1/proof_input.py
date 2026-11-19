"""Strict public-test recovery exports for N1; no proof generation or expiry rewriting.

The export's producer is not attested. Acceptance is freshly checked with the
installed native F verifier whose source and binary identity the runtime pins.
Native verification and public fixture signing must run under the switch's lock.
"""
from dataclasses import dataclass
import ctypes
import hashlib
import json
from pathlib import Path

CHAIN = 13378
OWNER = bytes.fromhex("9858effd232b4033e47d90003d41ec34ecaeda94")
VERSION = 0x80000008
MAX_PROOF = 196608
MAX_LIFETIME = 604800


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_bounded(path, limit):
    with Path(path).open("rb") as stream:
        data = stream.read(limit + 1)
    if len(data) > limit:
        raise ValueError("oversized proof input: " + str(path.name))
    return data


def read_json(path, limit=1024 * 1024):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError("duplicate JSON field: " + key)
            result[key] = value
        return result
    result = json.loads(read_bounded(path, limit), object_pairs_hook=pairs)
    if not isinstance(result, dict):
        raise ValueError("proof metadata must be an object")
    return result


def unhex(text, size, field):
    if not isinstance(text, str) or len(text) != 2 * size:
        raise ValueError("wrong hex width: " + field)
    try:
        data = bytes.fromhex(text)
    except ValueError as error:
        raise ValueError("invalid hex: " + field) from error
    if len(data) != size or text.lower() != data.hex():
        raise ValueError("noncanonical hex: " + field)
    return data


@dataclass(frozen=True)
class PublicRecoveryProof:
    pi: bytes
    proof: bytes
    public_key: bytes
    commitment: bytes
    expiry: int
    proof_sha256: str
    pi_sha256: str


def read_public_recovery(directory, *, now, minimum_remaining=3600):
    """Read current package output filenames, retaining exact proof/PI bytes."""
    directory = Path(directory)
    record = read_json(directory / "PROOF.json")
    statement = read_json(directory / "statement/statement.json")
    key = read_json(directory / "statement/pq-key.json")
    if (record.get("status") != "PASS" or record.get("publicTestOnly") is not True
            or statement.get("schema") != "pq-proof-pipeline/statement/v2"
            or statement.get("publicTestOnly") is not True or key.get("publicTestOnly") is not True):
        raise ValueError("requires current explicitly public-test package proof output")
    # The public export never contains an owner credential or a signing seed.
    if any(name in obj for obj in (record, statement, key)
           for name in ("xi", "xi_hex", "seed64_hex", "mnemonic", "credential", "input")):
        raise ValueError("secret-bearing or historical proof metadata is not accepted")
    pi = unhex(read_bounded(directory / "statement/pi198.hex", 400).decode().strip(), 198, "pi198.hex")
    if unhex(statement.get("pi198_hex"), 198, "statement PI") != pi:
        raise ValueError("exported PI files disagree")
    proof = read_bounded(directory / "f/proof.postcard", MAX_PROOF)
    psha, isha = hashlib.sha256(proof).hexdigest(), hashlib.sha256(pi).hexdigest()
    if not proof or record.get("proofSHA256") != psha or record.get("piSHA256") != isha or statement.get("pi198_sha256") != isha:
        raise ValueError("proof/PI export hash mismatch")
    if (int.from_bytes(pi[:32], "big") != CHAIN or pi[64:84] != OWNER
            or pi[84:92] != bytes(8) or pi[92] != 1
            or int.from_bytes(pi[125:129], "big") != VERSION or pi[169:] != bytes(29)):
        raise ValueError("not the public fixture's initial unsponsored recovery statement")
    expiry = int.from_bytes(pi[129:137], "big")
    if not now + minimum_remaining < expiry <= now + MAX_LIFETIME:
        raise ValueError("proof expiry is not current or leaves too little run time")
    if int.from_bytes(pi[137:169], "big") < 16000000 * 2000000000:
        raise ValueError("proof fee cap cannot cover the fixed recovery carrier")
    public_key = unhex(key.get("public_key_hex"), 1312, "public key")
    commitment = unhex(key.get("pq_pk_commit"), 32, "public-key commitment")
    if (key.get("alg_id") != 1 or type(key.get("alg_id")) is not int
            or type(key.get("public_key_bytes")) is not int or key.get("public_key_bytes") != len(public_key)
            or key.get("public_key_sha256") != hashlib.sha256(public_key).hexdigest() or commitment != pi[93:125]):
        raise ValueError("exported public key metadata disagrees with PI")
    return PublicRecoveryProof(pi, proof, public_key, commitment, expiry, psha, isha)


def installed_verifier_binding(prefix, manifest):
    """Check acceptance-source records and the exact binaries used by this port.

    The caller must first call require_installed, which authenticates every
    installed payload and the installation completion marker.
    """
    prefix = Path(prefix)
    source = manifest.get("sourceIdentity")
    if not isinstance(source, dict) or not source.get("filesSHA256"):
        raise ValueError("installed source identity missing")
    if read_json(prefix / "share/build/source-identity.json", 16 * 1024 * 1024) != source:
        raise ValueError("installed source records disagree")
    prover = read_json(prefix / "prover-runtime/BUILD.json", 16 * 1024 * 1024)
    clients = read_json(prefix / "share/build/clients.json", 16 * 1024 * 1024)
    for record in (prover, clients):
        if (record.get("status") != "PASS" or record.get("sourceIdentity") != source
                or not manifest.get("dependencyManifestSHA256")
                or record.get("dependencyManifestSHA256") != manifest["dependencyManifestSHA256"]):
            raise ValueError("installed build source/dependency identity mismatch")
    paths = {"prover-runtime/bin/pq-test-crypto": prover.get("binaries", {}).get("pq-test-crypto"),
             "lib/libpq_final_native.so": clients.get("binaries", {}).get("lib/libpq_final_native.so")}
    for relative, digest in paths.items():
        if not digest or manifest.get("payloads", {}).get(relative, {}).get("sha256") != digest or sha(prefix / relative) != digest:
            raise ValueError("installed acceptance binary hash mismatch: " + relative)
    return {"sourceCommit": source.get("commit"), "sourceFilesSHA256": source["filesSHA256"],
            "binaries": paths, "exportOrigin": "unattested; fresh acceptance verification only"}


def verify_native(prefix, fixture):
    """Fresh native F verification; call only under the outer heavy-job lock."""
    prefix = Path(prefix)
    native = ctypes.CDLL(str(prefix / "lib/libpq_final_native.so"))
    native.pq_f_identity_v1.restype = ctypes.c_char_p
    native.pq_f_ready_v1.restype = ctypes.c_int32
    native.pq_f_verify_v1.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.c_char_p, ctypes.c_size_t]
    native.pq_f_verify_v1.restype = ctypes.c_int32
    identity = json.loads(native.pq_f_identity_v1().decode())
    expected = read_json(prefix / "share/identity/f-native.json")
    from install import PROFILE
    if (identity != expected or native.pq_f_ready_v1() != 0
            or identity.get("algorithm_digest") != PROFILE["nativeAlgorithmDigest"]
            or identity.get("f_vk_digest") != PROFILE["finalKeyDigest"]
            or identity.get("max_proof_bytes") != MAX_PROOF
            or identity.get("dev_mode") is not False or identity.get("groth16") is not False):
        raise ValueError("native F identity/readiness mismatch")
    status = native.pq_f_verify_v1(fixture.proof, len(fixture.proof), fixture.pi, len(fixture.pi))
    if status != 0:
        raise ValueError("native F rejected the unmodified exported proof: " + str(status))
    return {"status": "PASS", "identity": identity, "proofSHA256": fixture.proof_sha256,
            "piSHA256": fixture.pi_sha256}
