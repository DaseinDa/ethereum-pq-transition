#!/usr/bin/env python3
# Lean lab research client package: install, selfcheck and preflight.
# Public test fixtures only. loop-internal self-review; not
# independently reviewed.
"""Install and validate the fixed Lean local-network profile.
Public synthetic experiments only; production is disabled.
All payloads, native verifier identity and PI are checked before clients start.
A fresh installation never overwrites an existing prefix. No fallback backend.
loop-internal self-review; not independently reviewed.
"""
import argparse
import ctypes
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import PurePosixPath
from pathlib import Path
sys.dont_write_bytecode = True

PROFILE = {'legacySeedProofFromT0': True, 'chainId': 13378, 'version': 2147483656, 'nativeAlgorithmDigest': '0xead4fbe86b8ecd319816fc7999e0b3d44b8a7756d38744459fd3ab4c277f5afd', 'backend': 'l5-f-native-v1', 'proofLifetime': 604800, 'maxProofBytes': 196608, 'maxTxBytes': 199332, 'txGasCap': 16777216, 'verifyGas': 5666000, 'imageId': '0x0000000000000000000000000000000000000000000000000000000000000000', 'guestSha': '0x0000000000000000000000000000000000000000000000000000000000000000', 'verifierSha': '0x0000000000000000000000000000000000000000000000000000000000000000', 'w': 31536000, 'poolSlotSeconds': 12, 'maxPayloadBytes': 131072, 'registry': '0x0000000000000000000000000000000000000800', 'factRegistry': '0x0000000000000000000000000000000000000801', 'finalKeyDigest': '0xed2fcf813b942404729da7827c4743020dae8d89ebbc206e5bee7718503df3f2'}
REFUSED_DIGESTS = {"0x0675a90a342d394bf8b6b98f9df5e880d41fe6c6b0f605a800c33ba784ce09a2": "SHA-256 of ALGORITHM.txt",
                   "0xf620627069ad9b85321180583d4eb22455935cffeaa271b408910de54e5bf8b0": "Keccak-256 of ALGORITHM.txt"}
MAX_PROOF = 196608
AGGREGATE = {"key": "0x3f84335f8b7301181f37e3080cb81fc5d8444952574e0e90cd2a277d12bd2825",
             "verifyGas": 11771000, "nMax": 4, "maxTxBytes": 200512}


class Refused(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Refused(msg)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def check_payloads(root):
    root=Path(root).resolve()
    manifest = json.loads((root / "manifest.json").read_text())
    need(manifest.get("format")==1 and manifest.get("profile")=="pq-lean-f-native-lab-v1", "wrong package profile")
    need(manifest.get("productionEnabled") is False, "production is not enabled")
    need(manifest.get("optionalProfiles", []) == [], "unsupported optional profile")
    for rel,row in manifest["payloads"].items():
        parts=PurePosixPath(rel)
        need(rel and not parts.is_absolute() and ".." not in parts.parts and "." not in parts.parts and "\\" not in rel and str(parts)==rel, "unsafe payload path")
        p=root/rel
        need(all(not x.is_symlink() for x in [p,*list(p.parents)[:len(parts.parts)-1]]), "payload symlink")
        need(p.is_file() and p.resolve().is_relative_to(root), f"missing payload {rel}")
        need(p.stat().st_size==row["bytes"] and sha(p)==row["sha256"], f"payload hash mismatch: {rel}")
        need(oct(p.stat().st_mode & 0o777)==row["mode"], f"payload mode mismatch: {rel}")
    allowed=set(manifest["payloads"])|{"manifest.json","INSTALL-COMPLETE.json"}
    for p in root.rglob("*"):
        need(not p.is_symlink(), "unlisted symlink")
        if p.is_file():need(p.relative_to(root).as_posix() in allowed, "unlisted payload")
    return manifest


def require_installed(prefix):
    manifest=check_payloads(prefix)
    marker=Path(prefix)/"INSTALL-COMPLETE.json"
    need(marker.is_file() and not marker.is_symlink(), "installation is incomplete")
    need(json.loads(marker.read_text())["manifestSHA256"]==sha(Path(prefix)/"manifest.json"), "installation manifest changed")
    return manifest


def aggregate_descriptor(prefix):
    """Validate every shipped C field against the fixed client/native profile.

    The native ABI exposes readiness and key only; remaining dimensions are
    fixed acceptance parameters, not values reported by that ABI.
    """
    def unique_fields(pairs):
        result = {}
        for key, value in pairs:
            need(key not in result, "duplicate C descriptor field: " + key)
            result[key] = value
        return result

    descriptor = json.loads((Path(prefix) / "share/identity/c-native.json").read_text(),
                            object_pairs_hook=unique_fields)
    expected = {"format": 1, "backend": "c-native-v1", "version": PROFILE["version"],
                "key": AGGREGATE["key"], "owners": AGGREGATE["nMax"],
                "statementBytes": 6 + 198 * AGGREGATE["nMax"], "maxProofBytes": MAX_PROOF,
                "verifyGas": AGGREGATE["verifyGas"], "maxTxBytes": AGGREGATE["maxTxBytes"]}
    need(isinstance(descriptor, dict) and descriptor.keys() == expected.keys(), "C descriptor field set mismatch")
    for key, value in expected.items():
        need(type(descriptor[key]) is type(value) and descriptor[key] == value,
             "C descriptor field mismatch: " + key)
    return descriptor


def aggregate_genesis_config(descriptor):
    return {"key": descriptor["key"], "verifyGas": descriptor["verifyGas"],
            "nMax": descriptor["owners"], "maxTxBytes": descriptor["maxTxBytes"]}


def selfcheck(prefix, inputs=None):
    manifest=check_payloads(prefix)
    c_identity = aggregate_descriptor(prefix)
    lib=prefix/'lib/libpq_final_native.so'
    so=ctypes.CDLL(str(lib))
    so.pq_f_identity_v1.restype=ctypes.c_char_p
    so.pq_f_ready_v1.restype=ctypes.c_int32
    so.pq_f_verify_v1.argtypes=[ctypes.c_char_p,ctypes.c_size_t,ctypes.c_char_p,ctypes.c_size_t]
    so.pq_f_verify_v1.restype=ctypes.c_int32
    identity=json.loads(so.pq_f_identity_v1().decode())
    expected=json.loads((prefix/'share/identity/f-native.json').read_text())
    need(identity==expected and so.pq_f_ready_v1()==0,'F identity/key initialization')
    need(identity['algorithm_digest']==PROFILE['nativeAlgorithmDigest'] and identity['f_vk_digest']==PROFILE['finalKeyDigest']
         and identity['max_proof_bytes']==196608 and not identity['dev_mode'] and not identity['groth16'],'F profile identity')
    aggregate = ctypes.CDLL(str(prefix / 'lib/libpq_migrate_tree.so'))
    aggregate.pq_aggregate_key_v1.restype = ctypes.c_char_p
    aggregate.pq_aggregate_ready_v1.restype = ctypes.c_int32
    aggregate_key = aggregate.pq_aggregate_key_v1().decode()
    need(aggregate_key.removeprefix('0x') == c_identity['key'][2:]
         and aggregate.pq_aggregate_ready_v1() == 0, 'C identity/key initialization')
    outcomes = {}
    if inputs is not None:
        inputs = Path(inputs)
        proof = (inputs/'recovery/proof.postcard').read_bytes()
        pi = (inputs/'recovery/pi.bin').read_bytes()
        need(len(pi) == 198 and int.from_bytes(pi[:32], 'big') == PROFILE['chainId'], 'fixture chain/PI')
        need(pi[169] == 0 and int.from_bytes(pi[84:92], 'big') == 0, 'initial recovery mode/nonce')
        changed = bytearray(pi); changed[136] ^= 1
        cases = {'proof': (proof, pi, {0}), 'changed-pi': (proof, bytes(changed), {1,2}),
                 'truncated': (proof[:-1], pi, {1,2}), 'trailing': (proof+b'\0', pi, {1,2}),
                 'over-bound': (bytes(MAX_PROOF+1), pi, {1})}
        for name, (data, statement, expected) in cases.items():
            status = so.pq_f_verify_v1(data, len(data), statement, len(statement))
            outcomes[name] = status
            need(status in expected, f'F ABI {name}: {status}')
    r=subprocess.run([str(prefix/'bin/geth'),'version'],capture_output=True,text=True,cwd='/')
    need(r.returncode==0,'geth startup')
    return {'payloads':len(manifest['payloads']),'identity':identity,'aggregateKey':aggregate_key,'aggregateIdentity':c_identity,'abi':outcomes,'realProofChecked':inputs is not None,'gethVersion':r.stdout.splitlines()[:2]}


HEX_DIGITS = "0123456789abcdefABCDEF"


def genesis_uint64(value, what):
    """A genesis integer as geth's HexOrDecimal64 reads it: absent, null or "" is 0;
    otherwise a JSON integer, or a decimal or 0x-hexadecimal string, below 2**64."""
    if value is None or value == "":
        return 0
    n = -1
    if type(value) is int:
        n = value
    elif isinstance(value, str) and value[:2] in ("0x", "0X"):
        if value[2:] and all(ch in HEX_DIGITS for ch in value[2:]):
            n = int(value[2:], 16)
    elif isinstance(value, str) and value.isascii() and value.isdigit():
        n = int(value)
    need(0 <= n < 2**64, f"{what} = {value!r} is not a genesis integer")
    return n


def genesis_code(value, what):
    """Genesis code as geth's hexutil.Bytes reads it: absent, null or "" is no code;
    otherwise a 0x-prefixed string of whole bytes."""
    if value is None or value == "":
        return b""
    digits = value[2:] if isinstance(value, str) and value[:2] in ("0x", "0X") else None
    need(digits is not None and len(digits) % 2 == 0 and all(ch in HEX_DIGITS for ch in digits),
         f"{what} = {value!r} is not 0x-prefixed hex")
    return bytes.fromhex(digits)


def genesis_field(obj, name, where):
    """The value geth reads for the field name of a genesis JSON object, None when
    absent. geth's encoding/json matches a key to a field in any case, rune by rune,
    so a key is compared with name character by character under str.casefold():
    "Timestamp" is the timestamp, while a ligature such as U+FB06 (st) makes another
    key, which geth ignores. Two keys that fold to name are refused, since geth
    keeps whichever comes last."""
    keys = [key for key in obj
            if len(key) == len(name) and all(k.casefold() == n.casefold() for k, n in zip(key, name))]
    need(len(keys) <= 1, f"{where} spells {name} more than once: {', '.join(map(repr, keys))}")
    return obj[keys[0]] if keys else None


def check_genesis_images(genesis, c, p):
    """Mirror the client's start-up check S8 (spec section 24.6 rule 3) before any
    client starts. When T0 is at or before the genesis timestamp no block installs
    the code images, so the allocation must hold PQ_REGISTRY and FACT_REGISTRY each
    with code exactly 0x00 and nonce 1. As in the client, a configuration with the
    state bridge is not checked: the bridge installs the images at its InitBlock.
    The keys pqStateBridge, timestamp, alloc, code and nonce are read in any case,
    as geth reads them (genesis_field)."""
    s8 = "start-up check S8"
    if genesis_field(c, "pqStateBridge", s8 + ": the chain configuration") is not None:
        return
    t0 = p.get("t0")
    need(type(t0) is int and 0 <= t0 < 2**64, "pqMigrate.t0 must be an integer")
    timestamp = genesis_uint64(genesis_field(genesis, "timestamp", s8 + ": the genesis"), "genesis timestamp")
    if t0 > timestamp:
        return
    alloc = genesis_field(genesis, "alloc", s8 + ": the genesis")
    need(isinstance(alloc, dict), "the genesis allocation must be an object")
    for name, key in (("PQ_REGISTRY", "registry"), ("FACT_REGISTRY", "factRegistry")):
        address = p[key]
        where = f"{s8} (T0 {t0} <= genesis timestamp {timestamp}): {name} {address}"
        # geth reads an allocation key with or without 0x, in either case.
        found = [account for spelled, account in alloc.items()
                 if spelled.lower().removeprefix("0x") == address.lower().removeprefix("0x")]
        need(len(found) <= 1, where + " is listed more than once in the allocation")
        need(len(found) == 1, where + " is absent from the allocation; want code 0x00 and nonce 1")
        need(isinstance(found[0], dict), where + " is not an account object")
        code = genesis_code(genesis_field(found[0], "code", where), where + " code")
        need(code == b"\x00", where + f" holds {'code 0x' + code.hex() if code else 'no code'}; want exactly 0x00")
        nonce = genesis_uint64(genesis_field(found[0], "nonce", where), where + " nonce")
        need(nonce == 1, where + f" holds nonce {nonce}; want 1")


def preflight(prefix, genesis_path, inputs=None, *, research_window_seconds=None):
    require_installed(prefix)
    c_identity = aggregate_descriptor(prefix)
    genesis = json.loads(Path(genesis_path).read_text())
    c = genesis.get("config", {})
    need(c.get("chainId") != 13375, "chain id 13375 belongs to earlier lab profiles, not Lean lab")
    need(c.get("chainId") == PROFILE["chainId"], "chain id must be 13378 (Lean lab)")
    p = c.get("pqMigrate")
    need(isinstance(p, dict), "pqMigrate is required for Lean lab")
    f = p.get("fullResearch") or {}
    need(f.get("version") != 0x80000002, "verifier_version 0x80000002 belongs to earlier lab profiles, not Lean lab")
    need(f.get("nativeAlgorithmDigest") not in REFUSED_DIGESTS, f"the {REFUSED_DIGESTS.get(f.get('nativeAlgorithmDigest'))} is not Lean lab's identity")
    for key in ("version", "nativeAlgorithmDigest", "backend", "proofLifetime", "maxProofBytes", "maxTxBytes", "txGasCap", "verifyGas",
                "imageId", "guestSha", "verifierSha", "finalKeyDigest"):
        need(f.get(key) == PROFILE[key], f"fullResearch.{key} = {f.get(key)!r}, Lean lab fixes {PROFILE[key]!r}")
    if research_window_seconds is not None:
        need(type(research_window_seconds) is int and 12 <= research_window_seconds <= PROFILE['w']
             and research_window_seconds % PROFILE['poolSlotSeconds'] == 0,
             'research request-window override must be a positive slot multiple within the profile window')
    for key in ("w", "poolSlotSeconds", "maxPayloadBytes", "registry", "factRegistry", "legacySeedProofFromT0"):
        expected = research_window_seconds if key == 'w' and research_window_seconds is not None else PROFILE[key]
        need(p.get(key) == expected, f"pqMigrate.{key} = {p.get(key)!r}, expected {expected!r}")
    need(not p.get("factVerifiers"), "Lean lab enables no Route B version")
    aggregate = p.get("aggregateResearch")
    expected_aggregate = aggregate_genesis_config(c_identity)
    need(isinstance(aggregate, dict) and aggregate.keys() == expected_aggregate.keys()
         and all(type(aggregate[key]) is type(value) and aggregate[key] == value
                 for key, value in expected_aggregate.items()), "C descriptor/genesis aggregate profile mismatch")
    for descriptor_key, genesis_key in (("version", "version"), ("maxProofBytes", "maxProofBytes")):
        need(type(f.get(genesis_key)) is int and f[genesis_key] == c_identity[descriptor_key],
             "C descriptor/fullResearch mismatch: " + genesis_key)
    need(c.get("osakaTime") is not None and c["osakaTime"] <= p["t0"] == p["receivingTime"] < p["t"], "timing: Osaka <= T0 = receivingTime < T")
    need(f.get("activation", 2**64) <= p["t0"] < f.get("sunset", 0), "activation <= T0 < sunset")
    need(not any(k.startswith("bpo") or k in ("amsterdamTime", "ubtTime") for k in c), "no BPO, Amsterdam or UBT fork in Lean lab")
    check_genesis_images(genesis, c, p)
    need(inputs is not None, "runtime proof inputs are required")
    selfcheck(prefix, inputs)
    expiry=json.loads((Path(inputs)/"recovery/config.json").read_text())["fields"]["expiry"]
    need(p["t"] <= expiry <= p["t"]+f["proofLifetime"], "proof expiry outside this genesis recovery window")
    with tempfile.TemporaryDirectory(prefix="pq-lean-preflight-") as tmp:
        r = subprocess.run([str(prefix / "bin/geth"), "init", "--datadir", tmp, "--state.scheme=hash", str(genesis_path)],
                           capture_output=True, text=True, cwd="/")
        need(r.returncode == 0 and "Successfully wrote genesis state" in r.stderr, f"geth init refused the genesis: {r.stderr[-400:]}")
        h = [l for l in r.stderr.splitlines() if "Successfully wrote genesis state" in l][-1].split("hash=")[-1].strip()
    return {"chainId": c["chainId"], "T0": p["t0"], "T": p["t"], "W": p["w"],
            "researchWindowOverride": research_window_seconds is not None, "gethInitHash": h}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("command", choices=["install", "selfcheck", "preflight"])
    ap.add_argument("--package", type=Path)
    ap.add_argument("--prefix", required=True, type=Path)
    ap.add_argument("--genesis", type=Path)
    ap.add_argument("--inputs", type=Path)
    a = ap.parse_args()
    prefix = a.prefix.resolve()
    try:
        if a.command == "install":
            need(a.package is not None, "--package is required")
            need(not prefix.exists(), "the prefix exists; installation never overwrites")
            dist = a.package.resolve()
            manifest = check_payloads(dist)
            prefix.mkdir(parents=True)
            for rel, row in manifest["payloads"].items():
                (prefix / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(dist / rel, prefix / rel)
                os.chmod(prefix / rel, int(row["mode"], 8))
            shutil.copyfile(dist / "manifest.json", prefix / "manifest.json")
            report = selfcheck(prefix)
            (prefix / "INSTALL-COMPLETE.json").write_text(json.dumps({"manifestSHA256": sha(prefix / "manifest.json"),
                                                                      "selfcheck": report}, indent=1) + "\n")
        elif a.command == "selfcheck":
            report = selfcheck(prefix, a.inputs)
        else:
            need(a.genesis is not None, "--genesis is required")
            report = preflight(prefix, a.genesis, a.inputs)
        print(json.dumps({"status": "OK", "command": a.command, "report": report}))
    except (Refused, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({"status": "REFUSED", "command": a.command, "reason": str(error)}))
        sys.exit(2)


if __name__ == "__main__":
    main()
