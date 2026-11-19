"""N1 checkpoint tool (design note section 3.4): from the finalized EL chain at B_ck to the Lean genesis at S.

  checkpoint.py run    --profile P.json --snapshot S.json --genesis G.json --expect-genesis-sha256 HASH
                       --bck 0xHASH --rpc URL --rpc URL --out NEWDIR
                       [--labels LABELS.json] [--tool3 PATH/profile-tool-three]
  checkpoint.py layout --checkpoint DIR --expect-manifest-sha256 HASH --keystore H=DIR
                       --binding H:0=KEY_DIRECTORY [--binding H:1=OTHER_DIRECTORY] --out NEWDIR

Step 1  On every node: B_ck is known, canonical, exactly the halted 'finalized' marker, timestamp < D_reg; same stateRoot on all.
Step 2  Completeness: the registry code and D_reg at B_ck are the profile's; every Registered log in blocks <= B_ck is
        replayed into acc = keccak(acc || keccak(payload)) and count, which must equal storage slots 1 and 2 at B_ck;
        logs are identical on all nodes. Any failure in steps 1-2 refuses the whole checkpoint (REFUSED.json, exit 2).
Step 3  Each registration is checked in this order (the first failure is its reason; every failure is listed):
        chain-id, scheme-id, unknown-index, bls-pubkey-mismatch, bls-invalid, lean-key-noncanonical, lean-interval,
        withdrawal-credentials (0x00 excluded, rule 6 (a)). A failing registration is reported and ignored.
Step 4  Valid registrations grouped by index: one distinct (attestation, proposal) key tuple = included; two or more =
        excluded for conflict (late path); none = missed (or excluded for its 0x00 credential).
Outputs (one new directory): lean-validators.json (Lean index = rank in beacon-index order), lean-network.yaml,
pub/<lean>-v<beacon>/{attestation,proposal}.pub, cl-genesis.json (profile-tool-three), anchor.json (B_ck and the
network identity), registrations.json, exclusions.json, stake-report.json, checkpoint.json, MANIFEST.json (SHA-256 of
every file; the digest fixed out of band). The stake report judges rule 3 (c) on the Lean set at S (author 2026-11-02);
the beacon-stake fractions are information only. A's keys are known only through lab labels.
research lab; not production validation.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from fractions import Fraction
from pathlib import Path, PurePosixPath

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import n1lib as L  # noqa: E402
from rules import resolve_registrations

TOOL3 = "profile-tool-three"
RULE3C_LABEL = "rule 3 (c), Lean set at S"
CHECK_ORDER = ["length", "chain-id", "scheme-id", "unknown-index", "bls-pubkey-mismatch", "bls-invalid",
               "lean-key-noncanonical", "lean-interval", "withdrawal-credentials"]


class Refused(Exception):
    def __init__(self, reason, **details):
        super().__init__(reason)
        self.reason, self.details = reason, details


def h2b(x):
    return bytes.fromhex(x[2:] if x.startswith("0x") else x)


def validate_profile_snapshot(profile, snapshot):
    if "T0" not in profile:
        raise Refused("missing-explicit-t0")
    if any(type(profile.get(field)) is not int for field in ("S", "dReg", "T0")) or \
            profile["S"] != profile["dReg"] or profile["T0"] != profile["S"]:
        raise Refused("timing-requires-S-T0-Dreg-equality")
    validators = snapshot.get("validators", [])
    if not validators or len({v["index"] for v in validators}) != len(validators):
        raise Refused("invalid-validator-snapshot")
    root = "0x" + L.validators_list_root(validators).hex()
    if root != snapshot.get("genesisValidatorsRoot") or root != profile.get("genesisValidatorsRoot"):
        raise Refused("snapshot-root-mismatch")
    if snapshot.get("genesisForkVersion") != profile.get("genesisForkVersion"):
        raise Refused("snapshot-fork-version-mismatch")


def validate_genesis_binding(profile, path, expected):
    """Bind the profile's fork time to the exact operator-pinned EL genesis."""
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if not expected or digest != expected.lower():
        raise Refused("genesis-digest-mismatch")
    genesis = json.loads(raw)
    config = genesis.get("config", {})
    t0 = config.get("pqMigrate", {}).get("t0")
    if type(t0) is not int or t0 != profile.get("T0"):
        raise Refused("t0-genesis-mismatch")
    if config.get("chainId") != profile.get("elChainId"):
        raise Refused("chain-id-genesis-mismatch")
    return digest


def verify_manifest(directory, expected):
    manifest = directory / "MANIFEST.json"
    if not expected or L.file_sha256(manifest) != expected.lower():
        raise Refused("checkpoint-manifest-digest-mismatch")
    files = json.loads(manifest.read_text())
    for name, digest in files.items():
        rel = PurePosixPath(name)
        if not name or rel.is_absolute() or ".." in rel.parts or "\\" in name or str(rel) != name:
            raise Refused("unsafe-checkpoint-path")
        path = directory / name
        parents = [directory.joinpath(*rel.parts[:i]) for i in range(1, len(rel.parts) + 1)]
        if any(p.is_symlink() for p in parents):
            raise Refused("checkpoint-symlink")
        if not path.resolve().is_relative_to(directory.resolve()) or L.file_sha256(path) != digest:
            raise Refused("checkpoint-file-digest-mismatch", file=name)
    actual = {p.relative_to(directory).as_posix() for p in directory.rglob("*") if p.is_file()}
    if actual != set(files) | {"MANIFEST.json"}:
        raise Refused("checkpoint-file-inventory-mismatch")


# ---------------------------------------------------------------- step 1
def step1(profile, bck, urls):
    seen = []
    for k, url in enumerate(urls):
        b = L.rpc(url, "eth_getBlockByHash", [bck, False])
        if b is None:
            raise Refused("bck-unknown", node=k, url=url)
        num = int(b["number"], 16)
        canon = L.rpc(url, "eth_getBlockByNumber", [hex(num), False])
        if canon is None or canon["hash"] != bck:
            raise Refused("bck-not-canonical", node=k, canonicalAtHeight=canon and canon["hash"], number=num)
        fin = L.rpc(url, "eth_getBlockByNumber", ["finalized", False])
        if fin is None or int(fin["number"], 16) < num:
            raise Refused("bck-not-finalized", node=k, finalized=fin and {"number": int(fin["number"], 16), "hash": fin["hash"]},
                          number=num)
        if int(fin["number"], 16) != num or fin["hash"] != bck:
            raise Refused("bck-not-last-finalized", node=k, number=num,
                          finalized={"number": int(fin["number"], 16), "hash": fin["hash"]})
        ts = int(b["timestamp"], 16)
        if ts >= profile["dReg"]:
            raise Refused("bck-at-or-after-dreg", node=k, timestamp=ts, dReg=profile["dReg"])
        seen.append({"node": k, "url": url, "number": num, "hash": b["hash"], "stateRoot": b["stateRoot"], "timestamp": ts,
                     "finalized": {"number": int(fin["number"], 16), "hash": fin["hash"]}})
    if len({s["stateRoot"] for s in seen}) != 1 or len({s["number"] for s in seen}) != 1:
        raise Refused("bck-mismatch-between-nodes", nodes=seen)
    return seen


# ---------------------------------------------------------------- step 2
def decode_log(log):
    data = h2b(log["data"])
    if len(data) < 96 or int.from_bytes(data[32:64], "big") != 64:
        raise Refused("log-malformed", log=log)
    n = int.from_bytes(data[64:96], "big")
    payload = data[96:96 + n]
    pad = data[96 + n:]
    if len(payload) != n or len(data) != 96 + (n + 31) // 32 * 32 or any(pad):
        raise Refused("log-malformed", log=log)
    return {"seq": int(log["topics"][1], 16), "index": int(log["topics"][2], 16), "accAfter": data[:32], "payload": payload,
            "blockNumber": int(log["blockNumber"], 16), "blockHash": log["blockHash"], "logIndex": int(log["logIndex"], 16),
            "txHash": log["transactionHash"]}


def step2(profile, bck_num, bck, urls):
    reg = profile["registry"]
    per_node, storage = [], []
    for k, url in enumerate(urls):
        code = h2b(L.rpc(url, "eth_getCode", [reg, {"blockHash": bck}]))
        if "0x" + L.keccak(code).hex() != profile["registryRuntimeKeccak"]:
            raise Refused("registry-code-mismatch", node=k, codeKeccak="0x" + L.keccak(code).hex())
        slots = [int(L.rpc(url, "eth_getStorageAt", [reg, hex(s), {"blockHash": bck}]), 16) for s in (0, 1, 2)]
        if slots[0] != profile["dReg"]:
            raise Refused("registry-dreg-mismatch", node=k, slot0=slots[0], dReg=profile["dReg"])
        logs = L.rpc(url, "eth_getLogs", [{"fromBlock": "0x0", "toBlock": hex(bck_num), "address": reg}])
        for lg in logs:
            if lg.get("removed") or lg["topics"][:1] != [L.REGISTERED_TOPIC] or len(lg["topics"]) != 3 \
                    or lg["address"].lower() != reg.lower() or int(lg["blockNumber"], 16) > bck_num:
                raise Refused("log-malformed", node=k, log=lg)
        logs.sort(key=lambda lg: (int(lg["blockNumber"], 16), int(lg["logIndex"], 16)))
        per_node.append(logs)
        storage.append(slots)
    canon_logs = [[(lg["blockHash"], lg["logIndex"], lg["transactionHash"], tuple(lg["topics"]), lg["data"]) for lg in logs]
                  for logs in per_node]
    if any(c != canon_logs[0] for c in canon_logs[1:]) or any(s != storage[0] for s in storage[1:]):
        raise Refused("logs-or-storage-differ-between-nodes", counts=[len(c) for c in canon_logs], storage=storage)
    entries = [decode_log(lg) for lg in per_node[0]]
    for e in entries:   # every log block is canonical on every node (logs of an orphaned block are not counted)
        for url in urls:
            if L.rpc(url, "eth_getBlockByNumber", [hex(e["blockNumber"]), False])["hash"] != e["blockHash"]:
                raise Refused("log-block-not-canonical", entry=e["seq"])
    acc, failures = L.ZERO32, []
    for k, e in enumerate(entries):
        acc = L.keccak(acc + L.keccak(e["payload"]))
        if e["seq"] != k or e["accAfter"] != acc:
            failures.append({"check": "log-sequence", "position": k, "seq": e["seq"]})
        if len(e["payload"]) >= 16 and e["index"] != int.from_bytes(e["payload"][8:16], "little"):
            failures.append({"check": "log-index-topic", "position": k})
    s_acc, s_count = storage[0][1].to_bytes(32, "big"), storage[0][2]
    head = []
    if acc != s_acc:
        head.append({"check": "accumulator-mismatch", "replayed": "0x" + acc.hex(), "storage": "0x" + s_acc.hex()})
    if len(entries) != s_count:
        head.append({"check": "count-mismatch", "logs": len(entries), "storage": s_count})
    failures = head + failures
    if failures:
        raise Refused(failures[0]["check"], failures=failures)
    return entries, {"acc": "0x" + acc.hex(), "count": s_count, "dReg": storage[0][0], "logs": len(entries)}


# ---------------------------------------------------------------- step 3
def validate(m, sig, profile, snap, domain):
    reasons = []
    if m["el_chain_id"] != profile["elChainId"]:
        reasons.append("chain-id")
    if m["lean_scheme_id"] != h2b(profile["leanSchemeId"]):
        reasons.append("scheme-id")
    v = snap.get(m["validator_index"])
    if v is None:
        reasons.append("unknown-index")
    elif m["bls_pubkey"] != h2b(v["pubkey"]):
        reasons.append("bls-pubkey-mismatch")
    elif not L.bls_verify(m["bls_pubkey"], L.signing_root(L.message_root(m), domain), sig):
        reasons.append("bls-invalid")
    problems = {r: L.lean_key_problems(m[f]) for r, f in (("attestation", "lean_attestation_pubkey"),
                                                          ("proposal", "lean_proposal_pubkey"))}
    if any(problems.values()):
        reasons.append("lean-key-noncanonical")
    act, n = m["activation_epoch"], m["num_active_epochs"]
    if not (act == 0 and n >= profile["leanHorizon"] and act + n <= 2**32):
        reasons.append("lean-interval")
    if v is not None and h2b(v["withdrawalCredentials"])[0] not in (1, 2):
        reasons.append("withdrawal-credentials")
    return reasons, {r: p for r, p in problems.items() if p}


# ---------------------------------------------------------------- run
def run(a):
    profile = json.loads(a.profile.read_text())
    snapshot = json.loads(a.snapshot.read_text())
    labels = json.loads(a.labels.read_text()) if a.labels else None
    out = a.out
    out.mkdir(parents=True)
    rec = {"review": "research lab; not production validation", "tool": "n1-checkpoint",
           "inputs": {"profileSHA256": L.file_sha256(a.profile), "snapshotSHA256": L.file_sha256(a.snapshot),
                      "labelsSHA256": L.file_sha256(a.labels) if a.labels else None, "bck": a.bck, "rpc": a.rpc}}
    try:
        res = _run(profile, snapshot, labels, a, out, rec)
    except Refused as r:
        refusal = {"status": "REFUSED", "reason": r.reason, "details": r.details, **rec}
        (out / "REFUSED.json").write_text(json.dumps(refusal, indent=1, default=str) + "\n")
        print(json.dumps({"status": "REFUSED", "reason": r.reason}))
        return 2
    print(json.dumps(res))
    return 0


def _run(profile, snapshot, labels, a, out, rec):
    bck = a.bck.lower()
    urls = a.rpc
    if len(urls) < 2 or len(set(urls)) < 2:
        raise Refused("two-distinct-rpc-endpoints-required")
    validate_profile_snapshot(profile, snapshot)
    rec["inputs"]["elGenesisSHA256"] = validate_genesis_binding(profile, a.genesis, a.expect_genesis_sha256)
    domain = L.compute_domain(h2b(profile["domainType"]), h2b(profile["genesisForkVersion"]),
                              h2b(profile["genesisValidatorsRoot"]))
    snap = {v["index"]: v for v in snapshot["validators"]}
    assert len(snap) == len(snapshot["validators"]), "duplicate snapshot index"
    nodes = step1(profile, bck, urls)
    bck_num = nodes[0]["number"]
    entries, registry_state = step2(profile, bck_num, bck, urls)
    again = step1(profile, bck, urls)                      # B_ck still canonical and finalized after the reads
    if [n["hash"] for n in again] != [n["hash"] for n in nodes]:
        raise Refused("bck-changed-during-read")

    # step 3
    regs = []
    for e in entries:
        try:
            m, sig = L.decode_payload(e["payload"])
        except ValueError:
            regs.append({"seq": e["seq"], "block": e["blockNumber"], "tx": e["txHash"], "valid": False, "reason": "length",
                         "reasons": ["length"]})
            continue
        reasons, problems = validate(m, sig, profile, snap, domain)
        r = {"seq": e["seq"], "block": e["blockNumber"], "tx": e["txHash"], "index": m["validator_index"],
             "message": L.message_json(m), "signature": "0x" + sig.hex(), "valid": not reasons,
             "reason": reasons[0] if reasons else None, "reasons": reasons, "payloadSHA256": hashlib.sha256(e["payload"]).hexdigest()}
        if problems:
            r["leanKeyProblems"] = problems
        regs.append(r)

    # Conflict exclusion is independent of registration order and uses only valid tuples.
    results, lean, unknown = resolve_registrations(snap, regs)
    if not lean:
        raise Refused("empty-lean-set")

    lean_set = []
    for k, item in enumerate(lean):
        v = snap[item["index"]]
        lean_set.append({"leanIndex": k, "beaconIndex": item["index"], "attestation": item["attestation"],
                         "proposal": item["proposal"], "blsPubkey": v["pubkey"], "effectiveBalanceGwei": v["effectiveBalanceGwei"],
                         "registrationSeqs": item["valid"]})
    seen = {}
    for x in lean_set:
        for role in ("attestation", "proposal"):
            seen.setdefault(x[role], []).append({"beaconIndex": x["beaconIndex"], "role": role})
    duplicates = [{"key": k, "holders": v} for k, v in seen.items() if len(v) > 1]

    # outputs: pub dirs, CL root, YAML, anchor
    pubdirs = []
    for x in lean_set:
        d = out / "pub" / ("%02d-v%d" % (x["leanIndex"], x["beaconIndex"]))
        d.mkdir(parents=True)
        (d / "attestation.pub").write_bytes(h2b(x["attestation"]))
        (d / "proposal.pub").write_bytes(h2b(x["proposal"]))
        pubdirs.append(d)
    tool3 = shutil.which(a.tool3 or TOOL3)
    if tool3 is None:
        raise Refused("cl-genesis-tool-unavailable")
    argv = [str(tool3), "genesis", str(pubdirs[0]), str(profile["S"])] + [str(d) for d in pubdirs[1:]]
    q = subprocess.run(argv, capture_output=True, text=True, timeout=300)
    if q.returncode != 0:
        raise Refused("cl-genesis-failed", stderr=q.stderr[-500:])
    cl = json.loads(q.stdout.strip().splitlines()[-1])
    assert cl["genesisTime"] == profile["S"]
    (out / "cl-genesis.json").write_text(json.dumps({**cl, "tool": Path(tool3).name, "toolSHA256": _tool_sha(tool3),
                                                    "argv": ["genesis", "pub/<lean 0>", str(profile["S"]), "pub/<lean 1..>"]},
                                                   indent=1) + "\n")
    net = {"GENESIS_TIME": profile["S"], "NUM_VALIDATORS": len(lean_set),
           "GENESIS_VALIDATORS": [{"attestation_public_key": x["attestation"], "proposal_public_key": x["proposal"]} for x in lean_set],
           "SECONDS_PER_SLOT": profile["secondsPerSlot"], "JUSTIFICATION_LOOKBACK_SLOTS": profile["justificationLookbackSlots"]}
    (out / "lean-network.yaml").write_text(json.dumps(net, indent=2) + "\n")
    b0 = nodes[0]
    identity = hashlib.sha256(b"PQ-LEAN-FENCED-v1" + profile["elChainId"].to_bytes(8, "big") + h2b(cl["clRoot"]) +
                              h2b(b0["hash"]) + h2b(b0["stateRoot"])).hexdigest()
    anchor = {"bck": {"hash": b0["hash"], "stateRoot": b0["stateRoot"], "number": b0["number"], "timestamp": b0["timestamp"]},
              "nodes": nodes, "anchorClRoot": cl["clRoot"], "networkIdentity": "0x" + identity,
              "engineAnchor": {"anchor_cl_root": cl["clRoot"], "anchor_el_hash": b0["hash"], "anchor_state_root": b0["stateRoot"]},
              "registryAtBck": registry_state, "dReg": profile["dReg"], "S": profile["S"]}
    (out / "anchor.json").write_text(json.dumps(anchor, indent=1) + "\n")
    (out / "lean-validators.json").write_text(json.dumps({"leanSet": lean_set, "duplicateKeysAcrossIndices": duplicates,
                                                          "mapping": [[x["leanIndex"], x["beaconIndex"]] for x in lean_set]},
                                                         indent=1) + "\n")
    (out / "registrations.json").write_text(json.dumps({"registrations": regs, "unknownIndexSeqs": unknown}, indent=1) + "\n")
    excl = [r for r in results if r["result"] == "excluded"]
    (out / "exclusions.json").write_text(json.dumps({"excluded": excl, "invalidRegistrations": [
        {"seq": r["seq"], "index": r.get("index"), "reason": r["reason"], "reasons": r["reasons"]} for r in regs if not r["valid"]]},
        indent=1) + "\n")
    stake = stake_report(snap, lean_set, regs, labels)
    (out / "stake-report.json").write_text(json.dumps(stake, indent=1) + "\n")
    summary = {"status": "CHECKPOINT", "review": rec["review"], "inputs": rec["inputs"], "profile": profile,
               "domain": "0x" + domain.hex(), "bck": anchor["bck"], "clRoot": cl["clRoot"], "networkIdentity": "0x" + identity,
               "registryAtBck": registry_state, "results": results,
               "leanSet": [[x["leanIndex"], x["beaconIndex"]] for x in lean_set], "duplicates": duplicates,
               "rule3c": stake["rule3c"]}
    (out / "checkpoint.json").write_text(json.dumps(summary, indent=1) + "\n")
    files = sorted(p for p in out.rglob("*") if p.is_file() and p.name != "MANIFEST.json")
    manifest = {str(p.relative_to(out)).replace("\\", "/"): L.file_sha256(p) for p in files}
    (out / "MANIFEST.json").write_text(json.dumps(manifest, indent=1, sort_keys=True) + "\n")
    return {"status": "CHECKPOINT", "leanSet": summary["leanSet"], "excluded": {r["index"]: r["reason"] for r in excl},
            "clRoot": cl["clRoot"], "manifestSHA256": L.file_sha256(out / "MANIFEST.json"), "rule3c": stake["rule3c"]["verdict"]}


def _tool_sha(p):
    p = Path(p)
    real = p.parent.parent / "libexec" / p.name
    return L.file_sha256(real if real.exists() else p)


def frac(f):
    return {"fraction": "%d/%d" % (f.numerator, f.denominator), "decimal": round(float(f), 6)}


def stake_report(snap, lean_set, regs, labels):
    total = sum(v["effectiveBalanceGwei"] for v in snap.values())
    included = [x["beaconIndex"] for x in lean_set]
    inc_stake = sum(snap[i]["effectiveBalanceGwei"] for i in included)
    rep = {"note": "Lean counts validators (equal weight); beacon stake is balance-weighted (design note R5). Every lab "
                   "validator has 32 ETH.",
           "leanSet": {"validators": len(lean_set), "beaconIndices": included},
           "beaconStake": {"label": "information only (beacon stake of the snapshot)", "totalGwei": total,
                           "includedGwei": inc_stake, "included": frac(Fraction(inc_stake, total))}}
    if not labels:
        rep["rule3c"] = {"label": RULE3C_LABEL, "verdict": "not computable: the tool cannot know which keys A holds "
                                                          "(supply lab labels)"}
        return rep
    akeys = {k.lower() for k in labels["attacker"]["leanKeys"]}
    a_inc = [x["beaconIndex"] for x in lean_set if x["attestation"].lower() in akeys or x["proposal"].lower() in akeys]
    n, k = len(lean_set), len(a_inc)
    f = Fraction(k, n)
    rep["rule3c"] = {"label": RULE3C_LABEL, "fA": frac(f), "aControlledIncluded": a_inc, "leanSetSize": n, "bound": "1/3",
                     "verdict": ("within bound: f_A < 1/3" if 3 * k < n else "bound exceeded: f_A >= 1/3")}
    forged = sorted({r["index"] for r in regs if r["valid"] and (r["message"]["lean_attestation_pubkey"].lower() in akeys or
                                                                 r["message"]["lean_proposal_pubkey"].lower() in akeys)})
    broken = sorted(labels["attacker"].get("brokenIndices", []))
    st = lambda idx: sum(snap[i]["effectiveBalanceGwei"] for i in idx if i in snap)  # noqa: E731
    rep["beaconStake"].update(aControlledIncluded=frac(Fraction(st(a_inc), total)), aValidForgedIndices=forged,
                              aValidForged=frac(Fraction(st(forged), total)), aBrokenIndices=broken,
                              aBroken=frac(Fraction(st(broken), total)))
    rep["labels"] = "lab-only: A's keys and broken indices are supplied by the harness; the tool cannot know them"
    return rep


# ---------------------------------------------------------------- layout
def layout_plan(lean, keystores, bindings):
    """Validate every checkpoint/directory/index binding without writing files."""
    by_index, by_tuple = {}, {}
    for entry in lean:
        index = entry["leanIndex"]
        if type(index) is not int or index < 0 or index in by_index:
            raise Refused("invalid-lean-index")
        pubs = tuple(h2b(entry[role]) for role in ("attestation", "proposal"))
        by_index[index] = entry
        by_tuple.setdefault(pubs, []).append(index)
    # A registration can copy an honest tuple without possessing either private
    # key. Never infer ownership from matching public bytes, and never refuse
    # because of a copy: refusing would let A block every node's provisioning
    # with one copied registration (fix list F-04). The operator binds its own
    # index explicitly below; a copier's index stays unbound, that is offline,
    # since nobody holds its private keys. It is reported in the summary.
    shared = [sorted(indices) for indices in by_tuple.values() if len(indices) > 1]

    stores = {}
    for value in keystores:
        node, separator, directory = value.partition("=")
        if not separator or not directory or not re.fullmatch(r"[A-Za-z0-9_-]+", node):
            raise Refused("invalid-keystore-binding")
        if node in stores:
            raise Refused("duplicate-keystore-node", node=node)
        stores[node] = (Path(directory) / "hash-sig-keys").resolve(strict=True)
    if not bindings:
        raise Refused("explicit-key-index-bindings-required")

    registry = {node: [] for node in stores}
    bound_indices, bound_directories, bound_tuples = set(), set(), {}
    for value in bindings:
        owner, separator, relative = value.partition("=")
        node, colon, raw_index = owner.rpartition(":")
        if not separator or not colon or node not in stores or not re.fullmatch(r"[0-9]+", raw_index):
            raise Refused("invalid-key-index-binding")
        index = int(raw_index)
        if index not in by_index:
            raise Refused("binding-index-not-in-checkpoint", index=index)
        if index in bound_indices:
            raise Refused("duplicate-key-index-binding", index=index)
        rel = PurePosixPath(relative)
        if not relative or rel.is_absolute() or ".." in rel.parts or "\\" in relative or str(rel) != relative:
            raise Refused("unsafe-key-directory")
        directory = stores[node].joinpath(*rel.parts).resolve(strict=True)
        if not directory.is_dir() or not directory.is_relative_to(stores[node]):
            raise Refused("key-directory-outside-keystore")
        if directory in bound_directories:
            raise Refused("key-directory-bound-more-than-once")
        pubs = tuple((directory / (role + ".pub")).read_bytes() for role in ("attestation", "proposal"))
        expected = tuple(h2b(by_index[index][role]) for role in ("attestation", "proposal"))
        if pubs != expected:
            raise Refused("key-tuple-does-not-match-operator-index", node=node, index=index)
        if pubs in bound_tuples:
            # One leanXMSS tuple signing for two indices would reuse its
            # one-time keys, whichever directories hold the copies.
            raise Refused("key-tuple-bound-twice", index=index, other=bound_tuples[pubs])
        bound_tuples[pubs] = index
        for role in ("attestation", "proposal"):
            if not (directory / (role + ".ssz")).is_file():
                raise Refused("private-key-file-missing", node=node, index=index, role=role)
            registry[node].append({"index": index, "pubkey_hex": "0x" + h2b(by_index[index][role]).hex(),
                                   "privkey_file": (rel / (role + ".ssz")).as_posix()})
        bound_indices.add(index)
        bound_directories.add(directory)
    for entries in registry.values():
        entries.sort(key=lambda entry: entry["index"])
    summary = {"nodes": {node: sorted({entry["index"] for entry in entries}) for node, entries in registry.items()},
               "unheldLeanIndices": sorted(set(by_index) - bound_indices),
               "sharedKeyTuples": [{"leanIndices": indices, "boundIndices": [i for i in indices if i in bound_indices]}
                                   for indices in shared],
               "note": "copy registry-<node>.yaml to <store>/registry.yaml; provision signing history before starting Ream"}
    return registry, summary


def layout(a):
    """Create registries only after checking all explicit operator index bindings.

    --keystore NODE=STORE locates STORE/hash-sig-keys; --binding NODE:INDEX=DIR
    assigns that relative key directory to the operator's intended Lean index.
    """
    verify_manifest(a.checkpoint, a.expect_manifest_sha256)
    lean = json.loads((a.checkpoint / "lean-validators.json").read_text())["leanSet"]
    try:
        registry, summary = layout_plan(lean, a.keystore, a.binding)
    except Refused as refusal:
        raise SystemExit(str(refusal)) from refusal
    # Every refusal above happens before the output directory or any registry
    # exists. An existing output is never overwritten, including on retry.
    a.out.mkdir(parents=True)
    for node, entries in registry.items():
        (a.out / ("registry-%s.yaml" % node)).write_text(json.dumps({node: entries}, indent=1) + "\n")
    (a.out / "layout.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps(summary))
    return 0


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--profile", type=Path, required=True)
    r.add_argument("--snapshot", type=Path, required=True)
    r.add_argument("--genesis", type=Path, required=True)
    r.add_argument("--expect-genesis-sha256", required=True)
    r.add_argument("--bck", required=True)
    r.add_argument("--rpc", action="append", required=True)
    r.add_argument("--out", type=Path, required=True)
    r.add_argument("--labels", type=Path)
    r.add_argument("--tool3")
    y = sub.add_parser("layout")
    y.add_argument("--checkpoint", type=Path, required=True)
    y.add_argument("--expect-manifest-sha256", required=True)
    y.add_argument("--keystore", action="append", required=True, metavar="NODE=STORE")
    y.add_argument("--binding", action="append", required=True, metavar="NODE:LEAN_INDEX=KEY_DIRECTORY")
    y.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    raise SystemExit(run(a) if a.cmd == "run" else layout(a))


if __name__ == "__main__":
    main()
