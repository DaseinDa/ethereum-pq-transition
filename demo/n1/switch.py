"""N1 two-phase checkpoint lab. The same two geth processes retain execution state across the switch.

Phase 0 is a trusted-consensus stand-in using three disposable Lean validators; it is not a BLS beacon client.
BLS-authorized registration chooses seven of ten synthetic validators; conflicting tuples are excluded.
S = T0 = D_reg. Phase 0 halts before that common deadline, leaving time for checkpointing and provisioning.
T6b stops X and checks six-of-seven finality. Optional T8 loads a current public-test package recovery proof;
no proof is generated and no CL withdrawal, re-stake or new-membership transition is claimed."""
import argparse
import hashlib
import json
import math
import os
import shutil
import signal
import subprocess
import sys
import time
import traceback
from pathlib import Path
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
PART1 = HERE
sys.path.insert(0, str(PART1))
import n1lib as L  # noqa: E402
import labnet  # noqa: E402
import register  # noqa: E402
import scenario  # noqa: E402
from build_registry import genesis_entry, runtime_hex  # noqa: E402
from rules import switch_timeline, execution_invariants
from checkpoint import verify_manifest
from proof_input import read_public_recovery, installed_verifier_binding, verify_native

CHAIN = 13378
SLOT = labnet.SLOT
HX = ("H", "X")
WRC = "0x00000961ef480eb55e80d19ad83579a64c007002"     # EIP-7002 withdrawal request contract
OWNER = L.FIXTURE_OWNER
SENDERS = {"H": 40, "A": 41, "late": 42, "afterS": 43}
REVIEW = "research lab; not production validation"
EXPECTED_EXCLUDED = {"7": "conflict", "8": "conflict", "9": "withdrawal-credentials-0x00"}
EXPECTED_LEAN = [[i, i] for i in range(7)]

# Registration groups (one block each; the next group is sent only after every receipt of the previous one is seen on
# both nodes). (name, beacon index, key label, interop signer, sender, kind). A5x and A9x are signed by A with
# interop key 6 for another index (invalid signature). H9 is index 9's owner on time: a valid signature over a 0x00
# credential (T9); its second call comes after D_reg and reverts.
GROUPS = {
    1: [("H0", 0, "H0", 0, "H", "valid"), ("H1", 1, "H1", 1, "H", "valid"), ("H2", 2, "H2", 2, "H", "valid")],
    2: [("H3", 3, "H3", 3, "H", "valid"), ("H4", 4, "H4", 4, "H", "valid"), ("H5", 5, "H5", 5, "H", "valid"),
        ("H5-again", 5, "H5", 5, "H", "valid, same tuple again"), ("A5x", 5, "A5x", 6, "A", "invalid signature")],
    3: [("A6", 6, "A6", 6, "A", "valid; the owner of 6 misses B_ck"), ("A7", 7, "A7", 7, "A", "valid; A first"),
        ("malformed", None, None, None, "A", "311 bytes: 'N1: length'")],
    4: [("H7", 7, "H7", 7, "H", "valid; then the owner"), ("H8", 8, "H8", 8, "H", "valid; the owner first")],
    5: [("A8", 8, "A8", 8, "A", "valid; then A"), ("A9x", 9, "A9x", 6, "A", "invalid signature"),
        ("H9", 9, "H9", 9, "H", "valid signature, 0x00 credential (T9)")],
}
TAIL = ("H6-tail", 6, "H6", 6, "H", "the owner of 6 in the last slot before D_reg: after B_ck, dropped")
LATE = ("H9-after-Dreg", 9, "H9", 9, "late", "index 9's owner again after D_reg: reverts")
AFTER_S = ("H6-after-S", 6, "H6", 6, "afterS", "the owner of 6 after S: reverts (T2)")
HONEST_KEYS = ["H%d" % i for i in range(10)]
ATTACKER_KEYS = ["A5x", "A6", "A7", "A8", "A9x"]
PHASE1_KEYS = ["H0", "H1", "H2", "H3", "H4", "H5", "A6"]


class Abort(Exception):
    """Stop before the phase-1 histories are provisioned: the leanXMSS keys stay untouched."""


def blk(b):
    if b is None:
        return None
    return {"number": int(b["number"], 16), "hash": b["hash"], "parentHash": b["parentHash"], "stateRoot": b["stateRoot"],
            "timestamp": int(b["timestamp"], 16)}


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def bitlist_indices(h):
    b = bytes.fromhex(h[2:] if h.startswith("0x") else h)
    if not b or b[-1] == 0:
        return None
    n = (len(b) - 1) * 8 + b[-1].bit_length() - 1
    return [i for i in range(n) if b[i // 8] >> (i % 8) & 1]


def canonical_random_key():
    return b"".join((int.from_bytes(os.urandom(4), "little") % L.KOALABEAR_P).to_bytes(4, "little") for _ in range(13))


class Lab2(labnet.Lab):
    """labnet.Lab with two changes (copies of prepare_ream and start_ream): the libp2p identity tool is given an explicit
    public-key directory (labnet derives it from the registry's privkey_file, which is relative in the layout's
    registry), and Ream's worker thread counts are a parameter (labnet: 2)."""
    ream_threads = 2

    def prepare_ream2(self, name, round_, *, network_yaml, registry_yaml, cl_root, anchor, signer_cfg, peer, peer_keydir):
        n = self.nodes[name]
        d = n["dir"]
        n["p2p"], n["rest"] = labnet.free_port(True), labnet.free_port()
        key = d / f"node-key-{round_}"
        n["peerid"] = self.command(f"{name}-network-identity-{round_}", [self.bin("profile-tool"), "peer", peer_keydir, key])
        (d / f"session-{round_}").write_bytes(os.urandom(32))
        (d / f"session-{round_}").chmod(0o600)
        other = self.nodes[peer]
        n["cfg"] = {"profile": "pq-lean-fenced-v1", "engine_url": n["engineUrl"] + "/", "rpc_url": n["url"] + "/",
                    "jwt_path": str(d / "jwt"), "session_path": str(d / f"session-{round_}"),
                    "materials_directory": str(n["materials"]), "material_peers": [f"http://127.0.0.1:{other['material']}/"],
                    "chain_id": CHAIN, "anchor_cl_root": cl_root, "anchor_el_hash": anchor["hash"],
                    "anchor_state_root": anchor["stateRoot"], "timeout_seconds": 10, "exclusive_unsigned_instance": False}
        (d / f"engine-{round_}.json").write_text(json.dumps(n["cfg"], indent=2))
        (d / f"signer-{round_}.json").write_text(json.dumps(signer_cfg))
        n["reamargs"] = [self.bin("ream"), "--data-dir", d / f"cl-{round_}", "lean_node", "--network", network_yaml,
                         "--validator-registry-path", registry_yaml, "--node-id", name, "--private-key-path", key,
                         "--socket-address", "127.0.0.1", "--socket-port", str(n["p2p"]), "--http-port", str(n["rest"])]
        n["round"] = round_

    def start_ream2(self, name, bootnode=None):
        n = self.nodes[name]
        d, r = n["dir"], n["round"]
        boot = "none"
        if bootnode:
            b = self.nodes[bootnode]
            boot = f"/ip4/127.0.0.1/udp/{b['p2p']}/quic-v1/p2p/{b['peerid']}"
        argv = n["reamargs"] + ["--bootnodes", boot, "--is-aggregator"]
        t = str(self.ream_threads)
        n["ream"] = self.spawn(f"{name}-ream-{r}", argv, {"PQ_MIGRATE_EXTERNAL_ENGINE_CONFIG": str(d / f"engine-{r}.json"),
                                                         "PQ_REAM_SIGNER_CONFIG": str(d / f"signer-{r}.json"),
                                                         "RAYON_NUM_THREADS": t, "TOKIO_WORKER_THREADS": t})


class Switch:
    def __init__(self, a):
        self.a = a
        self.root = a.root
        self.out = a.root
        self.out.mkdir(parents=True, exist_ok=False)
        self.rt = self.out / "runtime"
        self.rt.mkdir(mode=0o700)
        self.rec = {"status": "RUNNING", "runId": a.run_id, "keys": "fresh disposable", "review": REVIEW,
                    "tier": "two-node lab using the installed geth and Ream; "
                            "synthetic EL genesis; public test keys; n = 1",
                    "elPeering": "none: Ream's pq-lean-fenced-v1 profile requires net_peerCount == 0, so every transaction "
                                 "goes by RPC to both geth nodes; the CL nodes peer over QUIC",
                    "checks": {}, "observations": [], "keysProvisioned": False, "phase1Started": False}
        self.lab = Lab2(a.prefix, self.out, self.rec)
        self.lab.ream_threads = a.ream_threads
        self.sent = {}
        self.nonces = {k: 0 for k in SENDERS}
        self.py = [sys.executable, "-B", "-I"]

    # ------------------------------------------------------------------ bookkeeping
    def save(self):
        self.lab.save()

    def check(self, name, ok, **ev):
        self.rec["checks"][name] = {"pass": bool(ok), "unix": round(time.time(), 3), **ev}
        self.save()
        print(json.dumps({"check": name, "pass": bool(ok)}), flush=True)
        return bool(ok)

    def dump(self, name, obj):
        p = self.out / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(obj, indent=1, default=str) + "\n")
        return name

    def step(self, name, **kw):
        self.lab.step(name, **kw)

    def url(self, x):
        return self.lab.nodes[x]["url"]

    def rpc(self, x, method, params):
        return L.rpc(self.url(x), method, params)

    def tag(self, x, t):
        try:
            return blk(self.lab.el(x, t))
        except L.RPCError:
            return None

    def heads(self):
        return {x: {t: self.tag(x, t) for t in ("latest", "safe", "finalized")} for x in HX}

    def block(self, x, number):
        return blk(self.rpc(x, "eth_getBlockByNumber", [hex(number), False]))

    def wait_until(self, unix, what):
        d = unix - time.time()
        if d > 0:
            time.sleep(d)
        self.rec.setdefault("waits", []).append({"what": what, "target": unix, "at": round(time.time(), 3)})

    def receipts(self, h, timeout, what):
        def ok():
            r = {x: self.rpc(x, "eth_getTransactionReceipt", [h]) for x in HX}
            return r if all(r.values()) and r["H"] == r["X"] else None
        return L.wait_for(ok, timeout, 0.5, "receipts of " + what)

    def revert_info(self, x, h):
        try:
            t = self.rpc(x, "debug_traceTransaction", [h, {"tracer": "callTracer"}])
            return {"error": t.get("error"), "revertReason": t.get("revertReason"), "gasUsed": t.get("gasUsed")}
        except (L.RPCError, OSError, ValueError) as e:
            return {"traceError": repr(e)[:300]}

    def pycmd(self, label, argv, timeout=600):
        q = subprocess.run(self.py + [str(x) for x in argv], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout,
                           cwd="/")
        (self.out / (label + ".log")).write_bytes(q.stdout)
        self.rec.setdefault("commands", []).append({"label": label, "argv": [str(x) for x in argv], "exit": q.returncode})
        self.save()
        return q.returncode, q.stdout.decode(errors="replace")

    # ------------------------------------------------------------------ setup
    def setup(self):
        a = self.a
        prefix = a.prefix
        self.rec["binaries"] = {k: L.file_sha256(prefix / "libexec" / k) for k in
                                ("geth", "ream", "profile-tool", "profile-tool-three", "fresh-public-keys", "export-signed",
                                 "audit-history")}
        sys.path.insert(0, str(prefix / "tools"))
        from install import require_installed
        installed = require_installed(prefix)
        self.rec["installedManifestSHA256"] = L.file_sha256(prefix / "manifest.json")
        self.rec["clientSourceManifests"] = {k: installed[k] for k in ("gethSourceManifestSHA256", "reamSourceManifestSHA256")}
        (self.out / "scenario").mkdir()
        self.snapshot = scenario.make_snapshot()
        (self.out / "scenario/snapshot.json").write_text(json.dumps(self.snapshot, indent=1) + "\n")
        self.snap = {v["index"]: v for v in self.snapshot["validators"]}
        self.load_proof(installed)
        self.stores, self.pub = self.rehearsal_keys()
        self.labels_path = self.out / "labels.json"
        self.labels_path.write_text(json.dumps(scenario.make_labels({"keys": self.pub}), indent=1) + "\n")
        self.keydir = {k: self.stores["H" if k.startswith("H") else "X"] / "hash-sig-keys" / k for k in HONEST_KEYS + ATTACKER_KEYS}
        state = {}
        for k, d in self.keydir.items():
            on_disk = {r: "0x" + (d / (r + ".pub")).read_bytes().hex() for r in ("attestation", "proposal")}
            state[k] = {"pubMatches": on_disk == self.pub[k], "provisioned": (d / "history-provisioned-once").exists(),
                        "secret": (d / "attestation.ssz").exists() and (d / "proposal.ssz").exists()}
        self.check("setup.keysUnusedAndMatching", all(v["pubMatches"] for v in state.values()) and
                   not any(v["provisioned"] for v in state.values()) and all(state[k]["secret"] for k in PHASE1_KEYS)
                   and not (self.stores["H"] / "registry.yaml").exists() and not (self.stores["X"] / "registry.yaml").exists(),
                   keys=state)
        if not self.rec["checks"]["setup.keysUnusedAndMatching"]["pass"]:
            raise Abort("key directories are not in their never-used state")
        self.dump("keys-public.json", {"publicTestOnly": True, "keys": self.pub, "stores": {k: str(v) for k, v in self.stores.items()},
                                       "phase1Keys": PHASE1_KEYS})

    def load_proof(self, installed):
        """Load only current public fixture exports; never generate or rewrite PI."""
        if self.a.recovery_proof is None:
            self.rec["latePathNotRun"] = "--recovery-proof was not supplied; fresh package public-test recovery output is required"
            return
        prefix = self.a.prefix
        remaining = max(3600, self.a.lead + self.a.phase0_slots * SLOT + self.a.delta + self.a.t_after_t0
                        + self.a.phase1_timeout + (44 + self.a.silent_slots) * SLOT + 180)
        fixture = read_public_recovery(self.a.recovery_proof, now=int(time.time()), minimum_remaining=remaining)
        binding = installed_verifier_binding(prefix, installed)
        native = verify_native(prefix, fixture)
        # The only seed is reconstructed from the authenticated installed public
        # fixture. No credential or signing seed is read from the proof directory.
        sys.path.insert(0, str(prefix / "prover"))
        sys.path.insert(0, str(prefix / "wallet"))
        from statement import bip39_seed, parse_path
        import wallet_epochs
        import wallet as w
        public = json.loads((prefix / "share/public-input.json").read_text())
        credential = public["credential"]
        if credential.get("public") is not True:
            raise ValueError("installed fixture is not explicitly public test data")
        epoch = public["pq_key"]["epoch"]
        if type(epoch) is not int or epoch != 0:
            raise ValueError("late path requires the initial public test key epoch")
        seed = bip39_seed(credential["mnemonic"], credential.get("passphrase", ""))
        xi = wallet_epochs.derive_epoch_seed(seed, "ML-DSA-44", tuple(parse_path(public["path"])), epoch)
        self.w = w
        self.cr = w.wire.Worker(prefix / "prover-runtime/bin/pq-test-crypto")
        pk = self.cr("pk", xi)
        commitment = self.cr("hash", b"\x01" + pk)
        if pk != fixture.public_key or commitment != fixture.commitment:
            raise ValueError("proof does not bind the installed public test signing key")
        self.key = w.KeyMaterial(epoch, xi, pk, commitment)
        self.wcfg = dict(chain_id=CHAIN, registry="0x" + "00" * 18 + "0800", max_priority_fee_per_gas=10**9,
                         max_fee_per_gas=2 * 10**9, migration_gas_limit=16000000, pq_transaction_gas_limit=1500000)
        state = SimpleNamespace(chain_id=CHAIN, legacy_address=OWNER[2:])
        raw = w._encode_0x7e(state, 0, fixture.pi, fixture.proof, self.wcfg,
                            w.FeeChoice(fee_mode=0, fee_sponsor="00" * 20, fee_auth_until=0), crypto=self.cr)
        self.recovery = {"raw": raw, "hash": "0x" + self.cr("hash", raw).hex()}
        self.proof = {"proofSHA256": fixture.proof_sha256, "piSHA256": fixture.pi_sha256,
                      "proofBytes": len(fixture.proof), "expiry": fixture.expiry, "commit": "0x" + commitment.hex(),
                      "publicTestOnly": True, "acceptanceBinding": binding, "nativeVerification": native}
        self.rec["proof"] = self.proof
        self.rec["recoveryCarrier"] = {"hash": self.recovery["hash"], "bytes": len(raw), "sha256": sha_bytes(raw),
                                       "encoder": "installed wallet._encode_0x7e, initial unsponsored recovery"}
        self.save()

    def rehearsal_keys(self):
        """Fresh disposable keys in the run directory: real key pairs for the phase-1 signers (H0-H5, A6), and public-key
        only directories with random canonical keys for every other registration (they never sign)."""
        base = self.out / "keys"
        stores = {"H": base / "nodes/H", "X": base / "nodes/X"}
        seeds = base / "seeds"
        seeds.mkdir(parents=True, mode=0o700)
        pub = {}
        for k in HONEST_KEYS + ATTACKER_KEYS:
            d = stores["H" if k.startswith("H") else "X"] / "hash-sig-keys" / k
            d.parent.mkdir(parents=True, exist_ok=True)
            if k in PHASE1_KEYS:
                pub[k] = self.lab.fresh_keys(d, seeds / (k + "-PUBLIC-seeds.bin"))
            else:
                d.mkdir()
                for r in ("attestation", "proposal"):
                    (d / (r + ".pub")).write_bytes(canonical_random_key())
                pub[k] = {r: "0x" + (d / (r + ".pub")).read_bytes().hex() for r in ("attestation", "proposal")}
        self.step("rehearsal-keys", note="fresh disposable keys: 7 real pairs, 8 public-only")
        return stores, pub


    # ------------------------------------------------------------------ phase 0
    def phase0(self):
        a, lab = self.a, self.lab
        keys = self.rt / "p0-keys"
        keys.mkdir()
        p0 = {}
        for x in "ABC":
            p0[x] = lab.fresh_keys(keys / x, keys / (x + "-PUBLIC-seeds.bin"))
        self.rec["phase0Validators"] = {"note": "three fresh disposable lab validators; never registered", "publicKeys": p0}
        G0 = int(time.time()) + a.lead
        timing = switch_timeline(G0, a.phase0_slots, a.delta, a.t_after_t0, a.min_lead)
        self.Halt = timing["halt"]
        Dreg, S, T0, T = (timing[k] for k in ("dReg", "S", "T0", "T"))
        self.G0, self.Dreg, self.S, self.T0, self.T = G0, Dreg, S, T0, T
        self.K = a.phase0_slots
        if hasattr(self, "proof") and not T + 44 * SLOT < self.proof["expiry"] <= T + 604800:
            raise Abort("public recovery proof does not cover this run's actual late-path window")
        self.rec["timeline"] = {"elGenesis": G0, "phase0LeanGenesis": G0, "dReg": Dreg, "S": S, "T0": T0, "T": T,
                                "slotSeconds": SLOT, "phase0Slots": a.phase0_slots, "deltaSeconds": a.delta, "halt": self.Halt,
                                "utc": {k: time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(v)) for k, v in
                                        (("elGenesis", G0), ("dReg", Dreg), ("S", S), ("T0", T0), ("T", T))}}
        keccak = "0x" + L.keccak(bytes.fromhex(runtime_hex())).hex()
        self.profile = scenario.make_profile(self.snapshot, Dreg, S, "n1-checkpoint-" + a.run_id, keccak)
        self.profile_path = self.out / "profile.json"
        self.profile_path.write_text(json.dumps(self.profile, indent=1) + "\n")
        alloc = dict(genesis_entry(Dreg))
        for acct in SENDERS.values():
            alloc[L.test_account(acct)[1]] = {"balance": hex(10 * L.ETH), "nonce": "0x0", "code": "0x", "storage": {}}
        alloc[OWNER] = {"balance": hex(2 * L.ETH), "nonce": "0x0", "code": "0x", "storage": {}}
        template = json.loads((a.prefix / "share/templates/generator-el-genesis.json").read_text())["alloc"]
        known = {k.lower().removeprefix("0x") for k in template}
        assert not {k.lower().removeprefix("0x") for k in alloc} & known, "an added account is already in the template"
        genesis = lab.el_genesis(G0, T0, T, extra_alloc=alloc)
        self.genesis_path = self.out / "el-genesis.json"
        self.genesis_path.write_text(json.dumps(genesis, indent=1))
        self.rec["elGenesis"] = {"sha256": L.file_sha256(self.genesis_path), "timestamp": G0,
                                 "pqMigrate": {k: genesis["config"]["pqMigrate"][k] for k in ("t0", "t", "receivingTime")},
                                 "registry": {"address": L.REGISTRY_ADDRESS, "dReg": Dreg, "runtimeKeccak": keccak},
                                 "funded": {**{L.test_account(v)[1]: "10 ETH (sender %s, m/44'/60'/0'/0/%d)" % (k, v)
                                               for k, v in SENDERS.items()}, OWNER: "2 ETH (fixture owner)"}}
        for x in HX:
            lab.start_geth(x, self.genesis_path, self.rt)
        gb = lab.nodes["H"]["genesisBlock"]
        assert gb["hash"] == lab.nodes["X"]["genesisBlock"]["hash"]
        self.rec["elGenesis"].update(hash=gb["hash"], stateRoot=gb["stateRoot"])
        self.gethPids = {x: lab.nodes[x]["geth"].pid for x in HX}
        self.save()
        code = {x: self.rpc(x, "eth_getCode", [WRC, "latest"]) for x in HX}
        assert all(len(c) > 2 for c in code.values()), "EIP-7002 contract present"
        # phase-0 Lean chain anchored to the EL genesis
        kd = {x: keys / x for x in "ABC"}
        cl0 = lab.lean_genesis([kd["A"], kd["B"], kd["C"]], G0, "cl-genesis-0")
        anchor0 = {"hash": gb["hash"], "stateRoot": gb["stateRoot"]}
        id0 = labnet.network_identity(cl0["clRoot"], anchor0["hash"], anchor0["stateRoot"])
        labnet.write_network(self.out / "lean-network-0.yaml", G0, [p0["A"], p0["B"], p0["C"]])
        labnet.write_registry(self.rt / "registry-0.yaml", {"H": [{"index": 0, "dir": kd["A"], **p0["A"]}],
                                                            "X": [{"index": 1, "dir": kd["B"], **p0["B"]},
                                                                  {"index": 2, "dir": kd["C"], **p0["C"]}]})
        hist0 = {x: self.rt / x / "signing-history-0" for x in HX}
        tool3 = lab.bin("profile-tool-three")
        lab.command("H-history-0", [tool3, "history", kd["A"], hist0["H"], "0x" + id0, "0"])
        lab.command("X-history-0", [tool3, "history", kd["B"], hist0["X"], "0x" + id0, "1", kd["C"], "2"])
        for x in HX:
            lab.start_material_server(x, 0)
        for x, peer_kd in (("H", kd["A"]), ("X", kd["B"])):
            lab.prepare_ream2(x, 0, network_yaml=self.out / "lean-network-0.yaml", registry_yaml=self.rt / "registry-0.yaml",
                              cl_root=cl0["clRoot"], anchor=anchor0, peer="X" if x == "H" else "H", peer_keydir=peer_kd,
                              signer_cfg={"format": 1, "network_identity": "0x" + id0, "history": str(hist0[x]),
                                          "start_slot": 0, "end_slot": 4096})
        self.rec["phase0"] = {"genesisTime": G0, "clGenesis": cl0, "networkIdentity": "0x" + id0, "anchor": anchor0,
                              "validators": {"H": [0], "X": [1, 2]}}
        lab.start_ream2("X")
        L.wait_for(lambda: labnet.port_open(lab.nodes["X"]["rest"]), 60, 0.5, "Ream X REST (phase 0)")
        lab.start_ream2("H", bootnode="X")
        self.step("phase0-started", note=f"EL and phase-0 Lean genesis {G0} ({round(G0 - time.time(), 1)} s ahead); D_reg {Dreg}; S {S}")

    # ------------------------------------------------------------------ registrations
    def payload(self, spec):
        name, index, label, signer, _, kind = spec
        if kind.startswith("311"):
            base, _ = register.build(self.profile, self.snapshot, 0, bytes.fromhex(self.pub["H0"]["attestation"][2:]),
                                     bytes.fromhex(self.pub["H0"]["proposal"][2:]), L.interop_sk(0))
            return base[:311], None
        att, prop = (bytes.fromhex(self.pub[label][r][2:]) for r in ("attestation", "proposal"))
        p, m = register.build(self.profile, self.snapshot, index, att, prop, L.interop_sk(signer))
        return p, m

    def send(self, spec):
        name, index, label, signer, sender, kind = spec
        p, m = self.payload(spec)
        acct = SENDERS[sender]
        nonce = self.nonces[sender]
        r = register.send([self.url(x) for x in HX], p, acct, nonce, CHAIN)
        self.nonces[sender] += 1
        ok = all(v == r["hash"] for v in r["answers"].values())
        self.sent[name] = {"name": name, "index": index, "keys": label, "signerInterop": signer, "kind": kind,
                           "sender": r["from"], "senderPath": "m/44'/60'/0'/0/%d" % acct, "nonce": nonce, "hash": r["hash"],
                           "payloadBytes": len(p), "payloadSHA256": sha_bytes(p), "payload": "0x" + p.hex(),
                           "sentUnix": round(time.time(), 3), "answers": {x: a for x, a in zip(HX, r["answers"].values())},
                           "acceptedByBothPools": ok}
        if m is not None:
            self.sent[name]["message"] = L.message_json(m)
        return self.sent[name]

    def registrations(self):
        L.wait_for(lambda: all((self.tag(x, "latest") or {}).get("number", 0) >= 1 for x in HX), self.G0 + 60 - time.time(), 0.5,
                   "first phase-0 block on both nodes")
        groups = {}
        for g, specs in GROUPS.items():
            for spec in specs:
                self.send(spec)
            blocks = set()
            for spec in specs:
                s = self.sent[spec[0]]
                rc = self.receipts(s["hash"], 4 * SLOT, spec[0])
                s["receipts"] = rc
                s["block"] = int(rc["H"]["blockNumber"], 16)
                s["status"] = int(rc["H"]["status"], 16)
                s["logs"] = len(rc["H"]["logs"])
                if s["status"] == 0:
                    s["revert"] = {x: self.revert_info(x, s["hash"]) for x in HX}
                blocks.add(s["block"])
            groups[g] = sorted(blocks)
            self.step("registration-group", note=f"group {g} in block(s) {sorted(blocks)}")
        self.rec["registrationGroups"] = groups
        self.dump("registrations-sent.json", self.sent)
        s = self.sent
        valid = [n for g in GROUPS.values() for (n, *_r) in g if n != "malformed"]
        self.check("phase0.registrationsIncluded", all(s[n]["acceptedByBothPools"] and s[n]["status"] == 1 and s[n]["logs"] == 1
                                                       for n in valid),
                   statuses={n: (s[n]["status"], s[n]["logs"], s[n]["block"]) for n in valid})
        mal = s["malformed"]
        self.check("phase0.malformedReverts", mal["status"] == 0 and mal["logs"] == 0 and
                   all((v.get("revertReason") or "") == "N1: length" for v in mal["revert"].values()), revert=mal["revert"])
        self.check("phase0.conflictOrdersByBlock", s["A7"]["block"] < s["H7"]["block"] and s["H8"]["block"] < s["A8"]["block"],
                   blocks={n: s[n]["block"] for n in ("A7", "H7", "H8", "A8")})

    # ------------------------------------------------------------------ tail, stop, B_ck
    def tail_and_stop(self):
        Dreg = self.Halt  # Scheduling reference only; the registry deadline remains self.Dreg.
        try:
            L.wait_for(lambda: all((self.tag(x, "latest") or {}).get("timestamp", 0) >= Dreg - 2 * SLOT for x in HX),
                       max(1, Dreg - 2 * SLOT + 6 - time.time()), 0.25, "the head of slot K-2")
        except TimeoutError:
            self.rec["observations"].append({"label": "slot K-2 head not seen; tail registration sent anyway"})
        self.send(TAIL)
        self.wait_until(Dreg - SLOT + 7.0, "stop window opens (7.0 s into the last slot before D_reg)")
        agreed = None
        while time.time() < Dreg - SLOT + 8.5:
            h = self.heads()
            if all(h[x]["latest"] and h[x]["finalized"] for x in HX) and h["H"]["latest"]["hash"] == h["X"]["latest"]["hash"] \
                    and h["H"]["finalized"]["hash"] == h["X"]["finalized"]["hash"]:
                agreed = h
                break
            time.sleep(0.1)
        before = self.heads()
        t_stop = time.time()
        for x in HX:                          # SIGINT to both first, so neither runs alone for long
            self.lab.nodes[x]["ream"].send_signal(signal.SIGINT)
        stops = {x: self.lab.stop_ream(x) for x in HX}
        fences = {x: (self.lab.nodes[x]["dir"] / "signing-fence").exists() for x in HX}
        quar = {x: (self.lab.nodes[x]["dir"] / "session-0.quarantine").exists() for x in HX}
        owners = {x: (self.lab.nodes[x]["dir"] / "session-0.owner").exists() for x in HX}
        time.sleep(1.0)
        after = self.heads()
        stop = {"stopUnix": round(t_stop, 3), "intoSlot": round(t_stop - (Dreg - SLOT), 3), "agreedBeforeStop": agreed is not None,
                "headsBefore": before, "headsAfter": after, "exit": stops, "fencePresent": fences, "quarantine": quar,
                "sessionOwnerLeft": owners}
        self.check("phase0.stoppedCleanly", not any(fences.values()) and not any(quar.values()) and not any(owners.values())
                   and all(r == 0 for _, r in stops.values()), exit=stops, fences=fences, quarantine=quar, owners=owners)
        self.check("phase0.stopBeforeHalt", Dreg - SLOT + 7.0 <= t_stop <= Dreg - SLOT + 8.6,
                   stopUnix=t_stop, dReg=Dreg)
        same = after["H"]["latest"]["hash"] == after["X"]["latest"]["hash"] and \
            after["H"]["finalized"]["hash"] == after["X"]["finalized"]["hash"]
        if same:
            bck = after["H"]["finalized"]
            stop["bckRule"] = "geth's finalized block, the same on both nodes (part 1's README)"
        else:
            raise Abort("execution nodes disagree on head/finalized checkpoint")
        self.bck = bck
        head0 = after["H"]["latest"]
        tail = [self.block("H", n) for n in range(bck["number"] + 1, head0["number"] + 1)]
        stop.update(bck=bck, tail=tail)
        self.rec["bck"] = bck
        self.check("phase0.bckIsBothFinalized", same and bck["timestamp"] < self.Dreg, bck=bck, finalized={x: after[x]["finalized"] for x in HX})
        self.check("phase0.tailWithinReorgLimit", 0 <= len(tail) <= 32, tailBlocks=len(tail))
        ht = self.sent[TAIL[0]]
        rc = {x: self.rpc(x, "eth_getTransactionReceipt", [ht["hash"]]) for x in HX}
        ht["receiptsAtStop"] = rc
        ht["block"] = int(rc["H"]["blockNumber"], 16) if rc["H"] else None
        self.check("phase0.tailRegistrationAfterBck", ht["block"] is not None and ht["block"] > bck["number"] and
                   rc["H"] == rc["X"] and int(rc["H"]["status"], 16) == 1, tailBlock=ht["block"], bck=bck["number"])
        self.dump("phase0-stop.json", stop)
        self.dump("registrations-sent.json", self.sent)
        self.step("phase0-stopped", note=f"B_ck = block {bck['number']}; head {head0['number']}; tail {len(tail)}")

    # ------------------------------------------------------------------ after D_reg
    def after_dreg(self):
        self.wait_until(self.Dreg + 1.0, "D_reg + 1 s")
        h = self.heads()
        self.check("halt.noBlockAtOrAfterDreg", all(h[x]["latest"]["timestamp"] < self.Dreg for x in HX),
                   heads={x: h[x]["latest"] for x in HX})
        s = self.send(LATE)
        self.check("halt.lateCallInBothPools", s["acceptedByBothPools"], answers=s["answers"])
        self.dump("registrations-sent.json", self.sent)

    # ------------------------------------------------------------------ checkpoint
    def checkpoint(self):
        a = self.a
        ck = self.out / "checkpoint"
        code, out = self.pycmd("checkpoint-run", [PART1 / "checkpoint.py", "run", "--profile", self.profile_path,
                                                  "--snapshot", a.root / "scenario/snapshot.json", "--bck", self.bck["hash"],
                                                  "--genesis", self.genesis_path, "--expect-genesis-sha256", self.rec["elGenesis"]["sha256"],
                                                  "--rpc", self.url("H"), "--rpc", self.url("X"), "--labels", self.labels_path,
                                                  "--out", ck, "--tool3", self.lab.bin("profile-tool-three")])
        res = json.loads(out.strip().splitlines()[-1]) if out.strip() else {}
        self.rec["checkpoint"] = {"exit": code, "result": res}
        self.save()
        if code != 0:
            raise Abort("checkpoint refused: " + json.dumps(res)[:300])
        self.checkpoint_manifest = res["manifestSHA256"]
        self.ck = ck
        self.lean = json.loads((ck / "lean-validators.json").read_text())["leanSet"]
        self.excl = json.loads((ck / "exclusions.json").read_text())
        self.regs = json.loads((ck / "registrations.json").read_text())["registrations"]
        self.anchor = json.loads((ck / "anchor.json").read_text())
        self.stake = json.loads((ck / "stake-report.json").read_text())
        excluded = {str(e["index"]): e["reason"] for e in self.excl["excluded"]}
        gate = {"leanSet": res.get("leanSet") == EXPECTED_LEAN, "excluded": excluded == EXPECTED_EXCLUDED,
                "fA": self.stake["rule3c"].get("fA", {}).get("fraction") == "1/7",
                "withinBound": self.stake["rule3c"].get("verdict") == "within bound: f_A < 1/3",
                "manifest": (ck / "MANIFEST.json").exists()}
        self.check("checkpoint.gate", all(gate.values()), gate=gate, leanSet=res.get("leanSet"), excluded=excluded,
                   manifestSHA256=res.get("manifestSHA256"), clRoot=res.get("clRoot"))
        if not all(gate.values()):
            raise Abort("checkpoint outcome differs from the scenario: " + json.dumps(gate))

    # ------------------------------------------------------------------ phase 1
    def prepare_phase1(self):
        a, lab = self.a, self.lab
        if time.time() > self.S - a.min_lead:
            raise Abort("less than %d s before S; phase 1 not started" % a.min_lead)
        lay = self.out / "layout"
        bindings = [argument for index, label in enumerate(PHASE1_KEYS)
                    for argument in ("--binding", "%s:%d=%s" % ("H" if index < 6 else "X", index, label))]
        code, out = self.pycmd("checkpoint-layout", [PART1 / "checkpoint.py", "layout", "--checkpoint", self.ck,
                                                     "--keystore", "H=%s" % self.stores["H"], "--keystore", "X=%s" % self.stores["X"],
                                                     "--out", lay, "--expect-manifest-sha256", self.checkpoint_manifest] + bindings)
        layout = json.loads((lay / "layout.json").read_text()) if code == 0 else None
        ok = code == 0 and layout["nodes"] == {"H": [0, 1, 2, 3, 4, 5], "X": [6]} and layout["unheldLeanIndices"] == []
        self.check("phase1.layout", ok, layout=layout)
        if not ok:
            raise Abort("layout differs: " + out[-300:])
        ident = labnet.network_identity(self.anchor["anchorClRoot"], self.bck["hash"], self.bck["stateRoot"])
        assert "0x" + ident == self.anchor["networkIdentity"] and self.anchor["engineAnchor"]["anchor_el_hash"] == self.bck["hash"]
        hist = {x: self.rt / x / "signing-history-1" for x in HX}
        regyaml = {x: self.stores[x] / "registry.yaml" for x in HX}
        args = {}
        for x in HX:
            reg = json.loads((lay / ("registry-%s.yaml" % x)).read_text())[x]
            pairs = sorted({(e["index"], str(self.stores[x] / "hash-sig-keys" / Path(e["privkey_file"]).parent)) for e in reg})
            args[x] = pairs
        self.check("phase1.historyKeyDirs", [Path(d).name for _, d in args["H"]] == PHASE1_KEYS[:6] and
                   [Path(d).name for _, d in args["X"]] == ["A6"] and [i for i, _ in args["H"]] == list(range(6)) and
                   [i for i, _ in args["X"]] == [6], dirs=args)
        if time.time() > self.S - a.min_lead:
            raise Abort("less than %d s before S; phase 1 not started" % a.min_lead)
        # ---- from here on the leanXMSS keys are committed to this genesis (R2): never reuse them
        self.rec["keysProvisioned"] = True
        self.save()
        for x in HX:
            shutil.copyfile(lay / ("registry-%s.yaml" % x), regyaml[x])
        tool3 = lab.bin("profile-tool-three")
        for x in HX:
            argv = [tool3, "history", args[x][0][1], hist[x], self.anchor["networkIdentity"], str(args[x][0][0])]
            for i, d in args[x][1:]:
                argv += [d, str(i)]
            lab.command(f"{x}-history-1", argv)
        for x in HX:
            lab.start_material_server(x, 1)
        pubdirs = sorted((self.ck / "pub").iterdir())
        for x, pk in (("H", pubdirs[0]), ("X", pubdirs[6])):
            lab.prepare_ream2(x, 1, network_yaml=self.ck / "lean-network.yaml", registry_yaml=regyaml[x],
                              cl_root=self.anchor["anchorClRoot"], anchor={"hash": self.bck["hash"], "stateRoot": self.bck["stateRoot"]},
                              peer="X" if x == "H" else "H", peer_keydir=pk,
                              signer_cfg={"format": 1, "network_identity": self.anchor["networkIdentity"], "history": str(hist[x]),
                                          "start_slot": 0, "end_slot": 4096})
        self.hist = hist
        self.before = self.invariant_snapshot("beforeS")
        lab.start_ream2("H")
        self.rec["phase1Started"] = True
        L.wait_for(lambda: labnet.port_open(lab.nodes["H"]["rest"]), 60, 0.5, "Ream H REST (phase 1)")
        lab.start_ream2("X", bootnode="H")
        lead = round(self.S - time.time(), 1)
        self.rec["phase1"] = {"S": self.S, "clRoot": self.anchor["anchorClRoot"], "networkIdentity": self.anchor["networkIdentity"],
                              "anchor": self.anchor["engineAnchor"], "startLeadSeconds": lead,
                              "nodes": {"H": "Lean validators 0-5 (honest owners H0-H5)", "X": "Lean validator 6 (A's key A6)"}}
        self.check("phase1.startedAtLeast60sBeforeS", lead >= 60, leadSeconds=lead)
        self.step("phase1-started", note=f"S = {self.S} ({lead} s ahead); anchor B_ck {self.bck['number']}")

    def invariant_snapshot(self, label):
        bh = {"blockHash": self.bck["hash"]}
        regs = {x: {"atBck": [self.rpc(x, "eth_getStorageAt", [L.REGISTRY_ADDRESS, hex(s), bh]) for s in (0, 1, 2)],
                    "latest": [self.rpc(x, "eth_getStorageAt", [L.REGISTRY_ADDRESS, hex(s), "latest"]) for s in (0, 1, 2)]}
                for x in HX}
        accounts = [L.test_account(v)[1] for v in SENDERS.values()] + [OWNER, L.REGISTRY_ADDRESS]
        bal = {x: {acct: self.rpc(x, "eth_getBalance", [acct, bh]) for acct in accounts} for x in HX}
        snap = {"label": label, "unix": round(time.time(), 3),
                "gethBinarySHA256": L.file_sha256(self.a.prefix / "libexec/geth"),
                "elGenesisFileSHA256": L.file_sha256(self.genesis_path),
                "genesisBlock": {x: blk(self.rpc(x, "eth_getBlockByNumber", ["0x0", False])) for x in HX},
                "gethPids": {x: self.lab.nodes[x]["geth"].pid for x in HX},
                "gethAlive": {x: self.lab.nodes[x]["geth"].poll() is None for x in HX},
                "bckBlock": {x: blk(self.rpc(x, "eth_getBlockByHash", [self.bck["hash"], False])) for x in HX},
                "registrySlots0to2": regs, "balancesAtBck": bal, "heads": self.heads()}
        self.dump(f"T7-invariants-{label}.json", snap)
        return snap

    # ------------------------------------------------------------------ the switch
    def switch(self):
        a, lab, S, bck = self.a, self.lab, self.S, self.bck
        self.after_dreg()
        s = self.send(AFTER_S)
        first, end = {}, S + a.phase1_timeout
        last = None
        done = None
        while time.time() < end:
            time.sleep(0.25)
            for x in HX:
                if lab.nodes[x]["ream"].poll() is not None:
                    raise RuntimeError(f"phase-1 Ream {x} exited {lab.nodes[x]['ream'].returncode}")
            try:
                h = self.heads()
            except (OSError, ValueError, L.RPCError):
                continue
            t = round(time.time(), 3)
            key = json.dumps({x: (h[x]["latest"]["hash"], (h[x]["finalized"] or {}).get("hash")) for x in HX})
            if key != last:
                last = key
                self.rec["observations"].append({"label": "phase1", "unix": t, "slotOfS": round((t - S) / SLOT, 2),
                                                 "el": {x: {k: (v or {}).get("number") for k, v in h[x].items()} for x in HX}})
            for x in HX:
                lat, fin = h[x]["latest"], h[x]["finalized"]
                if lat["hash"] == bck["hash"]:
                    first.setdefault(x + ".headIsBck", t)
                if lat["number"] > bck["number"] and lat["timestamp"] >= S:
                    first.setdefault(x + ".phase1Head", t)
                if fin and fin["number"] > bck["number"] and fin["timestamp"] >= S:
                    first.setdefault(x + ".phase1Finalized", t)
            if all(x + ".phase1Finalized" in first for x in HX):
                done = h
                break
        self.rec["firstSeen"] = first
        self.save()
        if done is None:
            raise TimeoutError("phase 1 did not finalize a block past B_ck on both nodes")
        nxt = {x: self.block(x, bck["number"] + 1) for x in HX}
        canon = {x: self.block(x, bck["number"])["hash"] for x in HX}
        self.check("T7.firstPhase1BlockParentIsBck", all(nxt[x]["parentHash"] == bck["hash"] and nxt[x]["timestamp"] >= S and
                                                         nxt[x]["hash"] == nxt["H"]["hash"] for x in HX), next=nxt)
        self.check("T7.bckStillCanonical", all(canon[x] == bck["hash"] for x in HX), canonical=canon)
        stop = json.loads((self.out / "phase0-stop.json").read_text())
        orphaned = {x: [b["hash"] for b in stop["tail"] if (self.block(x, b["number"]) or {}).get("hash") != b["hash"]] for x in HX}
        self.check("switch.phase0TailOrphaned", all(len(orphaned[x]) == len(stop["tail"]) for x in HX), orphaned=orphaned)
        self.check("T6.finalizesPastBck", all(done[x]["finalized"]["number"] > bck["number"] for x in HX),
                   finalized={x: done[x]["finalized"] for x in HX}, firstSeen=first)
        self.step("phase1-finalized", note="EL finalized H %d, X %d" % (done["H"]["finalized"]["number"], done["X"]["finalized"]["number"]))
        # receipts of the calls after D_reg and after S (and of the dropped tail registration, if re-included)
        out = {}
        for name in (LATE[0], AFTER_S[0]):
            r = self.sent[name]
            rc = self.receipts(r["hash"], 6 * SLOT, name)
            r["receipts"] = rc
            r["block"] = int(rc["H"]["blockNumber"], 16)
            r["status"] = int(rc["H"]["status"], 16)
            r["revert"] = {x: self.revert_info(x, r["hash"]) for x in HX}
            out[name] = {"block": r["block"], "status": r["status"], "logs": len(rc["H"]["logs"]), "revert": r["revert"],
                         "blockTimestamp": self.block("H", r["block"])["timestamp"]}
        tl = self.sent[TAIL[0]]
        rc = {x: self.rpc(x, "eth_getTransactionReceipt", [tl["hash"]]) for x in HX}
        tl["receiptsAfterSwitch"] = rc
        out[TAIL[0]] = {"tailBlock": tl.get("block"), "receiptAfterSwitch": None if not rc["H"] else
                        {"block": int(rc["H"]["blockNumber"], 16), "status": int(rc["H"]["status"], 16),
                         "revert": {x: self.revert_info(x, tl["hash"]) for x in HX}}}
        self.dump("registrations-sent.json", self.sent)
        self.dump("T2-calls-after-Dreg-and-S.json", out)
        after = lambda n: (out[n]["status"] == 0 and out[n]["logs"] == 0 and out[n]["blockTimestamp"] >= self.Dreg and  # noqa: E731
                           all((v.get("revertReason") or "") == "N1: after D_reg" for v in out[n]["revert"].values()))
        self.check("T2.registrationAfterSRefused", after(AFTER_S[0]) and self.sent[AFTER_S[0]]["sentUnix"] >= S, calls=out)
        self.check("dreg.index9CallAfterDregReverts", after(LATE[0]), call=out[LATE[0]])

    def rest_reads(self):
        res, cmp = {}, {}
        want = [(x["attestation"].lower(), x["proposal"].lower()) for x in self.lean]
        regkeys = {}
        for r in self.regs:
            if r.get("valid"):
                regkeys.setdefault(r["index"], set()).add((r["message"]["lean_attestation_pubkey"].lower(),
                                                           r["message"]["lean_proposal_pubkey"].lower()))
        for x in HX:
            res[x] = {}
            for sid in ("0", "finalized", "head"):
                try:
                    st = self.lab.rest(x, "states/" + sid)
                    res[x][sid] = {"config": st.get("config"), "slot": st.get("slot"), "validators": st.get("validators")}
                except Exception as e:  # noqa: BLE001
                    res[x][sid] = {"error": repr(e)[:300]}
            def kh(v):
                return v.lower() if isinstance(v, str) else json.dumps(v)
            got = {sid: [(kh(v["attestation_public_key"]), kh(v["proposal_public_key"])) for v in d["validators"]]
                   for sid, d in res[x].items() if d.get("validators")}
            cmp[x] = {sid: g == want for sid, g in got.items()}
            cmp[x]["genesisTime"] = all(int(d["config"]["genesis_time"]) == self.S for d in res[x].values() if d.get("config"))
        registered_match = all(regkeys.get(b) == {want[li]} for li, b in [(x["leanIndex"], x["beaconIndex"]) for x in self.lean])
        self.dump("T1-rest-states.json", {"reads": res, "comparison": cmp, "registeredTuplesMatchLeanSet": registered_match})
        self.check("T1.genesisKeysOverRestEqualRegistered", registered_match and all(cmp[x] and all(cmp[x].values()) and
                                                                                  len(cmp[x]) >= 2 for x in HX), comparison=cmp,
                   registeredTuplesMatchLeanSet=registered_match)

    def checkpoint_tests(self):
        s, regs = self.sent, self.regs
        by_tx = {r["tx"]: r for r in regs}
        honest = ["H0", "H1", "H2", "H3", "H4", "H5", "H5-again", "H7", "H8", "H9"]
        self.check("T1.honestRegistrationsAccepted", all(s[n]["status"] == 1 and s[n]["logs"] == 1 and s[n]["hash"] in by_tx
                                                         for n in honest),
                   seqs={n: by_tx.get(s[n]["hash"], {}).get("seq") for n in honest})
        inv = {str(e["seq"]): e for e in self.excl["invalidRegistrations"]}
        a9 = by_tx.get(s["A9x"]["hash"], {})
        a5 = by_tx.get(s["A5x"]["hash"], {})
        self.check("T3.index9InvalidEntryExcluded", a9.get("valid") is False and a9.get("reason") == "bls-invalid" and
                   str(a9.get("seq")) in inv, entry={k: a9.get(k) for k in ("seq", "index", "reason", "reasons")})
        inc = {x["beaconIndex"]: x for x in self.lean}
        self.check("T3b.index5StillIncluded", 5 in inc and a5.get("reason") == "bls-invalid" and
                   inc[5]["attestation"].lower() == self.pub["H5"]["attestation"].lower() and len(inc[5]["registrationSeqs"]) == 2,
                   invalidEntry={k: a5.get(k) for k in ("seq", "reason")}, included=inc.get(5))
        ex = {e["index"]: e for e in self.excl["excluded"]}
        seq = lambda n: by_tx[s[n]["hash"]]["seq"]  # noqa: E731
        self.check("T4.index6IncludedWithAsKey", 6 in inc and inc[6]["attestation"].lower() == self.pub["A6"]["attestation"].lower()
                   and inc[6]["proposal"].lower() == self.pub["A6"]["proposal"].lower() and inc[6]["leanIndex"] == 6, included=inc.get(6))
        self.check("T5.conflictsExcludedEitherOrder", ex.get(7, {}).get("reason") == "conflict" and ex.get(8, {}).get("reason") == "conflict"
                   and seq("A7") < seq("H7") and seq("H8") < seq("A8"),
                   order={"7": {"A7": seq("A7"), "H7": seq("H7")}, "8": {"H8": seq("H8"), "A8": seq("A8")}},
                   excluded={k: ex.get(k) for k in (7, 8)})
        self.check("T9.zeroCredentialExcludedWithReason", ex.get(9, {}).get("reason") == "withdrawal-credentials-0x00" and
                   ex.get(9, {}).get("rule") == "6 (a)" and by_tx.get(s["H9"]["hash"], {}).get("reasons") == ["withdrawal-credentials"],
                   excluded=ex.get(9), ownerEntry={k: by_tx.get(s["H9"]["hash"], {}).get(k) for k in ("seq", "reasons")})
        rule = self.stake["rule3c"]
        self.check("T6.fAOneSeventhOnLeanSet", rule.get("fA", {}).get("fraction") == "1/7" and rule.get("leanSetSize") == 7 and
                   rule.get("aControlledIncluded") == [6], rule3c=rule, beaconStakeInformationOnly=self.stake["beaconStake"])
        tail_in = any(r["tx"] == s[TAIL[0]]["hash"] for r in regs)
        self.check("checkpoint.tailRegistrationDropped", not tail_in and (s[TAIL[0]].get("block") or 0) > self.bck["number"],
                   tailBlock=s[TAIL[0]].get("block"), bck=self.bck["number"])

    def invariants(self):
        aft = self.invariant_snapshot("afterS")
        b = self.before
        self.check("T7.executionStatePreserved", all(execution_invariants(b, aft).values()), fields=execution_invariants(b, aft))
        same_regs = all(aft["registrySlots0to2"][x]["atBck"] == b["registrySlots0to2"][x]["atBck"] and
                        aft["registrySlots0to2"][x]["latest"][1:] == b["registrySlots0to2"][x]["atBck"][1:] for x in HX)
        self.check("T7.registryAccCountUnchanged", same_regs, before=b["registrySlots0to2"], after=aft["registrySlots0to2"])
        self.check("T7.balancesAtBckUnchanged", aft["balancesAtBck"] == b["balancesAtBck"] and
                   aft["bckBlock"] == b["bckBlock"])
        self.check("T7.gethAndGenesisDigestsSameAcrossS", aft["gethBinarySHA256"] == b["gethBinarySHA256"] ==
                   self.rec["binaries"]["geth"] and aft["elGenesisFileSHA256"] == b["elGenesisFileSHA256"] ==
                   self.rec["elGenesis"]["sha256"] and aft["genesisBlock"] == b["genesisBlock"] and
                   aft["gethPids"] == b["gethPids"] == self.gethPids and all(aft["gethAlive"].values()),
                   geth=aft["gethBinarySHA256"], genesisFile=aft["elGenesisFileSHA256"], pids=aft["gethPids"])
        # the checkpoint again, after S, at the same B_ck: the registrations after D_reg and after S change nothing
        rr = self.out / "checkpoint-rerun-after-S"
        code, out = self.pycmd("checkpoint-rerun-after-S", [PART1 / "checkpoint.py", "run", "--profile", self.profile_path,
                                                            "--snapshot", self.a.root / "scenario/snapshot.json", "--bck",
                                                            self.bck["hash"], "--rpc", self.url("H"), "--rpc", self.url("X"),
                                                            "--labels", self.labels_path, "--out", rr, "--tool3", self.lab.bin("profile-tool-three"),
                                                            "--genesis", self.genesis_path, "--expect-genesis-sha256", self.rec["elGenesis"]["sha256"]])
        refusal = json.loads((rr / "REFUSED.json").read_text()) if (rr / "REFUSED.json").is_file() else {}
        verify_manifest(self.ck, self.checkpoint_manifest)
        self.dump("T7-checkpoint-rerun-after-S.json", {"exit": code, "reason": refusal.get("reason"),
                                                       "originalManifestSHA256": self.checkpoint_manifest,
                                                       "originalManifestVerified": True,
                                                       "note": "after finality advances, an older B_ck cannot create another checkpoint"})
        self.check("T2.oldCheckpointRefusedAfterFinalityAdvances", code == 2 and refusal.get("reason") == "bck-not-last-finalized",
                   reason=refusal.get("reason"), originalManifestUnchanged=True)

    def raw_send(self, name, raw):
        h = "0x" + self.cr("hash", raw).hex()
        answers, known = {}, {}
        for node in HX:
            answer = L.rpc_raw(self.url(node), "eth_sendRawTransaction", ["0x" + raw.hex()])
            answers[node] = answer.get("result", answer.get("error"))
            error = answer.get("error")
            if isinstance(error, dict) and error.get("message", "").strip().lower() == "already known":
                # Ream can import the first submission before the other RPC
                # arrives, even though the geth nodes themselves are unpeered.
                transaction = self.rpc(node, "eth_getTransactionByHash", [h])
                known[node] = isinstance(transaction, dict) and transaction.get("hash") == h
        self.rec.setdefault("rawSubmissions", []).append({"name": name, "hash": h, "answers": answers,
                                                          "alreadyKnownVerified": known, "unix": round(time.time(), 3)})
        self.save()
        if not all(answers[node] == h or known.get(node) is True for node in HX):
            raise ValueError("raw submission refused: " + repr((name, answers, known)))
        return h

    def account(self, x, tag="latest"):
        return self.rpc(x, "eth_getPQAccount", [OWNER, tag])

    def late_path(self):
        if not hasattr(self, "proof"):
            return
        self.rec.setdefault("scenarioTimings", {})["T8"] = {"startedUnix": round(time.time(), 3)}
        self.save()
        T = self.T
        L.wait_for(lambda: all((self.tag(x, "latest") or {}).get("timestamp", 0) >= T for x in HX), max(1, T + 6 * SLOT - time.time()), 0.5,
                   "a head at or after T on both nodes")
        if not int(time.time()) + 8 * SLOT < self.proof["expiry"]:
            raise Abort("public recovery proof expired or lacks its submission window; regenerate outside this run")
        ev = {"T": T, "headsAtStart": self.heads(), "scope": "EL recovery, activation and EIP-7002 request transport; no CL exit/withdrawal/re-stake claim"}
        before = {x: self.account(x) for x in HX}
        h = self.raw_send("recovery-0x7e", self.recovery["raw"])
        rc = self.receipts(h, 8 * SLOT, "recovery")
        acc = {x: self.account(x) for x in HX}
        ev["recovery"] = {"hash": h, "receipts": rc, "accountBefore": before, "accountAfter": acc,
                          "blockTimestamp": self.block("H", int(rc["H"]["blockNumber"], 16))["timestamp"]}
        ok_rec = rc["H"]["status"] == "0x1" and acc["H"] == acc["X"] and acc["H"]["pqPkCommit"].lower() == self.proof["commit"] \
            and int(acc["H"]["migrationNonce"], 16) == 1 and not acc["H"]["activated"] and ev["recovery"]["blockTimestamp"] >= T
        nonce = int(self.rpc("H", "eth_getTransactionCount", [OWNER, "latest"]), 16)
        owner_b = bytes.fromhex(OWNER[2:])
        raw_act, row = self.w._signed_rotate_0x7c(self.cr, self.wcfg, owner_b, self.key, nonce, True)
        h2 = self.raw_send("activation-0x7c", raw_act)
        rc2 = self.receipts(h2, 8 * SLOT, "activation")
        acc2 = {x: self.account(x) for x in HX}
        ev["activation"] = {"hash": h2, "nonce": nonce, "kind": "activating same-key rotate (wallet._signed_rotate_0x7c), as L1",
                            "receipts": rc2, "accountAfter": acc2}
        ok_act = rc2["H"]["status"] == "0x1" and acc2["H"] == acc2["X"] and acc2["H"]["activated"]
        fee_word = self.rpc("H", "eth_call", [{"to": WRC, "data": "0x"}, "latest"])
        fee = int(fee_word, 16)
        pk7 = bytes.fromhex(self.snap[7]["pubkey"][2:])
        data = pk7 + (0).to_bytes(8, "big")
        raw7 = self.sign_tx(owner_b, nonce + 1, bytes.fromhex(WRC[2:]), value=fee, data=data)
        h3 = self.raw_send("withdrawal-request-0x7c", raw7)
        rc3 = self.receipts(h3, 8 * SLOT, "EIP-7002 request")
        logs = [lg for lg in rc3["H"]["logs"] if lg["address"].lower() == WRC]
        ldata = bytes.fromhex(logs[0]["data"][2:]) if logs else b""
        blocks = {x: self.rpc(x, "eth_getBlockByHash", [rc3["H"]["blockHash"], False]) for x in HX}
        expected_rh = "0x" + hashlib.sha256(hashlib.sha256(b"\x01" + ldata).digest()).hexdigest()
        cred = self.snap[7]["withdrawalCredentials"]
        ev["withdrawalRequest"] = {"hash": h3, "nonce": nonce + 1, "to": WRC, "feeWei": fee, "valueWei": fee,
                                   "data": "0x" + data.hex(), "receipts": rc3, "log": logs[0] if logs else None,
                                   "logDecoded": {"source": "0x" + ldata[:20].hex(), "pubkey": "0x" + ldata[20:68].hex(),
                                                  "amount": int.from_bytes(ldata[68:76], "big")} if len(ldata) == 76 else None,
                                   "requestsHash": {x: blocks[x].get("requestsHash") for x in HX}, "expectedRequestsHash": expected_rh,
                                   "snapshotCredential": cred, "credentialAddress": "0x" + cred[-40:]}
        slot7002 = (int(blocks["H"]["timestamp"], 16) - self.S) // SLOT
        ev["withdrawalRequest"]["block"] = {"number": int(blocks["H"]["number"], 16), "hash": blocks["H"]["hash"], "leanSlot": slot7002,
                                            "proposerLeanIndex": slot7002 % 7, "builtBy": "X" if slot7002 % 7 == 6 else "H",
                                            "importedBy": "H" if slot7002 % 7 == 6 else "X",
                                            "note": "the importing geth got the block through Ream's engine_newPayloadV4 with "
                                                    "executionRequests; geth recomputes requestsHash from them before the block-hash "
                                                    "check, so the equal hash on both nodes shows Ream carried the request"}
        ok_7002 = (rc3["H"]["status"] == "0x1" and len(logs) == 1 and len(ldata) == 76 and ldata[:20] == owner_b and
                   ldata[20:68] == pk7 and ldata[68:76] == bytes(8) and all(blocks[x].get("requestsHash") == expected_rh for x in HX)
                   and cred.startswith("0x01") and cred[-40:] == OWNER[2:] and blocks["H"]["hash"] == blocks["X"]["hash"])
        last = max(int(r["H"]["blockNumber"], 16) for r in (rc, rc2, rc3))
        fin = L.wait_for(lambda: (lambda f: f if all(f[x]["number"] >= last for x in HX) else None)(
            {x: self.tag(x, "finalized") for x in HX}), 20 * SLOT, 1.0, "finality of the late path")
        canon = {x: [self.rpc(x, "eth_getTransactionReceipt", [t])["blockHash"] for t in (h, h2, h3)] for x in HX}
        accf = {x: self.account(x, "finalized") for x in HX}
        ev.update(finalized=fin, receiptBlocksAtEnd=canon, accountFinalized=accf)
        self.dump("T8-late-path.json", ev)
        self.check("T8.recoveryAfterT", ok_rec, receipt=rc["H"]["status"], account=acc["H"], blockTimestamp=ev["recovery"]["blockTimestamp"])
        self.check("T8.activation", ok_act, receipt=rc2["H"]["status"], account=acc2["H"])
        self.check("T8.eip7002RequestLogRequestsHashSource", ok_7002, log=ev["withdrawalRequest"]["logDecoded"],
                   requestsHash=ev["withdrawalRequest"]["requestsHash"], expected=expected_rh, source=ev["withdrawalRequest"]["credentialAddress"])
        self.check("T7.migrationAfterSIncludedAndFinalized", ok_rec and ok_act and all(fin[x]["number"] >= last for x in HX) and
                   canon["H"] == canon["X"] == [r["H"]["blockHash"] for r in (rc, rc2, rc3)] and accf["H"] == accf["X"] and accf["H"]["activated"],
                   finalized=fin, lastBlock=last)
        self.rec["scenarioTimings"]["T8"]["finishedUnix"] = round(time.time(), 3)

    def sign_tx(self, sender, nonce, to, value=0, data=b"", activate=False, gas=1_500_000):
        """Use the installed wallet wire/signature format for a public-test 0x7c."""
        w, cr = self.w, self.cr
        tx = [CHAIN, sender, nonce, 10**9, 2 * 10**9, gas, to, value, data, [], 1, [self.key.public_key] if activate else [], b""]
        msg = w.PQ_TX_TAG + cr("hash", b"\x7c" + w.wire.rlp(tx))
        tx[12] = cr("sign", self.key.xi, msg, w.PQ_TX_TAG)
        if cr.text("verify", self.key.public_key, msg, w.PQ_TX_TAG, tx[12]) != "true":
            raise ValueError("public test 0x7c signature self-check failed")
        return b"\x7c" + w.wire.rlp(tx)

    # ------------------------------------------------------------------ T6b: X silent
    def x_silent(self):
        if self.a.silent_slots == 0:
            self.rec["silentNotRun"] = "--silent-slots=0 explicitly disabled the X-silent scenario"
            return
        self.rec.setdefault("scenarioTimings", {})["T6b"] = {"startedUnix": round(time.time(), 3)}
        self.save()
        lab = self.lab

        def cl():
            fin = lab.rest("H", "blocks/finalized")
            jus = lab.rest("H", "checkpoints/justified")
            return {"finalizedSlot": int(fin["slot"]), "justified": jus, "el": self.tag("H", "finalized")}
        start = cl()
        stop_requested = time.time()
        stop = lab.stop_ream("X")
        t0 = time.time()
        self.rec["xSilent"] = {"stopRequestedUnix": round(stop_requested, 3), "stoppedUnix": round(t0, 3), "stop": stop}
        samples = []
        end = t0 + self.a.silent_slots * SLOT
        while time.time() < end:
            time.sleep(SLOT / 2)
            try:
                samples.append({"unix": round(time.time(), 3), **cl()})
            except Exception as e:  # noqa: BLE001
                samples.append({"unix": round(time.time(), 3), "error": repr(e)[:200]})
        last = next((s for s in reversed(samples) if "finalizedSlot" in s), None)
        head = self.tag("H", "latest")
        silent_from = math.ceil((t0 - self.S) / SLOT)
        slots = []
        b = head
        while b and b["timestamp"] > t0:
            slots.append((b["timestamp"] - self.S) // SLOT)
            b = self.block("H", b["number"] - 1)
        xslots = [s for s in range(silent_from, (head["timestamp"] - self.S) // SLOT + 1) if s % 7 == 6]
        # Supplement canonical block evidence with H's duty diagnostics.
        import re
        refused, proposed = [], []
        for line in (self.out / "H-ream-1.log").read_text(errors="replace").splitlines():
            line = re.sub(r"\x1b\[[0-9;]*m", "", line)
            m = re.search(r"Coordinated attestation refused: (.*) slot=(\d+)", line)
            if m and int(m.group(2)) >= silent_from:
                refused.append({"slot": int(m.group(2)), "reason": m.group(1)[:120]})
            m = re.search(r"Proposing block by Validator (\d+) slot=(\d+)", line)
            if m and int(m.group(2)) >= silent_from:
                proposed.append(int(m.group(2)))
        just_end = int((last or {}).get("justified", {}).get("slot", 0)) if last else 0
        ev = {"start": start, "samples": samples, "end": last, "stopSlot": round((t0 - self.S) / SLOT, 2),
              "firstSlotAfterStop": silent_from, "blockSlotsWhileSilent": sorted(slots), "xProposerSlots": xslots,
              "hProposalsWhileSilent": proposed, "hAttestationsRefusedWhileSilent": refused,
              "criterion": "a slot that starts after X's stop becomes justified and finalized on H within the window"}
        self.dump("T6b-x-silent.json", ev)
        self.check("T6b.sixOfSevenFinalizeWithXSilent", last is not None and just_end >= silent_from and
                   last["finalizedSlot"] >= silent_from and not set(xslots) & set(slots) and len(xslots) >= 1,
                   firstSlotAfterStop=silent_from, startFinalizedSlot=start["finalizedSlot"],
                   endFinalizedSlot=last and last["finalizedSlot"], endJustifiedSlot=just_end,
                   elFinalized=[start["el"]["number"], (last.get("el") or {}).get("number") if last else None], missedXSlots=xslots,
                   hAttestationsRefused=len(refused), hProposals=len(proposed))
        self.rec["scenarioTimings"]["T6b"]["finishedUnix"] = round(time.time(), 3)

    # ------------------------------------------------------------------ audits after the stop
    def audits(self):
        lab, out = self.lab, self.out / "audit"
        out.mkdir(exist_ok=True)
        res = {}
        for x in HX:
            hp = self.hist[x]
            if not hp.exists():
                continue
            shutil.copyfile(hp, out / f"{x}-final-signing-history.bin")
            q = subprocess.run([str(lab.bin("audit-history")), str(hp)], capture_output=True, text=True, timeout=600,
                               env=dict(os.environ, RAYON_NUM_THREADS="2"))
            (out / f"{x}-history-audit.json").write_text(q.stdout)
            try:
                au = json.loads(q.stdout)
            except ValueError:
                au = {"status": "unparsed", "stderr": q.stderr[-500:]}
            kinds = {}
            for r in au.get("records", []):
                kinds.setdefault("key%s-kind%s" % (r.get("key"), r.get("kind")), []).append(r.get("slot"))
            res[x] = {"exit": q.returncode, "status": au.get("status"), "verifiedSignatures": au.get("verifiedSignatures"),
                      "reservations": au.get("reservations"), "highWater": au.get("highWater"),
                      "recordsByKeyKind": {k: {"count": len(v), "slots": [min(v), max(v)]} for k, v in kinds.items()}}
            db = self.rt / f"audit-db-{x}"
            src = lab.nodes[x]["dir"] / "cl-1"
            if src.exists():
                shutil.copytree(src, db)
                ex = self.rt / f"export-{x}"
                with (self.out / f"{x}-export-signed.log").open("wb") as f:
                    r = subprocess.run([str(lab.bin("export-signed")), str(db), str(ex)], stdout=f, stderr=subprocess.STDOUT,
                                       env=dict(os.environ, RAYON_NUM_THREADS="2"), timeout=1200)
                res[x]["exportExit"] = r.returncode
                if r.returncode == 0:
                    idx = json.loads((ex / "index.json").read_text())
                    shutil.copyfile(ex / "index.json", out / f"{x}-export-index.json")
                    blocks = []
                    for b in idx["blocks"]:
                        j = json.loads((ex / (b["root"] + ".json")).read_text())
                        bb = j["block"]
                        atts = [{"slot": int(at["message"]["slot"]), "validators": bitlist_indices(at["aggregation_bits"])}
                                for at in bb["body"]["attestations"]]
                        ep = bb["body"].get("execution_payload", {})
                        blocks.append({"root": b["root"], "slot": int(bb["slot"]), "proposer": int(bb["proposer_index"]),
                                       "envelopeVerified": b["envelopeVerified"], "qualified": b["qualified"],
                                       "elNumber": int(ep.get("block_number", 0)), "elHash": ep.get("block_hash"),
                                       "txs": len(ep.get("transactions", [])), "attestations": atts})
                    blocks.sort(key=lambda b: b["slot"])
                    (out / f"{x}-export-blocks.json").write_text(json.dumps(blocks, indent=1) + "\n")
                    by6 = [b for b in blocks if b["proposer"] == 6]
                    att6 = [b["slot"] for b in blocks for at in b["attestations"] if at["validators"] and 6 in at["validators"]]
                    res[x]["export"] = {"blocks": len(blocks), "allEnvelopesVerified": all(b["envelopeVerified"] for b in blocks if b["slot"] > 0),
                                        "allQualified": all(b["qualified"] for b in blocks if b["slot"] > 0),
                                        "proposedByLean6": [b["slot"] for b in by6], "blocksCarryingLean6Votes": att6,
                                        "finalized": idx.get("finalized"), "cachedProofs": len(idx.get("cachedProofs", [])),
                                        "cachedProofsPass": all(p.get("verification") == "PASS" for p in idx.get("cachedProofs", []))}
        self.dump("audit/summary.json", res)
        h, xx = res.get("H", {}), res.get("X", {})
        exp = h.get("export", {})
        self.check("T4.nodeXSignaturesAudited", xx.get("status") == "PASS" and (xx.get("verifiedSignatures") or 0) > 0 and
                   h.get("exportExit") == 0 and exp.get("allEnvelopesVerified") and len(exp.get("proposedByLean6", [])) >= 1 and
                   len(exp.get("blocksCarryingLean6Votes", [])) >= 1 and h.get("status") == "PASS",
                   xHistory={k: xx.get(k) for k in ("status", "verifiedSignatures", "recordsByKeyKind")},
                   hExport={k: exp.get(k) for k in ("blocks", "allEnvelopesVerified", "proposedByLean6")},
                   lean6VotesInBlocks=len(exp.get("blocksCarryingLean6Votes", [])))

    def scan_logs(self):
        pats = {"geth": ["Shorten chain", "Chain reorg detected", "Skipping beacon update", "Ignoring beacon update",
                         "Refusing too deep reorg", "Forkchoice requested sync", "Impossible reorg"],
                "ream": ["quarantine", "EL selected forkchoice failed", "FCU target not observed", "anchor unavailable",
                         "ERROR", "panicked", "WARN"]}
        res = {}
        for f in sorted(self.out.glob("*.log")):
            kind = "geth" if f.name.endswith("-geth.log") else "ream" if "-ream-" in f.name else None
            if not kind:
                continue
            text = f.read_text(errors="replace").splitlines()
            res[f.name] = {p: {"count": sum(p in t for t in text), "first": next((t[:300] for t in text if p in t), None)}
                           for p in pats[kind]}
            res[f.name] = {p: v for p, v in res[f.name].items() if v["count"]}
        return res

    # ------------------------------------------------------------------ the end
    def finish(self):
        lab = self.lab
        try:
            for x in HX:
                n = lab.nodes.get(x)
                if n and n.get("ream") is not None and n["ream"].poll() is None:
                    self.rec.setdefault("finalStops", {})[x] = lab.stop_ream(x)
            self.rec["processesStopped"] = lab.stop_all()
        except Exception as e:  # noqa: BLE001
            self.rec["stopError"] = repr(e)
        if self.rec.get("phase1Started"):
            try:
                self.audits()
            except Exception as e:  # noqa: BLE001
                self.rec["auditError"] = traceback.format_exc()[-2000:]
        try:
            self.rec["logScan"] = self.scan_logs()
        except Exception as e:  # noqa: BLE001
            self.rec["logScanError"] = repr(e)
        if hasattr(self, "cr"):
            try:
                self.cr.close()
            except Exception as error:  # noqa: BLE001
                self.rec["cryptoCloseError"] = repr(error)
                try:
                    self.lab.stop(self.cr.proc)
                except Exception as stop_error:  # noqa: BLE001
                    self.rec["cryptoStopError"] = repr(stop_error)
        self.rec["tests"] = self.tests()
        self.save()

    def passed(self):
        """Requested scenarios must complete; skipped optional T8 is explicit."""
        tests = self.rec["tests"]
        return (all(check["pass"] for check in self.rec["checks"].values())
                and all(row["status"] != "FAIL" for row in tests.values())
                and (self.a.silent_slots == 0 or tests["T6b"]["status"] == "PASS")
                and (self.a.recovery_proof is None or tests["T8"]["status"] == "PASS")
                and self.rec.get("processesStopped")
                and not any(self.rec.get(name) for name in ("auditError", "cryptoCloseError", "cryptoStopError", "stopError")))

    def tests(self):
        c = self.rec["checks"]

        def status(prefixes, extra=()):
            names = [k for k in c if k.split(".")[0] in prefixes] + list(extra)
            if not names or any(n not in c for n in extra):
                return {"status": "NOT RUN", "checks": names}
            stamps = [c[n]["unix"] for n in names if "unix" in c[n]]
            return {"status": "PASS" if all(c[n]["pass"] for n in names) else "FAIL", "checks": names,
                    "checkObservations": {"firstUnix": min(stamps), "lastUnix": max(stamps),
                                          "spanSeconds": round(max(stamps) - min(stamps), 3)} if stamps else None}
        t = {"T1": status(("T1",)), "T2": status(("T2",)), "T3": status(("T3", "T3b")), "T4": status(("T4",)),
             "T5": status(("T5",)), "T6": status(("T6",)), "T6b": status(("T6b",)), "T7": status(("T7",)), "T8": status(("T8",), ("T7.migrationAfterSIncludedAndFinalized",)),
             "T9": status(("T9",))}
        required = {"T8": ["T8.recoveryAfterT", "T8.activation", "T8.eip7002RequestLogRequestsHashSource",
                           "T7.migrationAfterSIncludedAndFinalized"],
                    "T6b": ["T6b.sixOfSevenFinalizeWithXSilent"]}
        for name in ("T6b", "T8"):
            timing = self.rec.get("scenarioTimings", {}).get(name)
            t[name]["timing"] = timing
            if timing and ("finishedUnix" not in timing or any(n not in c for n in required[name])):
                t[name]["status"] = "FAIL"
                t[name]["reason"] = "scenario started but did not complete all required checks"
            elif timing:
                timing["seconds"] = round(timing["finishedUnix"] - timing["startedUnix"], 3)
            if t[name]["status"] == "NOT RUN":
                t[name]["notRun"] = self.rec.get("latePathNotRun" if name == "T8" else "silentNotRun",
                                               "run stopped before this scenario")
        t["T8"]["scope"] = "EL recovery, activation and request transport only; no CL exit, withdrawal, re-stake or new membership"
        t["rule7"] = {"status": "VACUOUS (recorded, not tested)", "why": "T0 = S = D_reg, so no migration step precedes S; "
                      "the driver judges finality only by geth's 'finalized' under Ream, and the profile has no light-client path"}
        return t


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--prefix", type=Path, required=True, help="verified installed runtime")
    ap.add_argument("--work", type=Path, required=True, dest="root", help="new directory outside the installation")
    ap.add_argument("--run-id", required=True)
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    ap.add_argument("--lead", type=int, default=90)
    ap.add_argument("--phase0-slots", type=int, default=22, help="slots until the pre-deadline halt")
    ap.add_argument("--delta", type=int, default=180, help="seconds from halt to S = T0 = D_reg")
    ap.add_argument("--t-after-t0", type=int, default=240)
    ap.add_argument("--min-lead", type=int, default=65)
    ap.add_argument("--phase1-timeout", type=int, default=420)
    ap.add_argument("--ream-threads", type=int, default=2)
    ap.add_argument("--silent-slots", type=int, default=10, help="T6b observation window; 0 explicitly skips, otherwise at least 10 slots")
    ap.add_argument("--recovery-proof", type=Path, help="current public-test prove.py output directory for optional T8; never generates a proof")
    a = ap.parse_args()
    a.prefix, a.root = a.prefix.resolve(), a.root.resolve()
    if not a.run_id.isalnum() or a.root.exists() or a.root.is_relative_to(a.prefix) or a.prefix.is_relative_to(a.root):
        ap.error("run-id must be alphanumeric and --work must be a new directory outside --prefix")
    switch_timeline(0, a.phase0_slots, a.delta, a.t_after_t0, a.min_lead)
    if a.lead < 30 or not 1 <= a.ream_threads <= 2 or a.phase1_timeout < 60:
        ap.error("lead >= 30, phase1-timeout >= 60, and 1..2 Ream worker threads are required")
    if a.silent_slots != 0 and a.silent_slots < 10:
        ap.error("silent-slots must be 0 (not run) or at least 10")
    if a.recovery_proof is not None:
        a.recovery_proof = a.recovery_proof.resolve(strict=True)
    sys.path.insert(0, str(a.prefix / "tools"))
    from heavy_job import heavy_job
    with heavy_job(a.lock, owner="n1-checkpoint-switch"):
        run = Switch(a)
        try:
            run.setup()
            run.phase0()
            run.registrations()
            run.tail_and_stop()
            run.checkpoint()
            run.checkpoint_tests()
            run.prepare_phase1()
            run.switch()
            run.rest_reads()
            run.invariants()
            run.late_path()
            run.x_silent()
        except Abort as e:
            run.rec.update(status="ABORTED", failure=str(e))
        except BaseException as e:
            run.rec.update(status="FAIL", failure=type(e).__name__ + ": " + str(e), traceback=traceback.format_exc()[-3000:])
        finally:
            run.finish()
            if run.rec["status"] == "RUNNING":
                run.rec["status"] = "PASS" if run.passed() else "FAIL"
            run.rec["validationScope"] = ("checkpoint switch; T6b=" + run.rec["tests"]["T6b"]["status"]
                                          + "; T8=" + run.rec["tests"]["T8"]["status"]
                                          + "; T8 covers EL recovery/activation/request transport only; no proof generation, CL exit, withdrawal, re-stake or new membership")
            run.rec["keysNote"] = "Never reuse any generated signing keys or signing histories for another genesis."
            files = {p.relative_to(run.out).as_posix(): L.file_sha256(p) for p in run.out.rglob("*")
                     if p.is_file() and not p.is_relative_to(run.rt) and not p.is_relative_to(run.out / "keys") and p.name not in ("result.json", "PUBLIC-MANIFEST.json")}
            run.rec["publicArtifactCount"] = len(files)
            run.save()
            files["result.json"] = L.file_sha256(run.out / "result.json")
            (run.out / "PUBLIC-MANIFEST.json").write_text(json.dumps(files, indent=2, sort_keys=True) + "\n")
            print(json.dumps({k: run.rec.get(k) for k in ("status", "failure", "keysProvisioned", "phase1Started", "processesStopped")}))
        raise SystemExit(0 if run.rec["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
