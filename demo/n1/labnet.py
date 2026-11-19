"""N1 lab: two-node geth + Ream helpers (the run_network.py / row-11 pattern), shared by the switch probe and the
part-2 driver. Uses the installed pq-migrate-lab runtime (prefix/bin wrappers); reads nothing else.
Every port is a fresh loopback port; geth nodes are not peered (pq-lean-fenced-v1 requires net_peerCount == 0).
research lab; not production validation.
"""
import hashlib
import json
import os
import shutil
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

import n1lib as L

CHAIN = 13378          # run identity: L1's chain id and verifier version 0x80000008, kept apart by run id and directory
SLOT = 12


def free_port(udp=False):
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM if udp else socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def port_open(port):
    with socket.socket() as s:
        s.settimeout(1)
        return s.connect_ex(("127.0.0.1", port)) == 0


def network_identity(cl_root, anchor_hash, anchor_state_root, chain=CHAIN):
    """Ream's signing identity: SHA-256('PQ-LEAN-FENCED-v1' || chain_id_be8 || CL root || EL hash || EL state root)."""
    return hashlib.sha256(b"PQ-LEAN-FENCED-v1" + chain.to_bytes(8, "big") + bytes.fromhex(cl_root[2:]) +
                          bytes.fromhex(anchor_hash[2:]) + bytes.fromhex(anchor_state_root[2:])).hexdigest()


class Lab:
    def __init__(self, prefix, out, record):
        self.prefix = Path(prefix)
        self.out = Path(out)
        self.record = record
        self.processes, self.files = [], []
        self.nodes = {}

    # ---------------------------------------------------------------- bookkeeping
    def save(self):
        (self.out / "result.json").write_text(json.dumps(self.record, indent=1, default=str) + "\n")

    def step(self, name, **kw):
        kw.update(step=name, unix=round(time.time(), 3))
        self.record.setdefault("steps", []).append(kw)
        self.save()
        print(json.dumps({k: v for k, v in kw.items() if k in ("step", "note", "slot", "unix")}), flush=True)

    def bin(self, name):
        return self.prefix / "bin" / name

    def command(self, label, argv, timeout=600, env=None):
        e = dict(os.environ, RAYON_NUM_THREADS="2", TOKIO_WORKER_THREADS="2")
        e.update(env or {})
        q = subprocess.run(list(map(str, argv)), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, env=e)
        (self.out / (label + ".log")).write_bytes(q.stdout)
        self.record.setdefault("commands", []).append({"label": label, "argv": list(map(str, argv)), "exit": q.returncode})
        self.save()
        assert q.returncode == 0, (label, q.returncode, q.stdout[-600:])
        return q.stdout.decode().strip()

    def spawn(self, label, argv, env=None):
        f = (self.out / (label + ".log")).open("wb")
        self.files.append(f)
        e = {k: os.environ[k] for k in ("HOME", "PATH", "LANG") if k in os.environ}
        e.update(RAYON_NUM_THREADS="2", TOKIO_WORKER_THREADS="2", GOMAXPROCS="2", RUST_BACKTRACE="1")
        e.update(env or {})
        p = subprocess.Popen(list(map(str, argv)), stdout=f, stderr=subprocess.STDOUT, env=e)
        self.processes.append(p)
        self.record.setdefault("commands", []).append({"label": label, "argv": list(map(str, argv)), "pid": p.pid,
                                                       "env": dict(env or {}), "unix": round(time.time(), 3)})
        self.save()
        return p

    @staticmethod
    def stop(p, timeout=20):
        t = time.time()
        if p.poll() is None:
            p.terminate()
            try:
                p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                p.kill()
                p.wait(timeout=10)
        return round(time.time() - t, 3), p.returncode

    def stop_ream(self, name, timeout=30):
        """Ream handles Ctrl-C (SIGINT) in main.rs and exits 0; SIGTERM was ignored for 20 s in probe run sw1."""
        p = self.nodes[name]["ream"]
        t = time.time()
        if p.poll() is None:
            p.send_signal(signal.SIGINT)
            try:
                p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                p.kill()
                p.wait(timeout=10)
        return round(time.time() - t, 3), p.returncode

    def stop_all(self):
        for n in self.nodes.values():          # Ream first, gracefully, then everything else
            if n.get("ream") is not None and n["ream"].poll() is None:
                self.stop_ream(n["name"])
        for p in reversed(self.processes):
            self.stop(p)
        for f in self.files:
            f.close()
        return all(p.poll() is not None for p in self.processes)

    # ---------------------------------------------------------------- keys and genesis
    def fresh_keys(self, directory, seed_file):
        """Fresh public leanXMSS key pair (attestation, proposal; activation 0..2^18) with the packaged keygen."""
        Path(seed_file).write_bytes(os.urandom(64))
        Path(seed_file).chmod(0o600)
        self.command("keygen-" + Path(directory).name, [self.bin("fresh-public-keys"), directory, seed_file], timeout=900,
                     env={"RAYON_NUM_THREADS": "2"})
        return {r: "0x" + (Path(directory) / (r + ".pub")).read_bytes().hex() for r in ("attestation", "proposal")}

    def el_genesis(self, genesis_time, t0, t, extra_alloc=None):
        """Lab template + pqMigrate (run_network.py l. 70-82 pattern) with chain id 13378 and verifier 0x80000008."""
        share = self.prefix / "share"
        g = json.loads((share / "templates/generator-el-genesis.json").read_text())
        profile = json.loads((share / "identity/lean-migration-profile.json").read_text())
        pm = json.loads((share / "templates/migration-genesis.json").read_text())["config"]["pqMigrate"]
        pm.update(t0=t0, t=t, receivingTime=t0)
        pm["fullResearch"].update({k: profile[k] for k in ("version", "backend", "nativeAlgorithmDigest", "finalKeyDigest",
                                                           "maxProofBytes", "maxTxBytes", "imageId", "guestSha", "verifierSha",
                                                           "verifyGas")})
        pm["fullResearch"]["activation"] = t0
        g["config"]["pqMigrate"] = pm
        g["config"]["chainId"] = CHAIN
        g["timestamp"] = hex(genesis_time)
        for k, v in (extra_alloc or {}).items():
            g["alloc"][k[2:] if k.startswith("0x") else k] = v
        return g

    def lean_genesis(self, keydirs, genesis_time, label):
        """CL genesis root of the validator list (keydirs in Lean index order) through profile-tool-three."""
        argv = [self.bin("profile-tool-three"), "genesis", keydirs[0], str(genesis_time)] + list(keydirs[1:])
        return json.loads(self.command(label, argv))

    # ---------------------------------------------------------------- nodes
    def start_geth(self, name, genesis_path, rundir):
        d = Path(rundir) / name
        d.mkdir(parents=True, exist_ok=True)
        secret = os.urandom(32).hex()
        (d / "jwt").write_text(secret)
        (d / "jwt").chmod(0o600)
        n = {"name": name, "dir": d, "jwtsecret": secret, "rpc": free_port(), "engine": free_port(), "elport": free_port()}
        self.command(name + "-init", [self.bin("geth"), "--datadir", d / "el", "--state.scheme=hash", "init", genesis_path])
        n["gethargs"] = [self.bin("geth"), f"--datadir={d}/el", "--state.scheme=hash", "--syncmode=full", "--gcmode=archive",
                         "--snapshot=false", "--cache=256", "--maxpeers=0", "--nodiscover", "--bootnodes=", "--nat=none",
                         f"--port={n['elport']}", "--ipcdisable", "--http", "--http.addr=127.0.0.1", f"--http.port={n['rpc']}",
                         "--http.vhosts=localhost,127.0.0.1", "--http.api=eth,net,web3,pqpool,debug,txpool",
                         "--authrpc.addr=127.0.0.1", f"--authrpc.port={n['engine']}", "--authrpc.vhosts=localhost,127.0.0.1",
                         f"--authrpc.jwtsecret={d}/jwt", "--miner.gasprice=1", "--verbosity=3", "--log.format=json"]
        n["geth"] = self.spawn(name + "-geth", n["gethargs"], {"PQ_LEAN_FENCE_PATH": str(d / "signing-fence")})
        n["url"] = f"http://127.0.0.1:{n['rpc']}"
        n["engineUrl"] = f"http://127.0.0.1:{n['engine']}"
        n["genesisBlock"] = L.wait_for(lambda: L.rpc(n["url"], "eth_getBlockByNumber", ["0x0", False]), 60, what=name + " geth")
        self.nodes[name] = n
        return n

    def start_material_server(self, name, round_):
        n = self.nodes[name]
        port = free_port()
        directory = n["dir"] / f"public-materials-{round_}"
        directory.mkdir()
        n["material"], n["materials"] = port, directory
        n["server"] = self.spawn(f"{name}-material-server-{round_}", [sys.executable, self.prefix / "tools/lean/material_server.py",
                                                                      "--directory", directory, "--port", str(port)])
        L.wait_for(lambda: port_open(port), 30, 0.2, name + " material server")

    def prepare_ream(self, name, round_, *, network_yaml, registry_yaml, cl_root, anchor, signer_cfg, peer):
        """Fresh data dir, node key, session and engine config for one Ream process (a new Lean chain each round)."""
        n = self.nodes[name]
        d = n["dir"]
        n["p2p"], n["rest"] = free_port(True), free_port()
        key = d / f"node-key-{round_}"
        anyd = Path(json.loads(Path(registry_yaml).read_text())[name][0]["privkey_file"]).parent
        n["peerid"] = self.command(f"{name}-network-identity-{round_}", [self.bin("profile-tool"), "peer", anyd, key])
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

    def start_ream(self, name, bootnode=None):
        n = self.nodes[name]
        d, r = n["dir"], n["round"]
        boot = "none"
        if bootnode:
            b = self.nodes[bootnode]
            boot = f"/ip4/127.0.0.1/udp/{b['p2p']}/quic-v1/p2p/{b['peerid']}"
        argv = n["reamargs"] + ["--bootnodes", boot, "--is-aggregator"]
        n["ream"] = self.spawn(f"{name}-ream-{r}", argv, {"PQ_MIGRATE_EXTERNAL_ENGINE_CONFIG": str(d / f"engine-{r}.json"),
                                                         "PQ_REAM_SIGNER_CONFIG": str(d / f"signer-{r}.json")})

    def rest(self, name, path):
        import urllib.request
        n = self.nodes[name]
        req = urllib.request.Request(f"http://127.0.0.1:{n['rest']}/lean/v0/{path}", headers={"Accept": "application/json"})
        with urllib.request.urlopen(req, timeout=4) as r:
            return json.load(r)

    def el(self, name, tag="latest"):
        return L.rpc(self.nodes[name]["url"], "eth_getBlockByNumber", [tag, False])


def write_registry(path, layout):
    """Ream's annotated registry (JSON is YAML): {node: [attester entry, proposer entry] per Lean index}."""
    reg = {}
    for node, entries in layout.items():
        reg[node] = []
        for e in entries:
            for role in ("attestation", "proposal"):
                reg[node].append({"index": e["index"], "pubkey_hex": e[role], "privkey_file": str(Path(e["dir"]) / (role + ".ssz"))})
    Path(path).write_text(json.dumps(reg, indent=1))
    return reg


def write_network(path, genesis_time, validators):
    net = {"GENESIS_TIME": genesis_time, "NUM_VALIDATORS": len(validators),
           "GENESIS_VALIDATORS": [{"attestation_public_key": v["attestation"], "proposal_public_key": v["proposal"]}
                                  for v in validators], "SECONDS_PER_SLOT": SLOT, "JUSTIFICATION_LOOKBACK_SLOTS": 3}
    Path(path).write_text(json.dumps(net, indent=2))
    return net


def copy_keys(src, dst):
    Path(dst).mkdir(parents=True)
    for f in ("attestation.pub", "proposal.pub", "attestation.ssz", "proposal.ssz"):
        shutil.copyfile(Path(src) / f, Path(dst) / f)
