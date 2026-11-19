#!/usr/bin/env python3
"""Generate L0-prime -> B -> F using in-memory witness and inner proofs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid
import resource
from custody import MemoryArtifacts
import statement

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True


def available_kib():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1])
    raise RuntimeError("MemAvailable is unavailable")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", type=Path, required=True)
    ap.add_argument("--input", required=True, help="- reads owner JSON from stdin; files are public-test data only")
    ap.add_argument("--keep-inner", action="store_true", help="retain inner proofs only for explicitly public test data")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--lifetime", type=int, default=3 * 86400)
    ap.add_argument("--expiry", type=int, help="fixed current expiry for a repeated-statement benchmark")
    ap.add_argument("--lock", type=Path, default=Path.home() / "pq-heavy-job.lock")
    a = ap.parse_args()
    if not 3600 <= a.lifetime <= 7 * 86400:
        ap.error("lifetime must be between one hour and seven days")
    build = a.build.resolve()
    manifest = json.loads((build / "BUILD.json").read_text())
    if manifest["status"] != "PASS":
        raise ValueError("the prover build did not pass")
    for name, expected in manifest["binaries"].items():
        if hashlib.sha256((build / "bin" / name).read_bytes()).hexdigest() != expected:
            raise ValueError("tool hash mismatch: " + name)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    inp = statement.read_input(a.input)
    public_test = inp.get("credential", {}).get("public") is True
    if a.keep_inner and not public_test:
        raise ValueError("--keep-inner requires explicitly public test data")
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "logs").mkdir()
    memory = MemoryArtifacts()
    memory.add("inputs/vk.json", (ROOT / "prover/keys/leaf.json").read_bytes())
    for layer, names in {"leaf": ["l0p2.postcard", "vk.json", "metrics.json", "statement.json", "verification.json"],
                         "b": ["proof.postcard", "statement.json", "report.json", "breakdown.json", "verification.json"],
                         "f": ["proof.postcard", "statement.json", "report.json", "breakdown.json", "verification.json"]}.items():
        for name in names:
            memory.add(layer + "/" + name)
    record = {"status": "WAITING", "review": "loop-internal self-review; not independently reviewed",
              "publicTestOnly": public_test, "keepInner": a.keep_inner, "custody": "anonymous-memory; only F exported by default", "commands": []}
    token = str(uuid.uuid4())
    owned = False

    def save():
        (out / "PROOF.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(name, args, minimum=0, limit=0, extra=None, expected_exit=0, stdin=None):
        if minimum and available_kib() < minimum * 1024**2:
            raise RuntimeError(f"{name} requires {minimum} GiB available RAM")
        if minimum >= 40:
            others = []
            for path in Path("/proc").glob("[0-9]*/status"):
                try:
                    rss = next((int(l.split()[1]) for l in path.read_text().splitlines() if l.startswith("VmRSS:")), 0)
                    if rss > 1024**2 and int(path.parent.name) != os.getpid():
                        others.append(int(path.parent.name))
                except (OSError, ValueError):
                    pass
            if others:
                raise RuntimeError(f"{name}: another process exceeds 1 GiB RSS")
        start = time.monotonic()
        killed = False
        peak = 0
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", **memory.environment())
        env.update(extra or {})
        captures = [os.memfd_create("pq-custody-diagnostic", os.MFD_CLOEXEC) for _ in range(3)]
        try:
            proc = subprocess.Popen(["/usr/bin/time", "-v", "-o", f"/proc/self/fd/{captures[2]}", *map(str, args)],
                                    env=env, stdin=subprocess.PIPE, stdout=captures[0], stderr=captures[1],
                                    pass_fds=tuple(memory.fds.values()) + tuple(captures), start_new_session=True)
            try:
                # Only the small leaf witness enters stdin; inner proofs use inherited anonymous descriptors.
                if stdin:
                    proc.stdin.write(stdin)
                proc.stdin.close()
                while proc.poll() is None:
                    try:
                        children = Path(f"/proc/{proc.pid}/task/{proc.pid}/children").read_text().split()
                        rss = 0
                        for child in children:
                            text = Path(f"/proc/{child}/status").read_text()
                            rss += next((int(l.split()[1]) for l in text.splitlines() if l.startswith("VmRSS:")), 0)
                        peak = max(peak, rss)
                        if limit and rss > limit * 1024**2:
                            killed = True
                            os.killpg(proc.pid, signal.SIGKILL)
                    except (OSError, ValueError):
                        pass
                    time.sleep(0.2)
                code = proc.wait()
            except BaseException:
                if proc.poll() is None:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                raise
            # time's report contains no witness. Raw child diagnostics may contain
            # assertion operands and must stay in memory on the owner path.
            timing = os.pread(captures[2], os.fstat(captures[2]).st_size, 0)
            (out / "logs" / (name + ".time")).write_bytes(timing)
            if a.keep_inner:
                for fd, suffix in zip(captures[:2], ["out", "err"]):
                    (out / "logs" / (name + "." + suffix)).write_bytes(os.pread(fd, os.fstat(fd).st_size, 0))
        finally:
            for fd in captures:
                os.close(fd)
        record["commands"].append({"name": name, "exit": code, "seconds": time.monotonic() - start,
                                   "watchdogPeakKiB": peak, "watchdogKilled": killed})
        save()
        if killed or code != expected_exit:
            raise RuntimeError(name + " failed; see logs")
        print(name + ": PASS", flush=True)

    try:
        while not owned:
            try:
                with a.lock.open("x") as file:
                    json.dump({"owner": "pq-migrate-lab-prover", "pid": os.getpid(), "token": token}, file)
                owned = True
            except FileExistsError:
                save()
                print("Waiting for the shared heavy-job lock", flush=True)
                time.sleep(10)
        expiry = a.expiry if a.expiry is not None else int(time.time()) + a.lifetime
        if not int(time.time()) + 3600 <= expiry <= int(time.time()) + 7 * 86400:
            raise ValueError("expiry must still be between one hour and seven days ahead")
        inp["pi"].pop("expiry_utc", None)
        inp["pi"]["expiry"] = expiry
        if inp["pi"]["fee_mode"] in (1, 3) and inp["pi"].get("fee_auth_until") in (None, "expiry"):
            inp["pi"]["fee_auth_until"] = expiry
        record.update(status="RUNNING", expiry=expiry)
        tool = build / "bin"
        keys = ROOT / "prover/keys"
        witness, public, public_key = statement.prepare(inp, ROOT, tool / "pq-test-crypto", manifest["binaries"]["pq-test-crypto"])
        del inp
        statement.save_public(out / "statement", public, public_key)
        pi = out / "statement/pi198.hex"
        memory.add("relation/fixtures/pi198.hex", pi.read_bytes())
        inputs, leaf, bdir, fdir = [memory.path(x) for x in ["inputs", "leaf", "b", "f"]]
        run("leaf-prove", [tool / "pq-migrate-leaf", "prove-statement", "--input", "-",
                           "--vk", keys / "leaf.json", "--out", leaf], 24, 33, {"RAYON_NUM_THREADS": "8"},
                           stdin=json.dumps(witness).encode())
        del witness
        run("leaf-verify", [tool / "pq-migrate-leaf", "verify-statement", "--dir", leaf, "--vk", keys / "leaf.json",
                            "--pi", pi, "--out", leaf / "verification.json"], 24, 33)
        if memory.document("leaf/verification.json")["verdict"] != "ACCEPTED":
            raise ValueError("fresh leaf verification rejected the proof")
        run("b-prove", [tool / "pq-migrate-tree", "b-prove-statement", "--in", inputs, "--child-dir", leaf,
                        "--vk", keys / "b.json", "--out", bdir], 40, 33)
        run("b-verify", [tool / "pq-migrate-tree", "verify", "--child", "l0p2", "--in", inputs, "--vk", keys / "b.json",
                         "--dir", bdir, "--out", bdir / "verification.json"], 24, 33)
        if memory.document("b/verification.json")["verdict"] != "ACCEPTED":
            raise ValueError("fresh B verification rejected the proof")
        if bytes(memory.document("b/statement.json")["public_values"]) != bytes.fromhex(public["pi198_hex"]):
            raise ValueError("B's verified public values differ from this run's expected PI")
        record["bPublicValuesEqualExpectedPI"] = True
        run("f-prove", [tool / "pq-migrate-tree", "f-prove", "--variant", "P", "--in", inputs, "--b-vk", keys / "b.json",
                        "--b-dir", bdir, "--f-vk", keys / "f.json", "--out", fdir], 48, 44)
        run("f-verify", [tool / "pq-migrate-tree", "f-verify", "--in", inputs, "--b-vk", keys / "b.json",
                         "--f-vk", keys / "f.json", "--dir", fdir, "--out", fdir / "verification.json"], 24, 33)
        if memory.document("f/verification.json")["verdict"] != "ACCEPTED":
            raise ValueError("fresh F verification rejected the proof")
        # No witness-dependent reports/trace hashes or inner openings are exported.
        record["layers"] = {}
        for layer, filename in [("leaf", "metrics.json"), ("b", "report.json"), ("f", "report.json")]:
            metrics = memory.document(layer + "/" + filename)
            record["layers"][layer] = {"prove_ms": metrics.get("prove_ms", metrics.get("timings_ms", {}).get("prove")),
                                      "proof_bytes": metrics["proof_bytes"], "fresh_verdict": "ACCEPTED"}
        (out / "f").mkdir()
        proof = out / "f/proof.postcard"
        proof.write_bytes(memory.read("f/proof.postcard"))
        if a.keep_inner:
            for virtual in memory.fds:
                rel = Path(virtual).relative_to("/pq-memory")
                if rel.parts[0] in ("leaf", "b", "f") and rel != Path("f/proof.postcard"):
                    dest = out / rel
                    dest.parent.mkdir(exist_ok=True)
                    dest.write_bytes(memory.read(str(rel)))
        run("standalone", [tool / "pq-final-verify", "--proof", proof, "--pi", pi, "--repeat", "1"])
        changed_pi = bytearray.fromhex(pi.read_text().strip())
        changed_pi[84] ^= 1
        mutation_pi = memory.add("changed-pi.hex", changed_pi.hex().encode() + b"\n")
        changed_proof = bytearray(proof.read_bytes())
        changed_proof[-1] ^= 1
        mutation_proof = memory.add("changed-proof.postcard", changed_proof)
        pi_fd = Path(f"/proc/self/fd/{memory.fds[str(mutation_pi)]}")
        proof_fd = Path(f"/proc/self/fd/{memory.fds[str(mutation_proof)]}")
        run("reject-changed-pi", [tool / "pq-final-verify", "--proof", proof, "--pi", pi_fd], expected_exit=1)
        run("reject-changed-proof", [tool / "pq-final-verify", "--proof", proof_fd, "--pi", pi], expected_exit=1)
        if proof.stat().st_size > 196608:
            raise ValueError("final proof exceeds the fixed on-chain cap")
        record.update(status="PASS", proofBytes=proof.stat().st_size,
                      proofSHA256=hashlib.sha256(proof.read_bytes()).hexdigest(),
                      piSHA256=hashlib.sha256(bytes.fromhex(pi.read_text().strip())).hexdigest())
    except BaseException as error:
        record.update(status="FAIL", failure=type(error).__name__ + ": details suppressed for credential custody")
        raise RuntimeError("proving failed; see non-secret PROOF.json status") from None
    finally:
        memory.close()
        save()
        if owned and a.lock.exists() and json.loads(a.lock.read_text()).get("token") == token:
            a.lock.unlink()


if __name__ == "__main__":
    try:
        main()
    except (Exception, SystemExit) as error:
        if isinstance(error, SystemExit) and error.code == 0:
            raise
        raise SystemExit("proving did not complete; credential details suppressed") from None
