"""N1 registry: reproduce its CC0-1.0 Solidity runtime with solc 0.8.28, or emit a genesis allocation.

The contract verifies no signature; checkpoint.py verifies registrations off chain.
The checked-in runtime is preserved byte for byte from the research source."""
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import n1lib as L  # noqa: E402

SOURCE = HERE / "contracts/N1Registry.sol"
RUNTIME = HERE / "contracts/N1Registry.bin-runtime"
SOLC = shutil.which("solc")
FORBIDDEN = {0xF0: "CREATE", 0xF1: "CALL", 0xF2: "CALLCODE", 0xF4: "DELEGATECALL", 0xF5: "CREATE2", 0xFA: "STATICCALL",
             0xFF: "SELFDESTRUCT"}
NAMES = {0x20: "KECCAK256", 0x36: "CALLDATASIZE", 0x35: "CALLDATALOAD", 0x37: "CALLDATACOPY", 0x42: "TIMESTAMP",
         0x54: "SLOAD", 0x55: "SSTORE", 0x34: "CALLVALUE", 0xA0: "LOG0", 0xA1: "LOG1", 0xA2: "LOG2", 0xA3: "LOG3",
         0xA4: "LOG4", 0xFD: "REVERT", 0xF3: "RETURN", 0x00: "STOP"}


def runtime_hex():
    return RUNTIME.read_text().strip()


def disassemble(code):
    """Instruction list up to the CBOR metadata (its length is in the last two bytes)."""
    meta = int.from_bytes(code[-2:], "big") + 2
    body, ins, pc = code[:-meta], [], 0
    while pc < len(body):
        op = body[pc]
        if 0x60 <= op <= 0x7F:
            n = op - 0x5F
            ins.append((pc, op, body[pc + 1:pc + 1 + n]))
            pc += 1 + n
        else:
            ins.append((pc, op, b""))
            pc += 1
    return ins, code[-meta:]


def shifted_constants(ins):
    """Values of the pattern PUSH a, PUSH1 s, SHL: the optimizer stores revert strings as (a << s), left-aligned."""
    out = set()
    for k in range(len(ins) - 2):
        (_, o1, a), (_, o2, s), (_, o3, _) = ins[k], ins[k + 1], ins[k + 2]
        if a and o2 == 0x60 and o3 == 0x1B:
            out.add(((int.from_bytes(a, "big") << s[0]) % 2**256).to_bytes(32, "big"))
    return out


def check(code):
    ins, meta = disassemble(code)
    ops = [op for _, op, _ in ins]
    pushes = [arg for _, op, arg in ins if arg]
    topic = bytes.fromhex(L.REGISTERED_TOPIC[2:])
    counts = {NAMES[o]: ops.count(o) for o in NAMES if ops.count(o)}
    reasons = shifted_constants(ins)
    checks = {
        "noExternalCallCreateOrSelfdestruct": not any(o in FORBIDDEN for o in ops),
        "onlyLog3": counts.get("LOG3", 0) == 1 and not any(counts.get(x, 0) for x in ("LOG0", "LOG1", "LOG2", "LOG4")),
        "pushesRegisteredTopic": topic in pushes,
        "pushesPayloadLength312": (312).to_bytes(2, "big") in pushes,
        "readsTimestampAndCalldataSize": counts.get("TIMESTAMP", 0) >= 1 and counts.get("CALLDATASIZE", 0) >= 1,
        "hashesWithKeccak": counts.get("KECCAK256", 0) >= 2,
        "twoStorageWrites": counts.get("SSTORE", 0) == 2,              # acc (slot 1) and count (slot 2); slot 0 never
        "revertsWithReasons": all((s + b"\x00" * 32)[:32] in reasons for s in (b"N1: after D_reg", b"N1: length")),
        "metadataIsCbor": meta[:1] == b"\xa2" and b"solc" in meta,
    }
    return checks, {"instructions": len(ins), "opcodeCounts": counts, "metadataBytes": len(meta),
                    "solcVersionInMetadata": meta[-5:-2].hex()}


def build(out, solc):
    out.mkdir(parents=True, exist_ok=True)
    rec = {"review": "research lab; not production validation", "source": "contracts/N1Registry.sol",
           "sourceSHA256": L.file_sha256(SOURCE), "checkedInRuntimeSHA256": hashlib.sha256(runtime_hex().encode()).hexdigest()}
    if not solc or not Path(solc).is_file():
        raise ValueError("solc 0.8.28 is required for build; pass --solc PATH")
    with tempfile.TemporaryDirectory(prefix="n1-solc-") as tmp:
        shutil.copyfile(SOURCE, Path(tmp) / "N1Registry.sol")   # the metadata hash covers the bare file name
        argv = [solc, "--optimize", "--bin-runtime", "N1Registry.sol"]
        q = subprocess.run(argv, cwd=tmp, capture_output=True, text=True, timeout=120)
        ver = subprocess.run([solc, "--version"], capture_output=True, text=True, timeout=30).stdout.strip().splitlines()[-1]
    if q.returncode != 0 or "0.8.28" not in ver:
        raise ValueError("solc 0.8.28 build failed: " + q.stderr[-500:])
    built = q.stdout.strip().splitlines()[-1].strip()
    rec["solc"] = {"path": solc, "sha256": L.file_sha256(solc), "version": ver, "argv": argv[1:], "exit": q.returncode}
    rec["builtRuntimeSHA256"] = hashlib.sha256(built.encode()).hexdigest()
    rec["reproduced"] = built == runtime_hex()
    code = bytes.fromhex(runtime_hex())
    checks, summary = check(code)
    rec.update(runtimeBytes=len(code), runtimeKeccak="0x" + L.keccak(code).hex(), disassembly=summary, checks=checks)
    rec["status"] = "PASS" if rec["reproduced"] is not False and all(checks.values()) else "FAIL"
    (out / "registry-build.json").write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps({"status": rec["status"], "reproduced": rec["reproduced"], "runtimeBytes": len(code),
                      "checks": checks}))
    return rec["status"] == "PASS"


def genesis_entry(dreg):
    return {L.REGISTRY_ADDRESS: {"balance": "0", "nonce": "1", "code": "0x" + runtime_hex(),
                                 "storage": {"0x" + "00" * 32: "0x" + int(dreg).to_bytes(32, "big").hex()}}}


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build")
    b.add_argument("--out", type=Path, required=True)
    b.add_argument("--solc", default=SOLC)
    e = sub.add_parser("entry")
    e.add_argument("--dreg", type=int, required=True)
    a = ap.parse_args()
    if a.cmd == "build":
        raise SystemExit(0 if build(a.out, a.solc) else 1)
    print(json.dumps(genesis_entry(a.dreg), indent=1))


if __name__ == "__main__":
    main()
