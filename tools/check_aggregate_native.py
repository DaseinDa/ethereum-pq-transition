#!/usr/bin/env python3
"""Exercise the real C ABI against the frozen genuine four-owner fixture."""
import argparse
import ctypes
import hashlib
import json
from pathlib import Path

from aggregate_support import C_KEY, MAX_CARRIER


def check(library, fixture):
    lib = ctypes.CDLL(str(Path(library).resolve()))
    lib.pq_aggregate_ready_v1.restype = ctypes.c_int32
    lib.pq_aggregate_key_v1.restype = ctypes.c_char_p
    lib.pq_aggregate_verify.restype = ctypes.c_int32
    lib.pq_aggregate_verify.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p, ctypes.c_size_t]
    if lib.pq_aggregate_key_v1().decode("ascii") != C_KEY or lib.pq_aggregate_ready_v1() != 0:
        raise RuntimeError("aggregate native readiness/key mismatch")
    proof = (fixture / "carrier.bin").read_bytes()
    statement = (fixture / "statement.bin").read_bytes()
    def verify(p, s):
        pb, sb = ctypes.create_string_buffer(p), ctypes.create_string_buffer(s)
        return lib.pq_aggregate_verify(pb, len(p), sb, len(s))
    if verify(proof, statement) != 0:
        raise AssertionError("genuine aggregate fixture rejected")
    cases = []
    def reject(name, p, s):
        code = verify(p, s)
        if code not in (1, 2):
            raise AssertionError(f"{name}: expected invalid input/proof, got {code}")
        cases.append({"case": name, "code": code})
    # Every byte, covering all 12 PI fields for every owner and both header fields.
    for offset in range(len(statement)):
        altered = bytearray(statement)
        altered[offset] ^= 1
        reject(f"statement-byte-{offset}", proof, bytes(altered))
    reject("entry-order", proof, statement[:6] + statement[204:402] + statement[6:204] + statement[402:])
    for name, changed in [("statement-short", statement[:-1]), ("statement-trailing", statement + b"\0"),
                          ("digest-only", hashlib.sha256(statement).digest())]:
        reject(name, proof, changed)
    reject("empty-proof", b"", statement)
    reject("advice-only", proof[:256], statement)
    reject("truncated-proof", proof[:-1], statement)
    reject("trailing-proof", proof + b"\0", statement)
    reject("oversized-proof", proof + bytes(MAX_CARRIER + 1 - len(proof)), statement)
    reject("noncanonical-advice", b"\xff" * 4 + proof[4:], statement)
    for offset in (0, 32, 64, 128, 192, 256, len(proof) - 1):
        altered = bytearray(proof)
        altered[offset] ^= 1
        reject(f"carrier-byte-{offset}", bytes(altered), statement)
    if lib.pq_aggregate_verify(None, 0, None, 0) != 1:
        raise AssertionError("null pointer input was not classified invalid")
    return {"status": "PASS", "key": C_KEY, "genuineFixtureAccepted": True,
            "negativeCases": cases, "nullPointersRejected": True,
            "review": "loop-internal self-review; not independently reviewed"}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--fixture", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    result = check(a.library, a.fixture)
    with a.out.open("x", encoding="utf-8") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "negativeCases": len(result["negativeCases"])}))


if __name__ == "__main__":
    main()
