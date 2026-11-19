"""Dependency-free, KAT-verified Keccak-256 (Ethereum flavour).

Ethereum's ``keccak256`` is the *original* Keccak submission (pad10*1 with a
``0x01`` domain suffix), NOT NIST FIPS-202 SHA3-256 (which uses ``0x06``).
Python's ``hashlib.sha3_256`` therefore produces the WRONG digest for Ethereum
address derivation (``last20(keccak256(pubkey))``). This module implements the
Keccak-f[1600] permutation in pure Python so the executable specification and
its fixtures have zero external dependencies and are byte-identical to what a
Geth/Reth client computes.

A self-test (known-answer test / KAT) runs at import time; if the permutation
were ever mis-transcribed the module refuses to load rather than emit silent
wrong roots.

Reference: NIST FIPS-202 (Keccak) and the Ethereum Yellow Paper appendix on the
KEC hash. Round constants and rotation offsets are the standard Keccak values.
"""

from __future__ import annotations

_MASK64 = (1 << 64) - 1

# Keccak-f[1600] round constants (iota step), 24 rounds.
_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]

# rho rotation offsets, in the order the pi-permutation visits lanes.
_ROTC = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
         27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44]

# pi lane permutation (destination lane index for each rho step).
_PILN = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
         15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1]


def _rotl64(x: int, n: int) -> int:
    return ((x << n) | (x >> (64 - n))) & _MASK64


def _keccak_f(st: list[int]) -> None:
    """In-place Keccak-f[1600] on 25 little-endian 64-bit lanes."""
    for rnd in range(24):
        # theta
        bc = [st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20] for i in range(5)]
        for i in range(5):
            t = bc[(i + 4) % 5] ^ _rotl64(bc[(i + 1) % 5], 1)
            for j in range(0, 25, 5):
                st[j + i] ^= t
        # rho + pi
        t = st[1]
        for i in range(24):
            j = _PILN[i]
            prev = st[j]
            st[j] = _rotl64(t, _ROTC[i])
            t = prev
        # chi
        for j in range(0, 25, 5):
            row = st[j:j + 5]
            for i in range(5):
                st[j + i] ^= (~row[(i + 1) % 5]) & row[(i + 2) % 5]
        # iota
        st[0] ^= _RC[rnd]


def _keccak(rate_bytes: int, data: bytes, suffix: int, out_bytes: int) -> bytes:
    st = [0] * 25
    m = bytearray(data)
    m.append(suffix)
    while len(m) % rate_bytes != 0:
        m.append(0)
    m[-1] |= 0x80
    for off in range(0, len(m), rate_bytes):
        block = m[off:off + rate_bytes]
        for i in range(rate_bytes // 8):
            st[i] ^= int.from_bytes(block[i * 8:i * 8 + 8], "little")
        _keccak_f(st)
    out = bytearray()
    while len(out) < out_bytes:
        for i in range(rate_bytes // 8):
            out += st[i].to_bytes(8, "little")
            if len(out) >= out_bytes:
                break
        if len(out) < out_bytes:
            _keccak_f(st)
    return bytes(out[:out_bytes])


def keccak256(data: bytes) -> bytes:
    """Ethereum keccak256: rate 1088 bits (136 bytes), 0x01 suffix, 32-byte out."""
    return _keccak(136, data, 0x01, 32)


def keccak256_hex(data: bytes) -> str:
    return "0x" + keccak256(data).hex()


# --- Known-answer tests (fail-closed at import) -----------------------------
_KATS = {
    b"": "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
    b"abc": "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45",
    b"testing": "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02",
}
for _msg, _want in _KATS.items():
    _got = keccak256(_msg).hex()
    if _got != _want:  # pragma: no cover - integrity guard
        raise RuntimeError(
            f"keccak256 KAT failed for {_msg!r}: got {_got}, want {_want}"
        )

if __name__ == "__main__":
    print("keccak256 self-test PASS")
    print("keccak256('') =", keccak256_hex(b""))
    print("keccak256('abc') =", keccak256_hex(b"abc"))
