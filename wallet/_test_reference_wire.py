"""Independent canonical RLP reference for synthetic wallet tests only.

No signatures or proofs are verified and no state/gas rules run here. Bounds
belong to this test harness and are not production limits.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass

from _test_reference_keccak import keccak256

TYPES = (0x7B, 0x7C, 0x7D, 0x7E, 0x7F)


class WireError(ValueError):
    """Local diagnostic; not an allocation in the consensus error table."""


@dataclass(frozen=True)
class Limits:
    wire_bytes: int = 8 * 1024 * 1024
    nodes: int = 50000
    depth: int = 16


TEST_LIMITS = Limits()


def require(ok, message):
    if not ok:
        raise WireError(message)


def uint_bytes(value):
    require(type(value) is int and value >= 0, "unsigned integer required")
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def rlp_encode(item):
    if type(item) is int:
        item = uint_bytes(item)
    is_list = isinstance(item, (list, tuple))
    if is_list:
        payload = b"".join(rlp_encode(child) for child in item)
        base = 0xC0
    else:
        require(type(item) is bytes, "RLP accepts bytes, integers or lists")
        payload, base = item, 0x80
        if len(payload) == 1 and payload[0] < 0x80:
            return payload
    size = len(payload)
    if size <= 55:
        return bytes([base + size]) + payload
    length = uint_bytes(size)
    require(len(length) <= 8, "RLP length exceeds uint64")
    return bytes([base + 55 + len(length)]) + length + payload


def rlp_decode(raw, limits=TEST_LIMITS):
    require(type(raw) is bytes and 0 < len(raw) <= limits.wire_bytes, "RLP byte bound")
    remaining = limits.nodes

    def parse(at, end, depth):
        nonlocal remaining
        remaining -= 1
        require(remaining >= 0 and depth <= limits.depth, "RLP resource bound")
        require(at < end, "truncated RLP")
        prefix = raw[at]
        at += 1
        if prefix < 0x80:
            return bytes([prefix]), at
        is_list = prefix >= 0xC0
        base = 0xC0 if is_list else 0x80
        count = prefix - base
        if count <= 55:
            size = count
        else:
            length_size = count - 55
            require(at + length_size <= end, "truncated RLP length")
            require(raw[at] != 0, "RLP length leading zero")
            size = int.from_bytes(raw[at:at + length_size], "big")
            at += length_size
            require(size > 55, "nonminimal long RLP")
        stop = at + size
        require(stop <= end, "truncated RLP payload")
        if not is_list:
            require(not (size == 1 and raw[at] < 0x80), "nonminimal single byte")
            return raw[at:stop], stop
        values = []
        while at < stop:
            value, at = parse(at, stop, depth + 1)
            values.append(value)
        return values, stop

    item, end = parse(0, len(raw), 0)
    require(end == len(raw), "trailing RLP bytes")
    return item


def seq(value, size=None):
    require(type(value) is list, "list required")
    require(size is None or len(value) == size, "field count")
    return value


def blob(value, size=None):
    require(type(value) is bytes, "bytes required")
    require(size is None or len(value) == size, "byte width")
    return value


def number(value, bits):
    blob(value)
    require(not value or value[0] != 0, "integer leading zero")
    require(len(value) <= (bits + 7) // 8, "integer overflow")
    result = int.from_bytes(value, "big")
    require(result < (1 << bits), "integer overflow")
    return result


def fields(values, widths):
    seq(values, len(widths))
    for value, width in zip(values, widths):
        if type(width) is int:
            number(value, width)
        else:
            blob(value, width[0])


def carrier(value):
    seq(value)
    require(bool(value), "missing carrier tag")
    route = number(value[0], 8)
    require(route in (0, 1), "unknown carrier")
    seq(value, 2 if route == 0 else 3)
    blob(value[1])
    if route == 1:
        seq(value[2])
        for fact in value[2]:
            blob(fact, 32)
        require(value[2] == sorted(set(value[2])), "fact references not sorted unique")
    return route


def validate_tree(kind, tx):
    """Schema/candidate normal forms only; proof and state checks remain external."""
    require(kind in TYPES, "unknown transaction type")
    seq(tx)
    if kind == 0x7B:
        fields(tx, [256, (32,), 64, 32, 16, (None,)])
    elif kind == 0x7C:
        seq(tx, 13)
        fields(tx[:6], [256, (20,), 64, 256, 256, 64])
        require(len(blob(tx[6])) == 20, "to width")  # v1.5 section 16.4: empty `to` is NON_CANONICAL_ENCODING (no contract creation from a PQ account in v1)
        number(tx[7], 256)
        blob(tx[8])
        for entry in seq(tx[9]):
            seq(entry, 2)
            blob(entry[0], 20)
            for key in seq(entry[1]):
                blob(key, 32)
        number(tx[10], 8)
        require(len(seq(tx[11])) in (0, 1), "public key option")
        if tx[11]:
            require(bool(blob(tx[11][0])), "empty optional public key")
        blob(tx[12])
    elif kind == 0x7D:
        fields(tx, [256, 64, 256, 256, 64, 8, (None,), (None,), 8, 256, 256])
        require(number(tx[8], 8) in (0, 1), "ECDSA parity")
        # r/s ranges, low-s, key/sig lengths and sender recovery are validation,
        # not generic integer serialization. Signing placeholders are not valid txs.
    elif kind == 0x7E:
        seq(tx, 14)
        fields(tx[:10], [256, (20,), 64, 8, (32,), 64, 256, 256, 256, 64])
        require(len(seq(tx[10])) in (0, 3), "sponsor option")
        if tx[10]:
            fields(tx[10], [(20,), 64, (None,)])
        number(tx[11], 32)
        route = carrier(tx[12])
        require(len(seq(tx[13])) in (0, 3), "lane auth option")
        if tx[13]:
            fields(tx[13], [64, (None,), (None,)])
        if route == 0:
            require(not tx[13], "Route A cannot carry lane auth")
        elif not tx[10]:
            require(bool(tx[13]), "self-pay Route B requires lane auth")
        elif tx[13]:
            require(number(tx[13][0], 64) == 0, "sponsored lane gas must be zero")
            # Do not require a valid key/signature here: adopted section 13.9
            # permits a sponsored recovery with invalid owner auth, reimbursement 0.
    else:
        seq(tx, 11)
        fields(tx[:9], [256, (20,), 64, 64, (None,), 256, 256, 64, 32])
        entries = seq(tx[9])
        require(0 < len(entries) <= 65535, "batch count")
        addresses = []
        for entry in entries:
            fields(entry, [(20,), 64, 8, (32,), 64, 256])
            addresses.append(entry[0])
        require(len(set(addresses)) == len(addresses), "duplicate batch address")
        carrier(tx[10])
    return tx


def decode_tx(raw, limits=TEST_LIMITS):
    require(type(raw) is bytes and 1 < len(raw) <= limits.wire_bytes, "transaction byte bound")
    kind = raw[0]
    return kind, validate_tree(kind, rlp_decode(raw[1:], limits))


def encode_tx(kind, tree):
    raw = bytes([kind]) + rlp_encode(tree)
    decode_tx(raw)
    return raw


def fixed(value, width):
    return number(value, width * 8).to_bytes(width, "big")


def pi_bytes(chain, version, entry):
    address, nonce, alg, commit, expiry, fee = entry
    chain32 = fixed(chain, 32)
    domain = keccak256(b"PQ-MIGRATE-v1" + chain32)
    return (chain32 + domain + blob(address, 20) + fixed(nonce, 8) + fixed(alg, 1)
            + blob(commit, 32) + fixed(version, 4) + fixed(expiry, 8) + fixed(fee, 32))
