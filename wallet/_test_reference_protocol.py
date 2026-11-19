"""Independent migration wire/PI reference for synthetic wallet tests.

This helper validates canonical encoding and layout agreement only. It is not an
execution client and supplies no proof, signature or consensus verification.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from pathlib import Path
from copy import deepcopy
import sys

import _test_reference_wire as old
from _test_reference_keccak import keccak256

ZERO20 = bytes(20)
ZERO32 = bytes(32)
U64MAX = (1 << 64)-1
rlp_encode, rlp_decode, number, fixed = old.rlp_encode, old.rlp_decode, old.number, old.fixed

class Invalid(ValueError):
    def __init__(self, code):
        super().__init__(code)
        self.code = code

@dataclass(frozen=True)
class Version:
    layout: int
    activation: int
    sunset: int

def validate_first_production_versions(versions):
    """Startup/configuration check, not a new transaction error code."""
    if not versions or any(v.layout != 2 for v in versions.values()):
        raise ValueError('first production activation requires PI_LAYOUT_2 only')

def need(ok, message='NON_CANONICAL_ENCODING'):
    if not ok: raise Invalid(message)

def fee_fields(entry):
    mode, sponsor, until = number(entry[6],8), old.blob(entry[7],20), number(entry[8],64)
    expiry = number(entry[4],64)
    need(mode in (0,1,2,3))
    if mode == 1: need(sponsor != ZERO20 and until <= expiry)
    elif mode == 3: need(sponsor == ZERO20 and until <= expiry)
    else: need(sponsor == ZERO20 and until == 0)
    return mode, sponsor, until

def decode(raw: bytes, versions: dict[int,Version], timestamp=None):
    """Bounded structural parse, layout agreement, then version liveness.

    Shape locates the candidate version field; only pinned configuration assigns
    semantics. No fallback to another version, layout, route or verifying key.
    TEST_LIMITS inherited from W1 are harness limits, not production bounds.
    """
    try:
        need(type(raw) is bytes and 1 < len(raw) <= old.TEST_LIMITS.wire_bytes)
        kind, tx = raw[0], rlp_decode(raw[1:])
        old.seq(tx)
        need(kind in (0x7E,0x7F))
        if kind == 0x7E:
            need(len(tx) in (14,17))
            layout = 1 if len(tx)==14 else 2
            offset = 3*(layout-1)
            version = number(tx[11+offset],32)
            stripped = tx if layout==1 else tx[:7]+tx[10:]
            old.validate_tree(kind,stripped)
            entries = [tx[1:7] if layout==1 else tx[1:10]]
            sponsor = tx[10+offset]
            if sponsor:
                # v1.7.3 author decision: sponsored carriers have an external payer.
                # A physical account cannot bypass the owner cap by taking both roles.
                need(sponsor[0] != tx[1])
                need(number(sponsor[1],64) <= number(tx[5],64))
            if layout==2:
                mode,_,_=fee_fields(entries[0])
                need(bool(sponsor) == (mode != 0))
        else:
            old.seq(tx,11)
            version = number(tx[8],32)
            entries = old.seq(tx[9])
            need(bool(entries))
            old.seq(entries[0])
            need(len(entries[0]) in (6,9))
            layout = 1 if len(entries[0])==6 else 2
            need(all(type(e) is list and len(e)==len(entries[0]) for e in entries))
            stripped = deepcopy(tx)
            stripped[9] = [e[:6] for e in entries]
            old.validate_tree(kind,stripped)
            need(tx[1] not in [e[0] for e in entries])
            need(number(tx[3],64) <= max(number(e[4],64) for e in entries))
            if layout==2:
                for e in entries: need(fee_fields(e)[0] != 0)
        for e in entries: need(e[3] != ZERO32)
        params = versions.get(version)
        if params is not None: need(params.layout == layout)
        # Generic canonical decoding precedes the version check, even for unknown v.
        need(params is not None, 'WRONG_VERIFIER_VERSION')
        if timestamp is not None:
            need(params.activation <= timestamp < params.sunset,'WRONG_VERIFIER_VERSION')
        return kind,tx,layout
    except old.WireError as exc:
        raise Invalid('NON_CANONICAL_ENCODING') from exc

def encode(kind, tx, versions, timestamp=None):
    raw = bytes([kind])+rlp_encode(tx)
    decode(raw,versions,timestamp)
    return raw

def public_inputs(kind,tx,layout):
    offset = 3*(layout-1)
    version = tx[11+offset] if kind==0x7E else tx[8]
    entries = [tx[1:7+offset]] if kind==0x7E else tx[9]
    result=[]
    for entry in entries:
        pi=old.pi_bytes(tx[0],version,entry[:6])
        if layout==2:
            fee_fields(entry)
            pi += fixed(entry[6],1)+old.blob(entry[7],20)+fixed(entry[8],8)
        need(len(pi)=={1:169,2:198}[layout])
        result.append(pi)
    return result
