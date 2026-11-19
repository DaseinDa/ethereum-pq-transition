# Batch proof verification interface

The package includes the fixed four-owner research C prover and native verifier
under `prover/aggregate`. Client builds link its `libpq_migrate_tree.so` alongside
F and enable the `pq_aggregate` tag. Version `0x80000008` selects this research C
profile. Packaging the implementation does not itself establish successful native
or live-chain validation; consult the corresponding build and run records.

## Public statement and batch identifier

For the four entries in transaction order, the client reconstructs every PI198
field from its entry and applicable transaction/chain fields:

```text
statement = uint16_be(4) || uint32_be(0x80000008) || PI_0 || PI_1 || PI_2 || PI_3
length(statement) = 798
batch_id = keccak256(statement)
```

Do not sort, deduplicate, truncate or re-encode those PI bytes. The fixed profile
does not accept other counts or versions. The complete statement is absorbed
into C's Fiat-Shamir transcript; `batch_id` is an identifier, not an acceptable
substitute public input. Current client receipt logs do **not** include
`batch_id`; there is no claim of receipt/log correlation through that field.

## Native boundary

`pq_aggregate_verify(proof, proof_len, statement, statement_len)` verifies the
carrier against the client-computed statement. The carrier is 256 bytes of
canonical periodic advice followed by the canonical C postcard proof; its maximum
length is 196608 bytes. Native verification checks C's fixed trusted parameters
and recomputes the pinned F periodic advice. The caller cannot supply another key.

The ABI returns 0 for acceptance, 1 for invalid input, 2 for an invalid proof, and
3 for a local verifier fault. `pq_aggregate_ready_v1` initializes the pinned keys
and periodic evaluator; `pq_aggregate_key_v1` reports
`3f84335f8b7301181f37e3080cb81fc5d8444952574e0e90cd2a277d12bd2825`.
F's single-owner ABI remains separate and is not used as an aggregate verifier.

## Reproduction and validation

`tools/build_aggregate.py` consumes an authenticated offline dependency bundle
and committed source snapshot. `prover/aggregate.py` consumes four F/PI exports,
preserves their order and independently verifies the generated carrier. See the
aggregate README for exact commands, custody rules and resource limits.

The frozen genuine fixture supplies all 798 public bytes and the matching C
carrier. `tools/check_aggregate_native.py` tests the real ABI: genuine acceptance,
every statement byte, entry order, lengths, digest-only substitution, malformed
and tampered carrier/advice, null pointers, readiness and key identity. The
builder also runs the native periodic consistency check. These checks must pass
before a build record says `PASS`; static tests do not stand in for native runs.
Client tests using the historical fixture pin its timestamp explicitly. A second
public fixture, `four-owner-gates`, was generated with the same frozen prover and
aggregate builds (`PROVENANCE.json` records the owner inputs and the proof records):
its entries carry an early expiry, fee modes 3 and 1 and a migration nonce of 1, so the
client's two-block import test exercises the expiry skip, the owner-money paths and
an override of a real `0x7d` enrollment end to end with native C acceptance. A current
live batch requires four fresh F proofs and a fresh aggregate within their expiry.

Stub acceptance only demonstrates client execution and cannot establish aggregate
proof validity.
