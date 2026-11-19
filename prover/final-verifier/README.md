# pq-final-verifier

The verifier of F, the final layer of the migration proof (L0′ → B → F). go-ethereum links it through
`prover/native`; the standalone binary `pq-final-verify` (`src/bin`) runs the same check.

## What `verify` checks

In this order:

1. the size: at most 196,608 bytes (`ProofTooLarge`, before any decoding);
2. strict decoding of the proof (postcard, no trailing byte, and the canonical re-encoding must equal the input);
3. the statement's canonical rules (`Pi198`): the domain tag, a non-zero key commitment, fee fields that fit the mode;
4. F's verifier key, built once per process from the embedded material and checked against `TRUSTED_PARAMS`;
5. the proof's degree bits;
6. F's STARK verifier, with the 198 bytes of the statement as its public values.

`Ok(())` means accepted. An error is an invalid input, a proof rejected by the STARK verifier, or a local fault
(`VerifyError::class`); a local fault is not a verdict on the proof. A panic inside the verifier is caught and
returned as an internal fault.

## What `TRUSTED_PARAMS` pins

F's FRI and PCS parameters (`FriPcsParams`: the trace size, blowup, number of queries, proof-of-work bits, cap height,
salts, digest size and extension degree), the digests of the embedded key material (`key/f-key-material.json`,
`key/f-periodic.rle`), its lookups and opened next-row sets, and the digest chain F → B → L0′. The verifier recomputes
all of them and refuses any other parameter set.

## Identity-bound files

`src/key.rs` embeds `key/f-key-material.json`, `key/f-periodic.rle`, `src/fkernel.rs` and the files in `key/sources/`
with `include_bytes!` and hashes them into the verifier key's identity. Do not edit these files, not even for
presentation: one changed byte changes the identity, and proofs made for the old identity are refused. `src/fkernel.rs`
and `key/sources/` are byte-identical copies of the prover's sources in `prover/tree/src`, which
`prover/air-source.sha256.json` pins; the verifier checks its own copies through the digest chain above.

## Build

`cargo build --release --offline --locked`, with the pinned `Cargo.lock` and a Cargo cache taken from the verified
dependency bundle; `tools/build_prover.py` does exactly this. The modified Plonky3 copies in `crates/` are described in
their `MODIFICATIONS.md` files and in `THIRD_PARTY.md`.

No figure here is a post-quantum security level.
