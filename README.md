# Correctable Enrollment and One-Transaction Seed Proofs for Ethereum's Post-Quantum Migration

Code for the paper of the same title, [arXiv:2611.25663](https://arxiv.org/abs/2611.25663).

A research prototype of a post-quantum migration path for Ethereum accounts and validators.

Once a cryptographically relevant quantum computer (CRQC) exists, an attacker can derive the private key of any
externally owned account (EOA) whose ECDSA (Elliptic Curve Digital Signature Algorithm) public key is exposed. In this
prototype, the owner of such an account moves its authority to a post-quantum key (ML-DSA-44, the Module-Lattice-Based
Digital Signature Algorithm of FIPS 204) with a migration transaction. The transaction carries a hash-based succinct
proof of knowledge of the seed used to derive the account. After a public cut-off time T, legacy ECDSA authority ends.
The local demo starts a fresh Lean genesis with leanXMSS validator keys and actual Ream consensus. It does not
demonstrate a live BLS-to-Lean checkpoint transition or a mainnet state import.

> **Status.** A research prototype under development, not audited. The proof system runs with research parameters.
> Use it only on local test networks with the public test keys provided here, never with real funds or real keys.
> Owner credentials reach the prover only on stdin. The witness, the 64-byte seed and the two inner proofs (L0-prime
> and B, which are not zero knowledge) stay in process memory or anonymous memory descriptors; only the final proof F
> and allowlisted public metadata are written out ([prover custody](docs/PROVER-CUSTODY.md)). Memory is not securely
> zeroized or locked against paging.
> The results have not been independently reviewed.

## Contents

| Directory | Content |
|---|---|
| `client/geth/` | the go-ethereum changes: transaction types, the in-client proof verifier, pool and block-building rules |
| `client/ream/` | the integration of Ream, a Lean consensus client |
| `prover/` | the migration proof pipeline and the standalone verifier |
| `wallet/` | public-test wallet encoding, tracking components and a command-line carrier demo |
| `demo/` | a one-command two-node demo that writes an HTML report |
| `bench/` | measurement scripts |
| `formal/` | an Apalache model of one account's authority record (an inductive invariant over unbounded integers), its runner, mutation controls and run of record |
| `docs/` | build, demo, wallet and local release instructions |
| `solana/` | the enrollment step measured for Solana on one local node and a sample of mainnet blocks: two measurement programs and a control, a client, a check against Agave's cost model, scripts, the run records and the sample's per-slot and per-transaction data; added after the paper and not part of it |

Start with [the offline build instructions](docs/BUILD.md), then
[the local demo commands](docs/DEMO.md). The runtime package includes no expiring
migration proof: proofs and their current expiry are generated when a run starts.
The current proof profile requires at least 48 GiB available memory. Measurement
commands and their sampling limits are in [bench/README.md](bench/README.md).

The installed geth uses the fixed native verifier version `0x80000008`, PI198,
the 196,608-byte proof bound and the 16,777,216 transaction gas cap. The optional
adversarial block-order hook is absent unless `pq_research_order` is explicitly
selected at build time. Runtime reports distinguish executed, failed and
unverified steps; source compilation alone is not an end-to-end result.

## Provenance

This repository is a snapshot of the code behind the paper's measurements: commit bbf13f0 of the development repository, published without its history. Files whose bytes are pinned by digests keep their original text, so some of them name the project's working title (PQ-Migrate) or refer to development commits, to paths of an unpublished research tree (`code/...`, `results/...`) and to sections of an unpublished protocol specification. The offline dependency bundle (pinned upstream sources and module caches, about 0.9 GB), the run records and the research scripts are not in this repository; the authors provide them on request. The directory `solana/` is not part of that snapshot or of the paper: it was added later and holds a measurement of 26 November 2026 with its own scripts, data and run records.

## Scope

The attacker is external and has a quantum computer: it derives ECDSA private keys from exposed public keys. BIP-39
mnemonics are assumed unexposed. Classical attacks and operational failures are out of scope.

## Licence

Code written for this project is dual-licensed under MIT OR Apache-2.0, at your option
([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)). Third-party code keeps its own licence. In particular,
the changes to go-ethereum are under go-ethereum's licences: LGPL-3.0-or-later for library code and GPL-3.0-or-later for
go-ethereum's command-line programs (our new `cmd/pqcheckpoint` is LGPL-3.0-or-later). The licence texts are in
`client/geth/COPYING` and `client/geth/COPYING.LESSER`; Ream's is in `client/ream/LICENSE`. See [THIRD_PARTY.md](THIRD_PARTY.md).

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this project, as
defined in the Apache-2.0 licence, shall be dual-licensed as above, without any additional terms or conditions.

## Abbreviations

| Abbreviation | Meaning |
|---|---|
| BIP-39 | Bitcoin Improvement Proposal 39 (mnemonic seed phrases) |
| BLS | Boneh–Lynn–Shacham signatures |
| CRQC | cryptographically relevant quantum computer |
| ECDSA | Elliptic Curve Digital Signature Algorithm |
| EOA | externally owned account |
| FIPS | Federal Information Processing Standard |
| ML-DSA | Module-Lattice-Based Digital Signature Algorithm |
| XMSS | eXtended Merkle Signature Scheme |
