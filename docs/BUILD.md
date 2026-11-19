# Building the local clients

This profile targets Linux x86-64 (including Ubuntu under WSL2). The build needs
Python 3.12 or later, Git, Go 1.25.14, Rust 1.98.0 (clients/F) and 1.96.0 (C), a C/C++ compiler, Clang,
pkg-config, CMake, Protobuf's compiler, and the OpenSSL development headers.
Ream requires x86-64-v3 and PCLMULQDQ. The F native library uses the baseline
x86-64 target. This is a research profile, not an Ethereum mainnet upgrade.

## Fixed sources

`client/geth/source.json` and `client/ream/source.json` pin upstream commits,
archive hashes, the ordered patch list (each patch's file, SHA-256 digest and
description), and the hash of the reconstructed file manifest.
Neither client is downloaded automatically. Obtain the corresponding public
Git objects on a preparation machine, and create these files:

```sh
mkdir -p cache
git -C /path/to/go-ethereum archive --format=tar \
  --output="$PWD/cache/geth.tar" 3d84c6b2e3e9be032f8f2dcd9e900f89391fcdab
git -C /path/to/ream archive --format=tar \
  --output="$PWD/cache/ream.tar" 9cd3498b97a5b2dbc54fd5b48c28143b773ca47d
python3 client/sources.py --cache cache --out prepared
```

`sources.py` checks the archives before extraction, checks each patch before
application, and verifies every resulting file. Existing output directories
are refused.

## Offline dependencies

On a preparation machine whose caches already contain the locked dependencies:

```sh
python3 tools/cache.py --sources prepared --out dependencies
```

This exports the selected Go source archives and Cargo dependencies. It never
downloads packages or copies credentials. Cargo Git revisions remain separate;
several LeanVM revisions use identical package names and versions, so flattening
them into one vendor directory would be incorrect. `CACHE-SHA256.json` records
every exported file; transfer its hash over the same trusted channel as the
source bundle. Compiler toolchains and system development packages must also
be installed on the offline machine.

## Build and check

```sh
# Set CACHE_SHA256 to the digest received through the trusted source channel.
python3 tools/build_aggregate.py --dependencies dependencies \
  --expect-cache-sha256 "$CACHE_SHA256" --out aggregate-build
python3 tools/build.py --cache cache --dependencies dependencies \
  --expect-cache-sha256 "$CACHE_SHA256" --aggregate-build aggregate-build --out build
```

The command uses new compiler and module caches, verifies the dependency bundle,
builds both clients, and runs the selected migration regressions. It does not
contact a module proxy or a Cargo registry. On Linux, an additional network
namespace can enforce this externally:

```sh
unshare -n python3 tools/build.py \
  --cache cache --dependencies dependencies --expect-cache-sha256 "$CACHE_SHA256" \
  --aggregate-build aggregate-build --out build
```

To include the actual F acceptance and altered-PI/proof tests, also supply
`--proof /path/to/f/proof.postcard --pi /path/to/statement/pi198.hex`, generated
for the current run. Missing optional fixtures are reported as skipped, never
as successful real-proof tests. `BUILD.json` and `logs/` preserve results and
command failures. Results are internal regression checks, not an independent
cryptographic audit. Reproducible source reconstruction is distinct from
bit-for-bit reproducibility of compiler output.

Ream tests run in two explicit configurations. With `reth`, missing execution
qualification must reject block production and votes; signer/history checks
exercise the production feature selection. A separate pure-CL run covers the
upstream algorithm fixtures that deliberately have no execution backend and
synthetic blocks. Passing that second suite is not evidence of Engine import,
PQ signatures, or production validity. The live demo supplies the real Engine
and signature checks. Optional heavy public-key fixtures remain visibly ignored
unless their required inputs are supplied.

The default geth binary uses `pq_final,pq_aggregate`. It verifies version `0x80000008`
in-process with the fixed F, B and L0-prime verification keys, PI198, and the
196,608-byte proof cap. No older proof backend substitutes for this verifier.
Four-owner `0x7f` transactions use the separately pinned C verifier and its
798-byte ordered statement. The build runs the public historical C fixture;
live-chain reproduction requires fresh proofs with the current expiry.
The `pq_research_order` build tag is absent from the installed binary. Its
separate test build allows adversarial ordering without changing transaction
validity or block import rules.

Before running a prover or nodes, use a shared job lock and allow only one
memory-intensive job. The proof-generation profile requires at least 48 GiB
available memory. Do not run it concurrently with this build.

The build commands above acquire `~/pq-heavy-job.lock` exclusively and refuse an
occupied lock. They never delete another owner's lock. Commit the source before
building: each successful record binds the commit, complete source content,
authenticated dependency manifest and output hashes. Assembly requires every
component to match that same snapshot. A later source change requires rebuilding;
older `VALIDATION.json` or `RECHECK.json` files cannot replace this provenance.

Git crates additionally have per-crate content identities and complete checkout
file manifests in `GIT-CRATES.json`. Build and release reject missing identities,
changed files, extra files or changed executable bits. Re-export older dependency
bundles before building. See [PROVER-CUSTODY.md](PROVER-CUSTODY.md).
