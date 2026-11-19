# Prover custody and dependency identities

The prover launcher keeps the credential, seed64, L0-prime proof and B proof in
process memory or inherited anonymous Linux memory descriptors. The leaf receives
witness JSON on stdin (`--input -`). No witness filename or credential is passed
in argv or environment variables. The environment descriptor map contains only
virtual artifact names and file descriptor numbers. Unmapped virtual paths fail;
they never fall back to disk. The fixed AIR, transcript parameters and trusted
verification keys are unchanged.

## Input and output

For the owner path, pipe JSON in the shape of `demo/public-input.json` into:

```sh
python3 -B prover/prove.py --build prover-build --input - --out runs/owner
```

The input producer must read the mnemonic or seed from its own protected input;
do not put it in a shell command, environment variable or temporary file. Mark
`credential.public` false (or omit it). This remains a research implementation:
the Python derivation is not constant-time, memory is not securely zeroized or
locked against OS paging, and OS hibernation/swap/crash collection is outside
this application-level no-file-persistence guarantee. The launcher disables core
dumps for itself and its children. The bundled demo uses public test data only.

Default output consists of:

- `f/proof.postcard`: the single final proof;
- `statement/pi198.hex`, `statement/statement.json`, `statement/pq-key.json`:
  public PI fields, the public ML-DSA key and its commitment, without the input
  credential, derivation path, seed64 or ML-DSA signing seed;
- `PROOF.json` and `logs/*.time`: allowlisted sizes, timings, exit codes and
  verification results. Raw child diagnostics and witness-dependent inner
  reports remain in memory, including on failures.

There is no default `input.json`, `inputs/`, `leaf/` or `b/` directory. Statement
construction no longer emits `l0p2-input.json`. `statement.py build - ...` uses
the same stdin-only owner input policy and emits only public metadata.

Every layer is still verified in a fresh process. B's verified public values
must equal the requested PI; the standalone F verifier checks the fixed keys
and the full PI. Altered-PI and altered-proof controls must reject. This custody
change does not establish a new soundness/hiding theorem or change any acceptance
gate, proof cap, gas constant, security parameter or trust assumption.

To check the address, or the ML-DSA key, against a public PI without putting a
credential on the command line:

```sh
# Have your input producer pipe one JSON object on stdin, for example
# {"mnemonic": "...", "path": "m/44'/60'/0'/0/0"}; "passphrase" is optional, and
# "xi" (hex) checks the ML-DSA-44 key commitment.
python3 -B prover/statement.py decode runs/owner/statement/pi198.hex --credentials-stdin \
  --repo . --crypto prover-build/bin/pq-test-crypto --crypto-sha256 EXPECTED_HELPER_SHA256
```

The decoder derives the address exactly as `build` does (the mnemonic as given,
its passphrase and the five-level path shape) and reports only the derived
address, the public ML-DSA key and whether they match the PI; it does not echo
the mnemonic, seed, path or xi. Obtain the helper digest from the authenticated
`prover-build/BUILD.json`. `--credentials-stdin` is a flag: the decoder has no
value-bearing credential option, and its parser refuses any unexpected argument
with a fixed message that does not repeat it.

## Explicit public-test retention

`prove.py --keep-inner` is accepted only with `credential.public: true`. File
inputs are likewise accepted only with that explicit public-test marker. This
is a declaration by the caller, not a detector for real secrets. Never mark a
private credential public. Retention exports the inner proofs/reports and raw
child logs for public-data diagnostics. It still does not export the credential.

`bench/run.py prove --keep-inner ...` forwards that opt-in. Without it, the
benchmark reads per-layer timings/sizes/verdicts from `PROOF.json`. Existing
frozen measurement cohorts retain their original interpretation; they are not
rewritten. The demo and CLI wallet reconstruct public test signing keys locally
and no longer depend on private key material in prover output.

## Git dependency content hashes

`tools/cache.py` checks each resolved Git source against its exact commit and
rejects modified tracked files. It exports committed content using `git archive`,
so untracked files cannot enter the bundle. Internal committed symlinks are
materialized from committed targets; external/dangling/cyclic links are refused.

`GIT-CRATES.json` records each Git package's name, version, Cargo source, full
commit, checkout and crate-relative paths, and a SHA-256 content identity. Each
checkout also has a file-by-file SHA-256/executable-bit list. The identity is
SHA-256 of compact, sorted-key JSON for that list. The `.cargo-ok` marker is an
explicit empty file included in the checkout identity.

Build and release commands (`tools/build.py`, `tools/build_prover.py`,
`tools/build_verified_prover.py`, `tools/build_aggregate.py`,
`tools/build_demo_tools.py`, `tools/release.py`) verify the complete bundle file set, every outer
checksum, every checkout/crate identity, and exact coverage of the Git packages
in `DEPENDENCIES.json`. Builds recheck copied Git sources before invoking Cargo.
Cargo may reconstruct `.git` metadata and internal committed symlinks in that
working copy. Only that metadata is excluded there; all source bytes and
executable bits remain checked, and escaping/non-file links are refused. The
immutable bundle itself still has an exact file set with no symlinks.
Releases preserve executable bits. Older caches without `GIT-CRATES.json` must
be exported again; do not invent missing identities by blessing their contents.
Checksums require an authenticated manifest; they do not authenticate a malicious
distributor on their own.

## Targeted regression commands

```sh
PQ_TEST_PROVER_BUILD="$PWD/prover-build" python3 -B -m unittest discover -s tests -v
python3 -B tests/run_custody_proofs.py --build prover-build --out runs/custody
```

The second command serially generates two full-parameter proofs with the public
synthetic credential: the default owner policy (marker false) and explicit public
retention (marker true). It checks all acceptance/negative controls, scans output
for credential material and observes file names while proving. It needs the same
48 GiB available memory and shared heavy-job lock as ordinary proving.

loop-internal self-review; not independently reviewed.
