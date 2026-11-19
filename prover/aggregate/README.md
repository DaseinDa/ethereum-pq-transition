# Four-owner research aggregate C

This separate workspace packages the existing AG -> C construction for four
distinct owners. It does not replace the single-owner F prover or its key. The
native library remains `libpq_migrate_tree.so`; the ABI is in
`include/pq_aggregate.h`. The fixed C key is
`3f84335f8b7301181f37e3080cb81fc5d8444952574e0e90cd2a277d12bd2825`.

`SOURCE.json` records all 58 imported source files, their research Git blobs,
the prepared Cargo files, and hashes of reused local dependency inputs. Imported
source files match the recorded research commit byte for byte. Historical
comments inside those files are retained: several source files contribute bytes
to AIR/key identities. Shared dependencies are listed separately so future local
diagnostic-only changes remain explicit. No existing F identity changes.

The fixed research verifier version is `0x80000008`. The expected statement is
exactly 798 bytes: `uint16_be(4) || uint32_be(0x80000008) || PI198_0 || ... || PI198_3`.
Each F proof must already bind that version in its PI. The carrier is 256 bytes
of canonical periodic advice followed by C's canonical postcard proof, with a
total limit of 196608 bytes. The native verifier checks C, then recomputes F's
periodic advice. It accepts the complete ordered statement, never a batch digest.

Build from a clean committed checkout and an authenticated offline dependency
bundle on Linux:

```sh
python3 tools/build_aggregate.py --dependencies /data/dependencies --expect-cache-sha256 TRUSTED_CACHE_MANIFEST_SHA256 --out /data/aggregate-build
```

The builder checks the exact Rust 1.96.0 compiler commit, copies only committed
source inputs, uses the shared `~/pq-heavy-job.lock`, and builds four binaries and
the native library. Its default per-process address-space cap is 8 GiB; a larger
`--memory-gib` requires an approved budget. Build success requires the genuine
fixture, native ABI negative tests and periodic-table check to pass. The dependency
bundle manifest digest must come from a trusted transfer record, not from an
untrusted bundle's own claim. The build record binds source and binary hashes.

Aggregate four exported F runs, in transaction order:

```sh
python3 prover/aggregate.py --build /data/aggregate-build --owner /data/f0 --owner /data/f1 --owner /data/f2 --owner /data/f3 --out /data/aggregate-proof
```

The launcher copies only `statement/pi198.hex` and `f/proof.postcard`. It does not
read seeds, private witnesses or owner logs. AG stays in memory by default;
`--keep-inner --public-test-data` additionally requires all four owner records to
declare `publicTestOnly`. C's output is `c/carrier.bin`; `statement.bin` is assembled
independently and compared against the prover output, then verified in a fresh
process. Historical source report labels say public-vector even for ordinary
inputs; the launcher's `AGGREGATE.json` records the actual input declaration.

Proving requires at least 48 GiB available RAM, eight Rayon threads, and a 40 GiB
per-process address-space cap under the shared lock. Recorded research runs used
about 31 GiB peak RSS; those historical measurements are not a new validation
result for this package. Never remove an occupied lock to start a competing job.

`fixtures/four-owner` contains a genuine historical public C proof and its complete
statement. Its expiry is historical; it is a component-verifier fixture, not a
current live-chain proof. `fixtures/four-owner-gates` is a second genuine public C
proof made with this package's frozen prover and aggregate builds from the four
public owner inputs it ships (one early expiry, fee modes 3 and 1, one migration
nonce 1), for the client's end-to-end entry-gate tests; its `PROVENANCE.json` pins
the files, the inputs and the proof records. Hash/provenance checks and Python model tests are small.
Native builds, native negative tests, fresh aggregation and live batch execution
must be reported separately when actually run. This remains research software.

Dependency process/shape diagnostics are quiet by default. Direct native tool
invocations may opt in with `PQ_PROVER_DIAGNOSTICS=1`; any other value leaves
those diagnostics disabled. The packaged launchers sanitize inherited proof
control variables. `SOURCE.json.localSharedInputChanges` records the six local
diagnostic-only dependency edits separately from the frozen aggregate imports.
