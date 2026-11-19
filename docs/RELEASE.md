# Local offline bundles

These commands create local files only. They do not create a GitHub release or
push a branch.

Commit the source tree before building the clients, prover and demo helpers as
described in [BUILD.md](BUILD.md) and [DEMO.md](DEMO.md). Assemble the runtime from builds
of that same commit. Then:

```sh
python3 -B tools/release.py --runtime runtime --cache cache \
  --dependencies dependencies --expect-cache-sha256 "$CACHE_SHA256" \
  --n1-dependencies n1-dependencies --out dist/local
cd dist/local
sha256sum -c SHA256SUMS
```

`runtime.tar.gz` contains an installer, binaries, notices, fixed verification
keys and public-test inputs. It contains no migration proof with an expiry.
`offline-source.tar.gz` contains the exact committed source, pinned upstream
archives and the dependency cache needed for rebuilding. Compiler toolchains
and operating-system development packages are prerequisites, not bundled
software. `RELEASE.json` identifies the source commit and archive hashes.
The source archive also carries `SOURCE-IDENTITY.json`; builders verify its file
hashes when no Git metadata is present. Release rechecks each embedded build
record against the current committed source and the actual runtime binaries.
An old build, a missing provenance field or a mixed dependency bundle is refused.

Checksums detect changes; they do not authenticate an untrusted distributor.
Obtain the expected manifest through a channel that you trust. Keep the corresponding source archive with the runtime archive.

## Install and start

On the supported Linux machine, with at least 48 GiB of memory available:

```sh
tar -xzf runtime.tar.gz
python3 -B pq-migrate-runtime/start.py --prefix installed --work runs/first
```

This provisions a fresh public-test genesis, generates current proofs, and runs
the two-node scenarios. It refuses existing installation and run directories.
The report is `runs/first/report.html`; machine-readable results and logs stay
under that run directory. Rerunning against an existing signing history is not
equivalent to provisioning a fresh genesis. The demo itself performs the
controlled restart using the existing keys and append-only history.

## Rebuild from the offline source archive

Install the toolchain versions and development packages listed in BUILD.md
before disconnecting the machine. The following commands need no Internet:

```sh
tar -xzf offline-source.tar.gz
cd pq-migrate-source
# CACHE_SHA256 is the separately authenticated dependency-manifest digest.
python3 -B tools/build_aggregate.py --dependencies dependencies \
  --expect-cache-sha256 "$CACHE_SHA256" --out aggregate-build
python3 -B tools/build.py --cache cache --dependencies dependencies \
  --expect-cache-sha256 "$CACHE_SHA256" --aggregate-build aggregate-build --out build
python3 -B tools/build_verified_prover.py --out prover-build --dependencies dependencies \
  --expect-cache-sha256 "$CACHE_SHA256"
python3 -B tools/build_demo_tools.py --build build --dependencies dependencies \
  --expect-cache-sha256 "$CACHE_SHA256"
python3 -B demo/assemble.py --client-build build --prover-build prover-build \
  --aggregate-build aggregate-build --n1-dependencies n1-dependencies --out runtime
python3 -B runtime/start.py --prefix installed --work runs/first
```

Run builds, proving and nodes serially. Build reproducibility here means fixed
source reconstruction and offline compilation. It does not claim identical
compiler-output bytes on arbitrary machines, deterministic randomized proofs,
or production security acceptance.
