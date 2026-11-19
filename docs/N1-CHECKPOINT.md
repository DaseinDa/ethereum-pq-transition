# N1 registration, checkpoint and consensus switch lab

The installed `tools/n1/` directory provides BLS-authorized registration,
checkpoint construction, conflict exclusion and a two-phase consensus switch.
The switch keeps both geth processes and their execution databases running. It
anchors phase 1 to the same finalized execution block `B_ck` on both nodes; it
does not create a new execution genesis or copy balances into another chain.

This is a synthetic lab. Phase 0 uses three disposable Lean validators as a
stand-in for the trusted pre-switch consensus. The ten-validator beacon snapshot
and its BLS keys are public test fixtures, not a running Ethereum beacon chain.
Phase 1 uses the seven eligible Lean validators and real leanXMSS signatures.
This driver covers checkpointing and consensus finality, including a window with
X silent (T6b). With a fresh public-test package recovery proof, T8 also exercises
EL recovery, same-key activation and EIP-7002 request transport/finality. It does
not establish CL exit, withdrawal, re-stake, new membership or light-client recovery.

## Dependencies and offline installation

`demo/n1/DEPENDENCIES.json` pins the complete tool-specific Python closure, its
versions, and approved wheel filenames, sizes and SHA-256 digests from PyPI.
`requirements.txt` is the readable version list. The lab runtime targets CPython
3.12 on Linux x86_64; choose wheels compatible with that target. The inventory
also records other published platform wheels so a compatible offline environment
can be assembled without changing package pins. No compiler or network access
is needed by the collector or installer.

For an existing wheelhouse containing exactly one compatible wheel for each of
the twelve pinned packages, create a new offline bundle:

```sh
python3 tools/n1_dependencies.py collect --wheelhouse /path/to/wheels --out /path/to/n1-wheels
```

Keep the printed manifest SHA-256 separately. Assembly uses
`verify_wheelhouse(bundle)` to recheck the complete closure against the committed
inventory. The runtime distribution carries this bundle under `share/n1-wheels`;
the offline source release carries it under `n1-dependencies/`. It is
separate from the Cargo/Go cache bundle.

Create a dedicated environment, then install using the trusted bundle digest:

```sh
python3.12 -m venv /path/to/n1-venv
python3 /path/to/install/tools/n1_dependencies.py install \
  --bundle /path/to/install/share/n1-wheels \
  --expect-manifest-sha256 TRUSTED_SHA256 \
  --python /path/to/n1-venv/bin/python
```

Installation uses pip's isolated mode, `--no-index`, `--no-deps`, binary wheels
only and mandatory hashes. There is no dependency download fallback. Wheel
license and notice files remain inside the wheel artifacts. The collector
refuses unknown, changed, missing or duplicate package wheels before creating
the output directory.

## Run the checkpoint switch

Use a verified installed runtime and a new work directory outside it:

```sh
/path/to/n1-venv/bin/python -B /path/to/install/tools/n1/switch.py \
  --prefix /path/to/install --work /path/to/new-n1-run --run-id n1fixture
```

The native tools needed by this driver are already part of the runtime: `geth`,
`ream`, `profile-tool`, `profile-tool-three`, `fresh-public-keys`, `audit-history`
and `export-signed`. Optional T8 also uses the installed native F verifier and
`pq-test-crypto`. The driver verifies the installed manifest before generating
keys; it never generates a proof or reads an external research checkout.
The whole key-generation, client-run and audit sequence holds the shared
`~/pq-heavy-job.lock` (override with `--lock`). An occupied lock fails immediately;
the driver removes only its own lock token on exit. It binds loopback ports,
gives geth a 256 MiB cache setting and limits native
worker counts to two. These settings are not an operating-system memory limit;
apply the run's resource guard when executing the native clients and keygen.

The default timeline is:

| Event | Time |
| --- | --- |
| Phase-0 EL and Lean genesis | `G0`, after setup |
| Phase-0 halt reference | `G0 + 22 * 12 seconds` |
| Common deadline | `D_reg = S = T0 = halt + 180 seconds` |
| End of classical-sender interval | `T = T0 + 240 seconds` |

Phase 0 stops in the last slot before the halt reference. Its unfinalized tail
contains the honest owner of validator 6's registration. Both nodes must agree
on their head and finalized checkpoint; disagreement aborts the run. During the
halt, no new phase-0 blocks can arrive. Checkpointing and phase-1 provisioning
must finish with the required lead before `S`; otherwise the run aborts. The
new consensus uses `B_ck` as its execution anchor and drops the unfinalized tail.
The registry rejects calls with block timestamp **equal to or later than**
`D_reg`; calls after `S` cannot change the frozen registry accumulator or count.

The fixture expects the following result:

| Beacon validators | Registration result |
| --- | --- |
| 0 through 5 | Honest tuple included; identical duplicate for 5 is harmless |
| 6 | Attacker tuple included; the owner's tail registration is after `B_ck` |
| 7 | Attacker then honest tuple: conflict, excluded |
| 8 | Honest then attacker tuple: conflict, excluded |
| 9 | Correct BLS signature but `0x00` withdrawal credential: excluded |

Invalid signatures for 5 and 9 are ignored. The result is seven of ten equal
32-ETH beacon validators, with one attacker-controlled validator in the Lean
set (`f_A = 1/7`). This classification is independent of conflict arrival order.
The labels identify attacker keys for reporting only; they never decide which
registrations pass validation.

The result records binary/source identities, timing, registration receipts,
checkpoint files, REST state comparisons, the unchanged EL genesis and process
IDs, balances and registry storage at `B_ck`, post-switch finality and signature
audits. A final `PASS` requires the audit checks and clean process shutdown too.
`PUBLIC-MANIFEST.json` hashes public run artifacts; runtime directories, private
key stores and seeds are excluded. Keep the work directory private and never
reuse its signing keys or histories for another genesis.

## Silent X and optional late path

T6b runs by default after the checkpoint checks and any requested T8 path. It
stops X's Ream process, then observes H for ten 12-second slots. The silence
boundary is after X has exited. A new slot after that boundary must become both
justified and finalized, and at least one scheduled X proposer slot must remain
absent from the canonical EL chain. Both geth processes stay running. Use
`--silent-slots 0` to explicitly skip this scenario; its result then says
`NOT RUN` with that reason. A nonzero observation window must be at least ten
slots.

To include T8, supply one **current package prover recovery output directory**:

```sh
/path/to/n1-venv/bin/python -B /path/to/install/tools/n1/switch.py \
  --prefix /path/to/install --work /path/to/new-n1-run --run-id n1fixture \
  --recovery-proof /path/to/public-recovery-output
```

The directory must contain `PROOF.json`, `statement/statement.json`,
`statement/pi198.hex`, `statement/pq-key.json` and `f/proof.postcard`, exactly as
exported by the package's `prover/prove.py` (or the `recovery/` child of the
package migration demo's proof outputs). It must be a successful, explicitly
public-test v2 statement for chain 13378, the installed fixture owner, migration
nonce zero, fee mode zero and verifier version `0x80000008`. Metadata and exact
PI/proof hashes are checked; secret-bearing historical exports are refused.
The proof expiry must be current, at most seven days away, and leave enough
room for the configured run. No historical expiry or statement byte is rewritten.

The installed prover/client build source and dependency identities and the
actual native-verifier/helper binary hashes must agree with the installed
manifest. The driver freshly verifies the unchanged proof with that native F
verifier under its outer shared lock. It derives only the installed public
fixture's test signing key in memory and checks the exported public key and
commitment against it. `result.json` records this acceptance verifier identity;
it explicitly says the export's producer identity is unattested.

Fresh proof generation is a separate, explicit job under the same heavy-job
lock and the prover's resource requirements. For example, after the lock is
available, use the installed public input and a new output directory:

```sh
python3 -B /path/to/install/prover/prove.py \
  --build /path/to/install/prover-runtime \
  --input /path/to/install/share/public-input.json \
  --out /path/to/public-recovery-output --lock /path/to/pq-heavy-job.lock
```

Pass that same lock path to the switch when overriding its default. The switch
does not start a proof-generation job or renew an expired proof inside the fixed
timeline.

T8 waits until both EL heads reach `T`, submits unsponsored recovery `0x7e`,
checks both accounts, activates the same key with `0x7c`, and submits a zero-amount
EIP-7002 request for excluded validator 7. The evidence checks the withdrawal
credential source, request log and `requestsHash`, identical receipt blocks on
both nodes, and finality of all three transactions. This demonstrates request
transport through the Engine API; it does not claim a CL stake-state transition.

Without `--recovery-proof`, T8 says `NOT RUN` and gives the missing-input reason;
T6b remains available. An invalid supplied proof aborts the run, and a requested
but incomplete T8 cannot produce an overall `PASS`. The `tests` section records
T1 through T9 (including T6b), first/last check observation timestamps, and
separate start/end/duration for T6b and T8 when attempted. Check observation
spans are evidence timestamps, not performance benchmarks. `validationScope`
names the actual T6b/T8 status and the limits above. No live result from the
older research timeline is substituted for this `S = T0 = D_reg` port.

## Individual tools

`scenario.py snapshot` creates the public ten-validator snapshot. `register.py
build`, `send` and `verify` construct and validate 312-byte SSZ/BLS registrations.
`checkpoint.py run` requires two distinct RPC endpoints and checks canonicality,
finality, the registry bytecode/deadline, complete log replay and storage on both
nodes. `B_ck` must equal each halted node's latest finalized marker, not merely
an older finalized ancestor. Supply `--genesis /path/to/el-genesis.json` and
`--expect-genesis-sha256 TRUSTED_SHA256`; the tool checks the exact genesis bytes,
chain ID and `config.pqMigrate.t0` against the profile's explicit `T0`. The profile
must state `S = T0 = D_reg`. After finality advances, another run with the old
`B_ck` is refused; the original checkpoint remains verifiable by its manifest. It then verifies the registration domains, BLS signatures, key encodings,
lifetimes and withdrawal credentials before resolving conflicts.

`checkpoint.py layout` requires `--expect-manifest-sha256` and verifies every
checkpoint file before checking local key bindings. Keep that digest outside
the checkpoint directory. Each signing directory needs an explicit operator
binding `--binding NODE:LEAN_INDEX=KEY_DIRECTORY`; the directory is relative to
that node's `--keystore NODE=STORE` root under `hash-sig-keys`. The tool checks
both public keys against the selected checkpoint index. It does not infer an
index from a matching public key. Unbound indices stay offline, and unused key
directories are ignored.

A valid BLS registration can copy another validator's public-key tuple without
possessing its private keys. The checkpoint records that duplicate, and layout
does not refuse it: refusing would let one copied registration block every
node's provisioning. The operator binds its own index explicitly, layout checks
the directory's public keys against that index, and the copier's index stays
unbound, that is offline, since nobody holds its private keys. `layout.json`
lists such indices under `sharedKeyTuples` (with the bound one) and
`unheldLeanIndices`. Layout refuses to bind one tuple to two indices
(`key-tuple-bound-twice`), even from two directories, because the tuple would
then sign for both and reuse its one-time keys. Every check runs before any
output is written; a refusal leaves existing keys and signing histories
untouched.

For example, a node holding the keys for Lean indices 0 and 1 uses:

```sh
/path/to/n1-venv/bin/python -B /path/to/install/tools/n1/checkpoint.py layout \
  --checkpoint /path/to/checkpoint --expect-manifest-sha256 TRUSTED_SHA256 \
  --keystore H=/private/H --binding H:0=H0 --binding H:1=H1 \
  --out /path/to/new-layout
cp /path/to/new-layout/registry-H.yaml /private/H/registry.yaml
```

Standalone layout does not create signing history. Before starting Ream with
fresh, unused test keys, provision a new history using the checkpoint's exact
`anchor.json` `networkIdentity` and the same explicit Lean indices:

```sh
/path/to/install/bin/profile-tool-three history \
  /private/H/hash-sig-keys/H0 /private/H/signing-history NETWORK_IDENTITY 0 \
  /private/H/hash-sig-keys/H1 1
```

The history tool decodes all keys and validates every directory/index/role
binding before creating a history or `history-provisioned-once` guard. Duplicate
bindings therefore fail without consuming fresh keys, and corrected inputs can
retry. Once creation starts, an I/O or race failure can leave guards behind;
retain them and follow signing-history continuity/recovery procedures. Never
delete a guard or history to make a previously provisioned key appear fresh.
The complete switch driver supplies these bindings and runs this history step.
Use `--help` for explicit input and output paths.

The registry source and precompiled runtime are copied verbatim from the
CC0-1.0 research contract. The source input digests and adaptation provenance are
in `PORT-SOURCES.json`; current package file hashes are in `ARTIFACTS.json`.
Rebuilding the optional registry bytecode requires exactly solc 0.8.28; ordinary
checkpoint runs use the shipped runtime and do not invoke a compiler.

## Validation

```sh
/path/to/n1-venv/bin/python -B -m unittest discover \
  -s /path/to/install/tools/n1/tests -v
```

The rules and dependency-bundle tests use only the Python standard library.
The checkpoint tests exercise real BLS signatures, domain separation, invalid
credentials/key encodings, the exact deadline, canonicality/finality refusal and
missing-log detection. They explicitly skip if the N1 dependencies are absent.
All 34 Python unit tests passed on 2026-11-10 in the existing pinned CPython
3.12 environment under a 1 GiB address-space limit (3.5 seconds; no build,
dependency installation or native client run). This includes a copied tuple
with valid BLS registrations for two indices: layout binds the honest index,
leaves the copier's index unbound and reports both (2026-11-10, fix list F-04);
binding one tuple to two indices is refused before any output.
The tests also cover explicit T0/genesis binding, rejection of older finalized
checkpoints, snapshot-based credential labels, an operator-selected index with mismatched keys, duplicate
bindings, offline unbound indices and refusal to overwrite an existing layout.
The proof-input regressions use synthetic bytes and do not claim native proof
acceptance. They cover current filenames/hashes, public-only schema, PI fields,
expiry refusal, size limits and installed source/binary mismatches. Orchestration
tests cover explicit skipped/partial outcomes, identical-transaction submission
races, worker shutdown failure and the silent-node observation boundary.
The native history provisioning regressions are separate; Python test success
does not establish their result or a successful native two-phase run. The
adapted common-deadline driver requires fresh runtime validation; results from
the original research driver, which used a different timeline, are not evidence
for this port.
