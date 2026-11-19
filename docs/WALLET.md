# Public-test command-line wallet

Use the installed package. The command-line wrapper only supports its public
test mnemonic and local chain 13378. It is a carrier construction demo, not a
production wallet or a substitute for the authorization-tracking component.

```sh
python3 -B installed/wallet/cli.py derive --epoch 0
python3 -B installed/wallet/cli.py recover \
  --proof-run runs/first/proofs/recovery --out recovery.bin
python3 -B installed/wallet/cli.py pq --nonce 0 --epoch 0 --activate --out activation.bin
python3 -B installed/wallet/cli.py pq --nonce 1 --epoch 0 \
  --to 0x000000000000000000000000000000000000beef --value 1 --out spend.bin
python3 -B installed/wallet/cli.py query --rpc http://127.0.0.1:8545 \
  --address 0x9858effd232b4033e47d90003d41ec34ecaeda94
```

The query requires a running local demo node and its actual RPC port; the demo
allocates ports dynamically and records them in its run metadata. The complete
scenario rotates the owner's key and advances both nonces, so the simple
activation/spend example above describes a fresh, unrotated recovery. Do not
submit these example nonces into the completed scenario.

`recover` checks the fixed native verifier, current expiry, chain, owner and
new-key commitment before writing the transaction. A mode-3 fixture additionally
requires `--consent-account-reimbursement`. All files contain public-test
material. Construction never submits a transaction, changes an account or
overwrites an existing output file. The installed demo owns submission and
checks inclusion, node agreement and state changes.

## Enrollment alerts

Watch the canonical enrollment logs through the local consensus-validating node:

```sh
python3 -B installed/wallet/cli.py watch-enrollment \
  --rpc http://127.0.0.1:8545 \
  --address 0x9858effd232b4033e47d90003d41ec34ecaeda94 \
  --state runs/owner-enrollment-cursor.json
```

Pass each enrollment transaction hash recorded by this wallet with
`--own-enrollment 0x...`. An enrollment absent from that record emits
`UNRECOGNIZED_ENROLLMENT`; a matching hash emits `KNOWN_ENROLLMENT`. The former
means the wallet did not record the enrollment, not that an attack has been
proved. The alert includes the new commitment, enrollment time, transaction and
block identifiers. It does not submit a recovery or sign anything.

`--once` scans through the head observed at startup and exits. Normal operation
continues polling. Coverage starts at genesis unless `--from-block` is supplied;
that option deliberately excludes earlier enrollments. Keep the cursor outside
the immutable installation. Reuse it for the same chain, genesis, account and
starting block after a restart. The public demo retains its scanned block list;
it is intended for bounded local experiments, not unattended production use.

Alerts are flushed before the cursor advances. A process crash can repeat an
alert; consumers may deduplicate by `(blockHash, transactionHash, logIndex,
removed)`. A reorganization emits `ENROLLMENT_REMOVED` and scans the replacement
branch. This observer never resets key exposure or key-generation state and
does not assert finality. It trusts the local validating node's RPC, as the rest
of the demo wallet does.

Component regression: `python3 -B -m unittest discover -s wallet -p
test_enrollment_watch.py -v`. These RPC-model tests are distinct from a live
consensus-driven enrollment demonstration.
