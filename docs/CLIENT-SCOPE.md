# Client timing and RPC policy

Each research chain fixes `T0`, `T` and `W` in its genesis `pqMigrate` configuration.
The client does not implement the protocol's governance mechanism for adopting
`T′` or `W′` while preserving the required notice interval and the earlier
configuration before activation. Changing genesis parameters is not that
mechanism and is not a supported upgrade of an existing chain. Tests that choose
a short `W` create a separate synthetic chain and report that choice explicitly.

The ordinary `0x7c`/`0x7d` payload size limit is pool policy. Imported blocks use
the consensus encoding, gas and signature rules; they do not inherit the pool's
128 KiB payload ceiling. Single and batch migration carriers have their own
versioned consensus size bounds.

Geth's default RPC transaction fee cap is 1 ETH. A recovery with a gas limit of
16,000,000 reaches that cap at a `max_fee_per_gas` of 62.5 gwei; a higher declared
maximum is refused by local RPC policy even when the transaction is otherwise
valid. At the full 16,777,216 gas limit, the threshold is about 59.60 gwei. This
uses the declared maximum fee, not the eventual gas used or effective price.

For a controlled local experiment that needs a higher maximum, start geth with
an explicit larger cap, for example `--rpc.txfeecap 2` for 2 ETH. A value of `0`
disables that RPC policy. Record the chosen value with the experiment. Neither
setting changes consensus or the payer's balance requirement.

At every start, after its F and C identity checks, the client checks the system
images of the genesis. When `T0` is at or before the genesis timestamp and no
state bridge is configured, it refuses to start unless the genesis state holds
code `0x00` and nonce 1 at both the Registry and the FactRegistry. It reads the
genesis trie, or the stored genesis allocation when its hash equals the genesis
state root; with neither available it refuses. When `T0` follows the genesis,
the `T0` transition block installs both images instead. Offline commands built
on `MakeChain`, such as `geth import`, run neither the identity checks nor this
check, so start a node on a new datadir once before importing blocks into it.

Debug tracing, `debug_intermediateRoots`, `debug_replayBadBlock` and
`eth_simulateV1` replay a block with the same PQ block prologue as import, so a
replay of the transition block reports the installed images.

The fixed F and C identities, current proof-size bounds and build instructions
are described in [BUILD.md](BUILD.md) and [BATCH-VERIFIER.md](BATCH-VERIFIER.md).
