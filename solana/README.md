# Solana: the enrollment step on a second network

The paper ([arXiv:2611.25663](https://arxiv.org/abs/2611.25663)) measures how long Ethereum accounts need to
register a post-quantum key before ECDSA is retired: 29.4 days for the 4.45 million accounts that hold at least
0.1 ETH, because block space is scarce. That figure comes from a ten-node simulation with mainnet-derived
accounts and fee demand. This folder measures the same step for Solana. It is not part of the paper.

The measurement was made on 26 November 2026 and has two parts. One is a local node of Agave 4.4.1, the
validator software version that 54.5 % of mainnet's stake reported that day, set to mainnet's feature set and
per-block limits. The other is a sample of mainnet's blocks from the same day.

## Result

| | Ethereum (the paper) | Solana (this run) |
|---|---|---|
| Step | enrollment and activation, signed with ECDSA, then ML-DSA-44 | enrollment and activation, signed with Ed25519, carrying ML-DSA-44 |
| One account | 567,878 gas | 2 transactions, 8,076 entry bytes, 23,772 cost units |
| Limit that binds | the gas target (30 M a block, half the limit): bidding at most 1 gwei, the migration takes what ordinary users leave, 40 % of it | entry bytes per block (10 MiB) in 1,394 of the 1,700 sampled blocks, cost units in the other 306 |
| Accounts per day | about 152,000 (21.1 accounts per slot, 7,200 slots a day) | block space for about 476 million if every block is filled to its limit; about 20.5 million if blocks only double in size |
| Example | 4.45 million accounts with at least 0.1 ETH: 29.4 days | 10.75 million addresses of every kind with at least 0.1 SOL: about 32 minutes of blocks filled to their limit; 12.6 hours if blocks only double in size |

The Solana column is block space for the enrollment step, not a time in which Solana could migrate. It counts
how many accounts can place their two transactions under the per-block limits, next to the ordinary traffic of a
365-second sample of mainnet. The transactions carry real ML-DSA-44 keys and signatures, but nothing on chain
verifies them: the validator has no ML-DSA-44 verifier, and 11,310 of the 23,772 cost units are a charge by rule
that stands for one. The column comes from one node: blocks filled to the limit carry 25 times the bytes of
today's blocks, and the run does not show how such blocks travel between mainnet's validators. The full table is
`results/SOLANA.md`; every number in it is in `results/SOLANA.json`.

Terms. A slot is the time in which one validator, the slot's leader, builds one block (about 0.2 s on mainnet);
an epoch is 432,000 slots on mainnet. A block is a sequence of entries, the batches in which the leader records
transactions; its entry bytes are the bytes of its transactions plus 56 bytes for each batch. A program is code
deployed on chain, which the validator runs in a virtual machine; a precompile is a signature verifier built
into the validator itself. Compute units meter what a transaction executes. Cost units are what the per-block
cost limit counts: the compute units plus charges for signatures, write locks, instruction data and loaded
account data. A transaction also has two limits of its own, on the compute units it may use and on the account
data it may load. It states them, or the validator applies its defaults. Its cost at the limits is what it would
be charged if it used both in full. A transaction's fee reward is its fee less the half of the signature fees
that is burnt. A feature is a protocol change that the validator software carries and that an account on chain
switches on. A lamport is 0.000000001 SOL.

## Findings

1. **By size, an ML-DSA-44 enrollment fits one Solana transaction.** The public key (1,312 bytes) and the proof
   of possession (2,420 bytes) travel in one transaction of 3,982 bytes. The v1 transaction format, active on
   mainnet since slot 447,120,000, allows 4,096. The program stores a commitment to the key and does not verify
   the proof (finding 7).
2. **A block of enrollments alone reaches the byte limit first.** Under mainnet's 200 ms slot parameters a block
   may hold 10,485,760 entry bytes and 50,000,000 cost units. The local node, under the same parameters, packed
   exactly 2,596 enrollments into each of 15 consecutive blocks and 2,596 activations into each of 14
   consecutive blocks; no block held more. That is the entry-byte limit divided by the 4,038 bytes one
   enrollment takes (3,982 plus 56 of entry overhead). Such a block uses 17.4 million cost units as measured and
   32.1 million with the charge for the verifications, 64 % of the cost limit.
3. **Ordinary traffic uses little of the entry-byte limit and a third of the cost limit.** In 1,700 consecutive
   mainnet slots (365 seconds of 26 November 2026), ordinary transactions use on average 4.0 % of the entry
   bytes and 33.6 % of the cost units that a block may hold; the fullest blocks reach 15.5 % of the bytes and
   49,999,374 of the 50,000,000 cost units. Next to this traffic the byte limit decides the migration's share in
   1,394 of the blocks and the cost limit in 306.
4. **For the addresses that hold at least 0.1 SOL, the enrollment needs minutes to hours of block space.** If
   the migration takes all the space that ordinary traffic leaves (the first rate), mainnet's blocks have room
   for about 476 million accounts a day. If it adds no more entry bytes to a block than ordinary traffic already
   puts there, so that blocks only double in size (the second rate), the room is about 20.5 million accounts a
   day. The first rate moves with the charge for a verification: it is about 489 million at the lower charge of
   section 1 and about 380 million at twice the charge. The second rate hardly moves. Counted in block space
   alone, every address with any balance, 1.24 billion of them, would take 2.6 days at the first rate and 60.2
   days at the second. Of these addresses, 1.20 billion hold less than 0.01 SOL, and the two transactions take
   0.00754 SOL from the wallet.
5. **What an account pays.** Two signature fees, 0.00001 SOL in total, and a deposit of 0.00753 SOL. The deposit
   is the minimum balance (the rent-exempt minimum) that mainnet requires of the record: 5,080 lamports for each
   of its 1,354 bytes and for the 128 bytes of overhead of every account. It is not a fee: it stays in the
   record, and this program has no instruction that returns it.
6. **If more enrollments arrive than the free space holds, a leader that runs Agave ranks most of today's
   traffic below them.** The two rates displace nothing: they use only the space that ordinary traffic leaves.
   Beyond that space the leader's ranking decides. Such a leader ranks a transaction by its fee reward per cost
   unit, and it takes the cost at the transaction's own limits, stated or default, before the transaction has
   run. An enrollment that pays only the signature fee offers 0.195 lamports per cost unit with the verification
   charge counted in its cost (0.348 without it). In the sample 80.2 % of ordinary transactions offer less (82.6
   % without the charge); they carry 89.0 % of the bytes and 91.0 % of the cost units that ordinary transactions
   use. This share rests on the limits of both sides. The run sets the limits of its enrollments just above what
   they use: 4,900 compute units for 4,425 used. The median ordinary transaction uses 21.6 % of its compute-unit
   limit, or 34.9 % among the two thirds of the sample that succeeded. And 40.7 % of the ordinary transactions
   state no limit on the account data they load, so they are ranked as if they loaded 64 MiB. Ranked by the cost
   units they used, at the fees they paid, 39.8 % of the ordinary transactions would offer less: about half of
   those that rank below do so only because they ask for more than they use. In turn, an enrollment that asked
   for 200,000 compute units and 64 MiB of loaded data, the defaults of a legacy transaction whose one
   instruction calls a program that is not on Agave's list of built-in programs, would rank above only 17.3 %.
   While enrollments wait, the transactions that offer less would be taken after them, and dropped if the
   leader's slots end first (section 5), unless they ask for tighter limits or add a fee: at their present
   limits a median of 26,041 lamports more ranks them level with an enrollment, 81,195 at the 90th percentile.
   Tips are outside this rule: 29,936 of the sampled transactions (4.7 %) also pay a tip into one of Jito's tip
   accounts, and Jito's block engine orders the groups of transactions (bundles) it hands to a leader by its own
   rule (docs.jito.wtf/lowlatencytxnsend).
7. **The ML-DSA-44 verifier written for this run does not fit in one transaction.** It takes 1,750,745 compute
   units inside the virtual machine, 1.25 times the 1,400,000 a transaction may use. It is one implementation,
   so the figure is no floor for other programs. The rates above assume a verifier built into the validator,
   like the one in the paper's client.

## How it was run

### 1. The registry program (`program/`)

A Solana program with the two steps an account takes on the paper's enrollment path.

- `Enroll` (transaction type `0x7d` in the paper): the wallet signs with its Ed25519 key. The transaction
  carries an ML-DSA-44 public key and a proof of possession. The program creates the wallet's record and stores
  the SHA-256 commitment to the key.
- `Activate` (the first transaction of type `0x7c` in the paper): the transaction carries the public key and an
  ML-DSA-44 signature. The program checks the key against the commitment and stores it in the record.

A wallet has one record: the account at the address that the system program derives from the wallet's address,
the seed `pq-enroll` and the program's id. Only the wallet can sign for that address. If someone sends lamports
to it first, the enrollment tops it up and allocates it instead of creating it.

The stock validator has no ML-DSA verifier, so the program does not verify the two ML-DSA signatures. The
transactions carry real keys and signatures, which the client produces with the `fips204` crate, so every
transaction has its real size. The run charges each verification separately, in proportion to Solana's price for
its Ed25519 precompile. Agave's `cost-model/src/block_cost_limits.rs` counts 30 cost units per microsecond and
gives a signature that the Ed25519 precompile verifies 2,400 units, a reference time of 80 microseconds (720 for
a transaction signature, 4,800 for the secp256r1 precompile). On the run's machine one ML-DSA-44 verification
takes 70.94 microseconds and one Ed25519 verification 30.11, each the median of the five rounds' medians in
`results/bench_verify.json`. The charge is 2,400 times the ratio of the two times (2.3563): 5,655 cost units per
verification. It stands for a verifier built into the validator, which mainnet does not have.

The first rate depends on this price. At 30 cost units per microsecond of the run's machine, which is faster
than Solana's reference, the charge would be 2,128 and the first rate about 489 million accounts a day. At twice
the charge the cost limit binds in 1,695 of the 1,700 sampled blocks and the first rate is about 380 million; at
five times it is about 193 million. From no charge to ten times the charge, the second rate stays between 20.3
and 20.5 million. A signature that a precompile verifies also pays a signature fee of 5,000 lamports; the run's
transactions pay one fee each. The program is a measurement program. Do not deploy it to hold value.

**Verification inside the virtual machine (`program-verify/`).** A second program measures what the verification
costs when a program does it. The `fips204` crate cannot run there: the build reports a frame of 62,656 bytes
for its verification function, a program's frame may use 4,096, and the node stops every call
(`program-verify-fips204/` is this control). `program-verify/src/mldsa44.rs` is a verifier written for that
limit: it keeps its polynomials on the heap. On 10,000 pairs of key and message, with valid signatures and with
altered signatures, keys and messages, it gives the same answer as `fips204` in all 189,890 comparisons, and
likewise on 4,397 further inputs built so that one check alone decides. Simulated on the local node
(`simulateTransaction`), one verification of a proof of possession takes 1,750,745 compute units, the median of
five keys (`results/verify-in-vm.json`). With the node's own limit the simulation stops at 1,400,000 units; the
figure was read with that limit lifted (`--compute-unit-limit`). If both verifications of an account could run
in a program at that cost, one account would take 3,513,952 cost units, the cost limit would bind in every
block, and the room would be about 3.8 million accounts a day.

### 2. The local node (`tools/start_node.sh`, `harness/`)

One Agave 4.4.1 node (`solana-test-validator`, feature set 2681577653, the set that 79.2 % of mainnet's stake
reports) with Alpenglow, mainnet's consensus protocol, switched on, and with the 35 features that `solana
feature status` lists as inactive on mainnet turned off.

The validator keeps its per-block limits in a table with one row for each slot time
(`runtime/src/slot_params.rs`). A node starts in the row of its genesis, which allows 20 MiB of entry bytes per
block; mainnet is in the 200 ms row, which allows 10 MiB. A slot-time feature takes effect at the start of the
epoch after its activation, so with 32-slot epochs the node is in the 200 ms row from slot 32. The run of record
starts after slot 96.

The client `pqsol` derives every wallet, key and signature from a seed. For each run it funds the wallets,
checks the program's rules on the first seventeen wallets one transaction at a time, then sends the enrollment
of every remaining wallet and, after those, every activation as fast as the node's RPC takes them, eight
transactions to a request. A transaction that has not landed when its blockhash expires is sent again. The
client reads the blocks back from the node and takes each transaction's size, compute units and cost units from
the node's own records.

| Run | Node flags | Row of the limits | Wallets | Largest block | Blocks of that size | Sent per second |
|---|---|---|---|---|---|---|
| `local-run-200ms` | `--alpenglow --slots-per-epoch 32` | mainnet's 200 ms row | 40,017 | 2,596 enrollments; 2,596 activations | 15; 14 | 25,130; 24,101 |
| `local-run-genesis` | `--alpenglow --ticks-per-slot 256` | genesis row, slots of 1.6 s | 60,017 | 5,193 enrollments; 5,193 activations | 11; 11 | 28,174; 27,361 |

`local-run-200ms` is the run of record: the node is in mainnet's 200 ms row, and its blocks stop at 2,596
transactions, the 10 MiB limit over 4,038 bytes. `local-run-genesis` checks that the stop follows the limit: in
the genesis row the limit is 20 MiB, the slots are set to 1.6 s, and the blocks stop at 5,193.

In both runs all enrollments and activations landed and none failed, and the eleven checks passed:

- after an enrollment the record holds the commitment, and after the activation the key;
- every remaining wallet ends with an activated record that holds its own key;
- an enrollment and an activation succeed after someone sent lamports to the record address first: less than the
  enrolled record needs, more than it needs, and as much as the activated record needs;
- an activation before the enrollment fails, a second enrollment of an enrolled wallet fails (after a first one
  that succeeds), an activation with a key other than the committed one fails, an enrollment into another
  wallet's record fails, and an enrollment of a wallet that did not sign fails, each with the error that its
  rule gives.

In both runs every transaction landed when it was first sent.

### 3. The mainnet sample (`tools/sample_blocks.py`, `tools/parse_blocks.py`)

1,700 consecutive finalized slots, 474,231,891 to 474,233,590 (26 November 2026, 17:28:34 to 17:34:39 UTC, 365
seconds), read from the public RPC with every transaction's raw bytes and metadata: 1,700 blocks, no skipped
slots, 640,488 transactions. Every block names the block before it as its parent, so the window has no gap.
`data/mainnet_blocks.csv` has one row per slot and `data/mainnet_txs.csv.gz` one row per transaction.
`data/mainnet_block_index.jsonl` has the size and SHA-256 of every block as downloaded (the JSON-RPC result,
written compactly). The downloaded blocks, 4.2 GB of JSON, are not in the repository; the two CSV files are what
the analysis reads. The RPC node reports each transaction's cost units, so a block's use of the cost limit is
that node's figure, not a recomputation.

The sample carries 1,754 transactions a second (640,488 in 1,700 slots of 214.8 ms). Over the 317 minutes around
it for which the RPC node reports the cluster's rate, that rate ranges from 1,140 to 3,292 with a median of
1,879 (`data/mainnet_params.json`).

### 4. The limits (`tools/mainnet_params.py`)

The limits are constants of the validator (`runtime/src/slot_params.rs`), and feature accounts on chain select
the row that applies. The script reads those accounts and writes what it reads to `data/mainnet_params.json`.
The feature that selects the 200 ms row was activated at slot 454,464,000 and applies from the next epoch (slot
454,896,000); the feature that raises the cost limit was activated at slot 435,888,000. Together they give
10,485,760 entry bytes and 50,000,000 cost units per block. Two observations agree with the constants. The block
of the sample that uses the most cost units uses 49,999,374. And the local node stops at 2,596 enrollments per
block: with 56 bytes of entry overhead each that is 10,482,648 entry bytes, 3,112 short of the limit, less than
the 4,038 of one more enrollment.

`runtime/src/slot_params.rs` also caps the account data a block allocates at 50 MB and the cost of the
transactions that write-lock one account at 20 million cost units. Neither binds here: a block of 2,596
activations adds 3.4 MB, and a migration transaction write-locks only its own wallet and record.

`data/mainnet_params.json` also holds the feature `bls_pubkey_management_in_vote_account` (activated at slot
431,568,000). With it Agave no longer counts the vote program as a built-in program when it sets a transaction's
default compute-unit limit (`builtins-default-costs/src/lib.rs`), and the defaults in section 5 rely on that.
The entry was added on 27 November 2026 (`features_read_at_unix`) with the script's `--features` form, which
reads the feature accounts again and leaves the rest of the file as it was read on 26 November 2026
(`read_at_unix`).

### 5. The rate (`tools/analyze.py`)

One account needs an enrollment and an activation: 8,076 entry bytes (3,982 + 3,982 + 2 x 56) and 23,772 cost
units (6,702 + 5,760 measured, plus 2 x 5,655 for the two verifications). For every sampled slot the analysis
takes the free entry bytes and the free cost units: the limit less what the block's ordinary transactions use.
Their entry bytes are counted as their bytes plus 56 per transaction, as if every transaction were recorded in a
batch of its own. The room for accounts is the smaller of the free entry bytes over 8,076 and the free cost
units over 23,772. A skipped slot offers no room. The mean over the sample, times the sample's slots per day, is
the first rate. The slot time, 214.8 ms, is the 365 seconds between the first block's time and the last, divided
by the 1,699 slots between them. The second rate also caps the migration's entry bytes in each block at the
entry bytes of that block's ordinary traffic, counted the same way; with the cap at the ordinary transactions'
bytes alone it is about 19.5 million accounts a day.

For the order of inclusion, a leader that runs Agave ranks a transaction by its priority, which is reward x
1,000,000 / (1 + cost), rounded down, and takes the cost at the transaction's limits
(`core/src/transaction_priority.rs`). The reward is the fee less the burnt half of the signature fees, 2,500
lamports per signature (`runtime/src/bank/fee_distribution.rs`). The migration's transactions ask for 4,900 and
3,900 compute units and for 98,304 bytes of loaded account data, which makes 7,177 and 6,177 cost units, and the
charge for a verification is added (12,832 and 11,832). The client sets these limits from its first
transactions: the most compute units that one of them used plus a tenth, rounded up to a hundred, and the
account data that a simulation loaded, rounded up to whole 32 KiB pages. Finding 6 holds for these limits, and
an enrollment that asked for more would rank lower. With the same compute-unit limits and 64 MiB of loaded data,
62.1 % of the ordinary transactions would rank below it; with the limits of the client's first transactions
(60,000 compute units and 1,048,576 bytes), 43.1 %; with 200,000 compute units and 64 MiB, 17.3 %.

For an ordinary transaction, `tools/parse_blocks.py` reads the limits from the transaction's bytes and computes
the cost at them by the rules of Agave's cost model (`cost-model/src/cost_model.rs`). A legacy or v0 transaction
states its limits in instructions of the compute-budget program. If none sets the compute-unit limit, it is
ranked at 200,000 compute units for every instruction, or at 3,000 for an instruction of a program on Agave's
built-in list, up to 1,400,000 in all. That list (`builtins-default-costs/src/lib.rs`) holds the system and
compute-budget programs, the four program loaders and the Ed25519 and secp256k1 precompiles. If none sets the
loaded-data limit, it is ranked at 64 MiB of loaded account data, which is 16,384 cost units. Its priority fee
is the price it states for a compute unit, in millionths of a lamport, times its compute-unit limit, rounded up
to a lamport. A v1 transaction states its limits and its priority fee, in lamports, in fields of its own,
without instructions, and a limit it does not state is zero. The reward is the fee less 2,500 lamports for every
signature, including the 1,867 signatures in the sample that a precompile verifies.

Three kinds of check stand behind these numbers. First, `tools/parse_blocks.py` holds every sampled transaction
to three conditions against what the node recorded. The fee is the signature fees plus the priority fee that the
script read or computed. The compute units used are within the compute-unit limit. And the cost units charged
are the script's figure for signatures, write locks and instruction data, plus the compute units used, plus 8
for each of a whole number of 32 KiB pages within the loaded-data limit. The first condition tests the
compute-unit limit only where the fee depends on it, for the legacy and v0 transactions that state a price above
zero: 175,195 of the sampled transactions (27.4 %). Second, in each of the 1,700 blocks the rewards add up to
the fee reward the block reports. Third, `cost-check/`, a small program built on the crates that Agave itself is
built from (`solana-cost-model`, `solana-runtime-transaction` and `solana-fee` 4.4.1), takes the same bytes and
gives the same limits, cost and fee, and with them the same reward and priority, for all 640,488 transactions
(`results/cost_check.json`).

In the sample 92.7 % of the transactions state a compute-unit limit and 59.3 % a limit on loaded data. The
median transaction uses 21.6 % of its compute-unit limit (5,328 transactions have a limit of zero and are left
out of this median). 211,352 of the sampled transactions (33.0 %) failed: each is in its block and paid its fee.
A transaction that failed used a median of 8.1 % of its compute-unit limit, one that succeeded 34.9 %. For the
median transaction the cost at the limits is 6.2 times the cost it used; summed over all transactions it is 4.2
times.

Ranked by the cost units they used, at the fees they paid, the shares of finding 6 would be 39.8 %, 49.6 % and
78.3 %. The fee is held fixed in that count. A legacy or v0 transaction pays its price for every compute unit of
its limit, so with a limit equal to its use and the same price it would pay less; the shares are then 43.6 %,
53.0 % and 82.5 %. Among the 429,136 transactions that succeeded, 76.5 % rank below the enrollment at their
limits and 43.4 % by the cost units they used, at the fees they paid.

At the limits, the shares of finding 6 (80.2 %, 89.0 % and 91.0 %) also move with the pricing of the migration's
transactions. Without the charge, which is how those transactions run today, they are 82.6 %, 91.4 % and 93.6 %.
With the charge and a signature fee for the ML-DSA-44 signature, as a precompile's signatures pay, they are 83.0
%, 91.7 % and 93.9 %. At their present limits, the transactions that rank below the enrollment of finding 6 pay
a median of 5,526 lamports today, and the fees they would add to rank level with it sum to 110.9 % of the fees
that all sampled transactions paid.

The same priority also decides which transactions such a leader drops for lack of room. When its buffer of
waiting transactions (100,000 at most, `core/src/banking_stage.rs`) is nearly full, it discards arrivals at or
below the lowest priority in the buffer, and when the buffer is full it removes the waiting transactions of
lowest priority (`core/src/sigverify.rs` and, under `core/src/banking_stage/transaction_scheduler/`,
`scheduler_controller.rs` and `transaction_state_container.rs`). Two other drops do not look at priority. The
leader clears what still waits when its slots are over and it is not due to lead again soon
(`core/src/banking_stage/decision_maker.rs`), and it removes a waiting transaction that is no longer valid, for
example because its blockhash has expired.

Payments outside the fee are not part of that rule. 29,936 transactions, in 1,684 of the 1,700 blocks, add to
the balance of one of Jito's eight tip accounts (`data/jito_tip_accounts.json`): 3.38 SOL in the sample, against
15.49 SOL of fee rewards. With each transaction's tip counted as reward, the shares of finding 6 are 79.5 %,
88.7 % and 90.5 %. Transactions that the block engine handed to the leader as one group with a tipping
transaction (a bundle) cannot be told from the blocks.

## What is measured, and what is not

- **Measured on the node:** transaction sizes, compute units and cost units; the number of transactions a block
  holds at the limit; the program's rules; the compute units of a simulated verification inside the virtual
  machine.
- **Measured on mainnet:** what ordinary traffic uses of each block, the limits its transactions ask for and the
  fees and tips they pay, the slot time, and which per-block limits are active.
- **Read from Agave's source (github.com/anza-xyz/agave, tag v4.4.1, commit 5bb30402):** the per-block limits
  (`runtime/src/slot_params.rs`), the 56 bytes of entry overhead (`core/src/banking_stage/consumer.rs`), the
  prices of signature verification (`cost-model/src/block_cost_limits.rs`), the signature fee of a precompile's
  signatures (`fee/src/lib.rs`), the half of the signature fees that is burnt
  (`runtime/src/bank/fee_distribution.rs`), the rule by which a leader ranks transactions
  (`core/src/transaction_priority.rs`), the rules by which it drops waiting transactions
  (`core/src/banking_stage.rs`, `core/src/banking_stage/decision_maker.rs`, `core/src/sigverify.rs` and, under
  `core/src/banking_stage/transaction_scheduler/`, `scheduler_controller.rs` and
  `transaction_state_container.rs`), and the limits and the cost it ranks them at
  (`cost-model/src/cost_model.rs`, `compute-budget-instruction/src/compute_budget_instruction_details.rs`,
  `runtime-transaction/src/transaction_meta.rs`, `builtins-default-costs/src/lib.rs`, and
  `program-runtime/src/execution_budget.rs` for the default values). The layout of a v1 transaction is read from
  the crate `agave-transaction-view` 7.0.0 (github.com/anza-xyz/agave-sdk), which that tag depends on.
- **Charged by rule, not executed on chain:** the two ML-DSA-44 verifications of an account.
- **Taken from a third party:** the address counts (Glassnode, read on 26 November 2026; the pages give no date
  for the figures). They count addresses of every kind, so each is an upper bound for key-controlled wallets.

The run uses one node. Its blocks of 10 MiB were built and executed on one machine and were not sent between
nodes; the block of the mainnet sample with the most bytes has 1,567,161 bytes of transactions. The second rate
needs only blocks twice the size of today's.

The per-block limits and the ranking rule are read from Agave's source. The rates apply the limits to every
slot, and finding 6 applies the rule to every sampled transaction. That is an assumption for part of the stake:
80.6 % reported version 4.4.0 or 4.4.1, and 18.5 % reported other version lines (26.x and 0.1.x) with other
feature sets, whose leaders may pack and order blocks by other rules. `solana feature status` reports version
numbers only: it does not tell Agave from the modified Agave clients that report the same numbers.

The client sends through the node's own RPC; what mainnet's leaders accept from one sender each second is not
part of the run. The local node sets the rent-exempt minimum at the genesis rate of 6,960 lamports per byte;
mainnet's rate is 5,080, and the deposit above is mainnet's. The run covers the enrollment step only: the
paper's recovery of an account by seed proof, after the old signatures are retired, was not run on Solana.

## Reproduce

Needs the Agave v4.4.1 release (`solana`, `solana-test-validator`, `solana-keygen` and its `cargo-build-sbf`,
which reports version 4.5.0), Rust (1.98.1 or later for `cost-check/`, as the Agave crates require) and Python
3.10 or later. The run used an Intel Core i9-12950HX (24 threads) under WSL2 with 50 GiB of memory.

```bash
cd solana
export WORK=$PWD/work     # the run kept WORK in memory (/dev/shm); under WSL2 keep it off the Windows drives
cargo-build-sbf --manifest-path program/Cargo.toml --sbf-out-dir "$WORK/out"
cargo build --release --manifest-path harness/Cargo.toml
harness/target/release/pqsol bench-verify 2000 > results/bench_verify.json

solana feature status -u mainnet-beta --output json > data/features_mainnet.json    # start_node.sh and cost_check.py read it
bash tools/start_node.sh --alpenglow --slots-per-epoch 32
bash tools/run_local.sh 40017 run-200ms run-200ms        # then copy $WORK/run/run-200ms to results/local-run-200ms
bash tools/start_node.sh --alpenglow --ticks-per-slot 256
bash tools/run_local.sh 60017 run-genesis run-genesis    # likewise to results/local-run-genesis
kill "$(cat "$WORK/run/node.pid")"                       # stop the node

python3 tools/sample_blocks.py sample FIRST_SLOT 1700    # FIRST_SLOT: a finalized slot; about 75 minutes on the public RPC
python3 tools/tip_accounts.py data/jito_tip_accounts.json
python3 tools/parse_blocks.py sample data
cargo build --release --manifest-path cost-check/Cargo.toml      # Agave's cost model on the same transactions
python3 tools/cost_check.py feed sample data | cost-check/target/release/cost-check \
  | python3 tools/cost_check.py compare data results/cost_check.json
python3 tools/mainnet_params.py data/mainnet_params.json # after the sample: its per-minute rates must cover the sampled slots
python3 tools/analyze.py data results
```

The verification inside the virtual machine, in the same shell (it needs `WORK`, the client, and the registry
program in `$WORK/out`, which `tools/start_node.sh` always loads):

```bash
cargo test --release --manifest-path program-verify/Cargo.toml     # the comparisons with fips204
cargo-build-sbf --manifest-path program-verify/Cargo.toml --sbf-out-dir "$WORK/out-verify"
ID=$(solana-keygen pubkey "$WORK/out-verify/pq_verify_in_vm-keypair.json")
bash tools/start_node.sh --alpenglow --slots-per-epoch 32 --bpf-program "$ID" "$WORK/out-verify/pq_verify_in_vm.so" \
  --compute-unit-limit 200000000
# as in the measurement, wait for slot 96: in its first slot the node cannot call a program loaded at genesis
solana -u http://127.0.0.1:8899 slot >/dev/null && until [ "$(solana -u http://127.0.0.1:8899 epoch 2>/dev/null || echo 0)" -ge 3 ]; do sleep 1; done
harness/target/release/pqsol verify-in-vm http://127.0.0.1:8899 "$WORK/keys/funder.json" "$ID" 5 1400000
kill "$(cat "$WORK/run/node.pid")"                                  # stop the node
cargo-build-sbf --manifest-path program-verify-fips204/Cargo.toml --sbf-out-dir "$WORK/out-fips204"   # the control
```

The `verify-in-vm` command prints its simulations, and the build of the control prints the frame messages. No
script writes `results/verify-in-vm.json`: it is the record of this run. It holds the simulations of that
command at the node's own limit and at the lifted limit under `runs`, from which `tools/analyze.py` takes the
compute units, next to the test counts, the facts of the builds and the control.

The registry program builds to the same bytes from an empty target directory (`results/build_check.txt`); its
SHA-256, `f713868ad4904fe21aea7045aac5dfc14b328d69068dc856cc44e115ced9b4ce`, and the versions of the tools
(platform-tools v1.57) are in each run's `build_info.txt`.

## Files

| Path | Content |
|---|---|
| `program/` | the registry program |
| `program-verify/` | ML-DSA-44 verification inside the virtual machine, with its tests |
| `program-verify-fips204/` | control: the same instruction verified by the `fips204` crate, which does not run in the virtual machine |
| `harness/` | the client `pqsol`: wallets, ML-DSA-44 keys, v1 transactions, block statistics |
| `cost-check/` | Agave's cost model on transaction bytes: the limits, cost, fee, reward and priority of each transaction |
| `tools/` | node start, local run, mainnet sample, per-block limits, cost check, rate |
| `data/mainnet_blocks.csv` | the sampled mainnet slots, one row each |
| `data/mainnet_txs.csv.gz` | the sampled transactions, one row each: size, fee, cost units, tip, whether it failed, its two limits and whether it states them, the price it states, and its cost at the limits |
| `data/mainnet_block_index.jsonl` | size and SHA-256 of every sampled block as downloaded (the blocks themselves are not in the repository) |
| `data/mainnet_params.json` | mainnet's limits, the feature accounts that select them, the feature account on which the default compute-unit limits of section 5 rely, the cluster's transaction rate |
| `data/features_mainnet.json` | `solana feature status` of mainnet on the day of the run |
| `data/jito_tip_accounts.json` | the tip accounts that Jito's block engine names |
| `data/populations.json` | the address counts and their source |
| `results/local-run-*/` | each local run: `run.json`, `blocks.csv`, the node's flags, features and genesis hash, `build_info.txt` |
| `results/bench_verify.json` | verification times on the run's machine |
| `results/verify-in-vm.json` | the verification inside the virtual machine: tests, build, simulations, and the control |
| `results/build_check.txt` | two builds of the registry program and their SHA-256 |
| `results/cost_check.json` | the comparison of every sampled transaction with Agave's cost model |
| `results/SOLANA.json`, `results/SOLANA.md` | the rates and the days |

## Next

- A run with several nodes and limited links between them, to measure how blocks of this size travel.
- A count of key-controlled wallets from a ledger snapshot, in place of the third-party address counts.
- The recovery step on Solana: a seed proof for Ed25519 keys and its cost in a transaction.
- ML-DSA-44 verification inside the validator, in place of the charge by rule.
- A verifier for the virtual machine with a hash function written for it, to see whether one verification fits
  in one transaction.
