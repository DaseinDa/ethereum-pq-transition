# Submission outcomes in the local profile

`eth_sendRawTransaction` and `eth_sendRawTransactionSync` share decoding and
admission for PQ transaction bytes. Sync waits for a receipt only after one
successful admission; a receipt timeout keeps geth's ordinary response.
GraphQL `sendRawTransaction` uses that same path for PQ types.

Errors carry exactly five fields: `failureClass`, `reason`, `protocolCode`,
`culprit`, and `pendingFetch`. JSON-RPC puts them in `error.data`; GraphQL puts
them in `errors[].extensions`, without a JSON-RPC envelope. Invalid RPC/DATA
arguments retain the framework's ordinary parameter error.

A protocol rejection is `-32003` with the fixed reason/code pair, including
sponsor pending limits, expiry, bans, pricing and version limits. A capacity,
rate or work-budget refusal without a protocol code is `-32005 LOCAL_LIMIT`.
An unavailable verifier or unknown local failure is `-32002 LOCAL_UNAVAILABLE`,
never `INVALID_PROOF`. The ordinary transaction gas cap is `-32003
STOCK_REJECTION`, with a null protocol code. A duplicate pending recovery is
`REPLACEMENT_UNDERPRICED`; duplicate ordinary PQ transactions use the stock
pool outcome. Errors do not authorize a wallet to stop tracking a previously
submitted authorization.

This profile executes enrollment (`0x7d`), PQ transactions (`0x7c`), Route A
recovery (`0x7e`) and, where the genesis configures `aggregateResearch`, the
four-owner batch recovery (`0x7f`). It does not enable Route B lanes: the
decoding-only `0x7b` envelope distinguishes malformed encoding from unsupported
capability and provides no lane assembly or fact verification. No Route B
verifier is live in the demo genesis. The aggregate C interface is specified in
[Batch proof verification interface](BATCH-VERIFIER.md); its public input is the
complete ordered batch statement, while its Keccak hash is only the batch ID.

Sponsor policy applies the cumulative balance bound, count, horizon and ban
before sponsor signature verification and before replacement/tip outcomes.
Only the admission conditions apply at admission; a reset does not reapply
count, horizon or ban to an already-held item. The ordering fix does not weaken
signature checks, proof checks, fees or limits. A tentative replacement never
removes an existing transaction before the new proof is accepted.
