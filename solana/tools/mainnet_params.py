"""Record mainnet's per-block limits and the on-chain state that selects them.

python -X utf8 -I mainnet_params.py OUT_FILE [RPC_URL]
python -X utf8 -I mainnet_params.py --features OUT_FILE [RPC_URL]

The limits are constants of the validator source (Agave v4.4.1, commit 5bb304027fe1a166b02cb26dc8c161593f416fca):
  runtime/src/slot_params.rs            the parameter table per slot-time regime (entry bytes, cost limits)
  cost-model/src/block_cost_limits.rs   30 cost units per microsecond; the costs of a transaction signature, of a
                                        signature that the Ed25519 precompile verifies, of a write lock
  core/src/banking_stage/consumer.rs    56 bytes of entry overhead per recorded batch
Which row of the table applies is decided by feature accounts on chain. This script reads those accounts, the
rent-exempt minimum of the two record sizes, the version of the node that answers, and the cluster's transaction
rate per minute for as long back as that node keeps it (720 minutes at most), and writes them next to the
constants.

The second form reads only the feature accounts again, into a file that the first form wrote. Every feature that
the file holds must read as it did, a feature that the file lacks is added, and the time of this read is recorded
as features_read_at_unix. Nothing else in the file changes. It adds a feature to the record of a sample whose
per-minute rates the node no longer keeps.
"""
import base64
import json
import sys
import time
import urllib.request

arguments = [a for a in sys.argv[1:] if a != "--features"]
features_only = "--features" in sys.argv[1:]
out_file = arguments[0]
rpc = arguments[1] if len(arguments) > 1 else "https://api.mainnet-beta.solana.com"

# feature gates, in the order of runtime/src/slot_params.rs, with the table row each one selects; a row applies
# from the first slot of the epoch after its gate's activation
SLOT_TIME_GATES = [
    ("reduce_slot_time_to_350ms", "iBRL5RuWhw4yqaAZu96RUULHckHTZAoe2b77qaV38JZ",
     {"ns_per_slot": 350_000_000, "cost_tracker_limits": [21_000_000, 52_500_000, 87_500_000], "max_entry_bytes_per_slot": 18_350_080}),
    ("reduce_slot_time_to_300ms", "iBRLL3k18HST852F1Mf3Lv83waTNQmmqvKDxvYGwQFL",
     {"ns_per_slot": 300_000_000, "cost_tracker_limits": [18_000_000, 45_000_000, 75_000_000], "max_entry_bytes_per_slot": 15_728_640}),
    ("reduce_slot_time_to_250ms", "iBRLMc81UjRa8fn8A6eE8bJTnRbgQoPTynM51akENCV",
     {"ns_per_slot": 250_000_000, "cost_tracker_limits": [15_000_000, 37_500_000, 62_500_000], "max_entry_bytes_per_slot": 13_107_200}),
    ("reduce_slot_time_to_200ms", "iBRLjhJnkmDZgNoZRDMW11d8ZV7HvsL3vAyRjZB5npW",
     {"ns_per_slot": 200_000_000, "cost_tracker_limits": [12_000_000, 30_000_000, 50_000_000], "max_entry_bytes_per_slot": 10_485_760}),
]
LEGACY = {"ns_per_slot": 400_000_000, "cost_tracker_limits": [24_000_000, 60_000_000, 100_000_000], "max_entry_bytes_per_slot": 20 * 1024 * 1024}
OTHER_GATES = [
    ("raise_block_limits_to_100m", "P1BCUMpAC7V2GRBRiJCNUgpMyWZhoqt3LKo712ePqsz"),
    ("alpenglow", "A1pengvuM6JEcyNuTnMqepBKhwHE3N6PmUrdATGawhJS"),
    ("enable_tx_v1", "txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL"),
    # with this gate the vote program is no longer a built-in program in the default compute-unit limit of a
    # transaction (builtins-default-costs/src/lib.rs); parse_blocks.py relies on it
    ("bls_pubkey_management_in_vote_account", "AnAP9zPV4KL7czAPQbFhpDKV2tx7g4UGNbK9wvXwjaRo"),
]
RECORD_ENROLLED = 42
RECORD_ACTIVATED = 42 + 1312


def call(method, params=None):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params or []}).encode()
    req = urllib.request.Request(rpc, data=body, headers={"Content-Type": "application/json", "User-Agent": "params-reader/1.0"})
    with urllib.request.urlopen(req, timeout=60) as r:
        doc = json.load(r)
    if "error" in doc:
        raise RuntimeError(doc["error"])
    return doc["result"]


def activation_slot(feature_id):
    """Activation slot of a feature account, or None if it is absent or pending."""
    value = call("getAccountInfo", [feature_id, {"encoding": "base64", "commitment": "finalized"}])["value"]
    if value is None:
        return None
    data = base64.b64decode(value["data"][0])
    return int.from_bytes(data[1:9], "little") if data and data[0] == 1 else None


features = {}
regime = dict(LEGACY, selected_by="genesis (400 ms)")
for name, fid, row in SLOT_TIME_GATES:
    slot = activation_slot(fid)
    features[name] = {"id": fid, "activated_at_slot": slot}
    if slot is not None:
        regime = dict(row, selected_by=name)
for name, fid in OTHER_GATES:
    features[name] = {"id": fid, "activated_at_slot": activation_slot(fid)}

if features_only:
    with open(out_file, encoding="utf-8") as f:
        stored = json.load(f)
    for name, entry in stored["features"].items():
        assert features[name] == entry, f"the feature account of {name} reads differently now"
    assert stored["slot_regime"] == regime, "the feature accounts select another row of the table now"
    merged = {}
    for key, value in stored.items():
        if key == "features_read_at_unix":
            continue
        merged[key] = features if key == "features" else value
        if key == "features":
            merged["features_read_at_unix"] = int(time.time())
    with open(out_file, "w", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(merged, indent=2) + "\n")
    print(json.dumps({"added": [name for name in features if name not in stored["features"]],
                      "features_read_at_unix": merged["features_read_at_unix"], "features": features}, indent=1))
    raise SystemExit(0)

account_cost, block_cost, allocated = regime["cost_tracker_limits"]
if features["raise_block_limits_to_100m"]["activated_at_slot"] is not None:
    # SlotParams::cost_limits: both cost limits scale by 100 / 60
    account_cost, block_cost = account_cost * 100 // 60, block_cost * 100 // 60

# one sample per minute, 720 at most
samples = call("getRecentPerformanceSamples", [720])
epoch = call("getEpochInfo", [{"commitment": "finalized"}])
now = int(time.time())
out = {
    "read_at_unix": now,
    "rpc": rpc,
    "genesis_hash": call("getGenesisHash"),
    "rpc_node_version": call("getVersion"),
    "finalized_slot": epoch["absoluteSlot"],
    "epoch": epoch["epoch"],
    "source": {"repository": "https://github.com/anza-xyz/agave", "tag": "v4.4.1", "commit": "5bb304027fe1a166b02cb26dc8c161593f416fca",
               "files": ["runtime/src/slot_params.rs", "cost-model/src/block_cost_limits.rs", "core/src/banking_stage/consumer.rs",
                         "runtime/src/bank/entry_bytes_budget.rs"]},
    "features": features,
    "features_read_at_unix": now,
    "slot_regime": regime,
    "max_entry_bytes_per_slot": regime["max_entry_bytes_per_slot"],
    "block_cost_limit": block_cost,
    "writable_account_cost_limit": account_cost,
    "allocated_account_data_bytes_per_block": allocated,
    "entry_overhead_bytes": 56,
    "cost_units_per_microsecond": 30,
    "signature_cost_units": 720,
    "ed25519_precompile_signature_cost_units": 2400,
    "write_lock_cost_units": 300,
    "instruction_data_bytes_per_cost_unit": 4,
    "max_v1_transaction_bytes": 4096,
    "record_bytes_enrolled": RECORD_ENROLLED,
    "record_bytes_activated": RECORD_ACTIVATED,
    "rent_exempt_lamports_enrolled_record": call("getMinimumBalanceForRentExemption", [RECORD_ENROLLED]),
    "rent_exempt_lamports_activated_record": call("getMinimumBalanceForRentExemption", [RECORD_ACTIVATED]),
    "recent_performance_samples": [{"slot": s["slot"], "slots": s["numSlots"], "seconds": s["samplePeriodSecs"],
                                    "transactions": s["numTransactions"]} for s in samples],
}
with open(out_file, "w", encoding="utf-8", newline="\n") as f:
    f.write(json.dumps(out, indent=2) + "\n")
print(json.dumps({k: out[k] for k in ("slot_regime", "max_entry_bytes_per_slot", "block_cost_limit", "writable_account_cost_limit",
                                       "rent_exempt_lamports_activated_record", "features")}, indent=1))
