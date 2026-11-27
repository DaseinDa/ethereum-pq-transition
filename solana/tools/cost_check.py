"""Check the limits, costs and fees of the sampled transactions against Agave's own crates, and the rewards and
priorities that follow from them.

python -X utf8 -I cost_check.py feed SAMPLE_DIR DATA_DIR | COST_CHECK | python -X utf8 -I cost_check.py compare DATA_DIR OUT_JSON

COST_CHECK is the program built from cost-check/ (cargo build --release --manifest-path cost-check/Cargo.toml). It
calls the crates that Agave v4.4.1 itself is built from: agave-transaction-view reads the transaction,
solana-runtime-transaction reads its limits, solana-cost-model gives its cost and solana-fee its fee. From these it
computes the reward and the priority by Agave's two formulas.

feed     writes, for cost-check, the features that DATA_DIR/features_mainnet.json lists as inactive on mainnet and then
         every transaction of the sample in SAMPLE_DIR (index.jsonl and raw/<slot>.json.gz), as it is on the wire.
compare  reads the answers of cost-check and compares each with the transaction's row in DATA_DIR/mainnet_txs.csv.gz,
         which parse_blocks.py wrote: version, signatures, the signatures that a precompile verifies, the two limits,
         the cost at the limits and the fee, and the reward and the priority that analyze.py derives from the row.
         Writes OUT_JSON, which also holds the SHA-256 of the rows it compared, and ends with an error if any
         transaction disagrees.
"""
import csv
import gzip
import hashlib
import json
import re
import sys
from pathlib import Path

BURN = 2500
PRIORITY_MULTIPLIER = 1_000_000
U64_MAX = 2**64 - 1
CRATES = ("agave-feature-set", "agave-transaction-view", "solana-cost-model", "solana-fee", "solana-runtime-transaction",
          "solana-svm-transaction", "solana-transaction")


def inactive_features(data):
    listed = json.loads((data / "features_mainnet.json").read_text(encoding="utf-8"))["features"]
    assert all(f["status"] in ("active", "inactive") for f in listed), (
        "a feature is pending on mainnet: it becomes active when the next epoch begins; "
        "read the status again after that, then sample")
    return sorted(f["id"] for f in listed if f["status"] == "inactive")


def feed(sample, data):
    out = sys.stdout
    for feature in inactive_features(data):
        out.write(f"I {feature}\n")
    index = {}
    for line in (sample / "index.jsonl").read_text(encoding="utf-8").splitlines():
        rec = json.loads(line)
        if rec["status"] in ("ok", "skipped") or rec["slot"] not in index:
            index[rec["slot"]] = rec
    for slot in sorted(index):
        if index[slot]["status"] != "ok":
            continue
        payload = gzip.decompress((sample / "raw" / f"{slot}.json.gz").read_bytes())
        assert hashlib.sha256(payload).hexdigest() == index[slot]["sha256"], slot
        for number, t in enumerate(json.loads(payload)["transactions"]):
            out.write(f"T {slot} {number} {t['transaction'][0]}\n")


def compare(data, out_path):
    text = gzip.decompress((data / "mainnet_txs.csv.gz").read_bytes())
    rows = list(csv.DictReader(text.decode("utf-8").splitlines()))
    answers = sys.stdin.buffer.read()
    agave = list(csv.DictReader(answers.decode("utf-8").splitlines()))
    assert len(agave) == len(rows), f"cost-check gave {len(agave)} answers, the data file has {len(rows)} transactions"
    fields = ("slot", "version", "transaction signatures", "signatures that a precompile verifies", "compute-unit limit",
              "limit on loaded account data", "cost at the limits", "fee", "reward", "priority")
    disagreements = dict.fromkeys(fields, 0)
    same_cost_both_ways = simple_votes = costs = rewards = 0
    for row, a in zip(rows, agave):
        precompile = sum(int(a[k]) for k in ("ed25519_signatures", "secp256k1_signatures", "secp256r1_signatures"))
        reward = int(row["fee_lamports"]) - BURN * (int(row["signatures"]) + int(row["precompile_signatures"]))
        priority = min(reward * PRIORITY_MULTIPLIER, U64_MAX) // (int(row["cost_units_at_limits"]) + 1)
        same = (row["slot"] == a["slot"], row["version"] == a["version"], row["signatures"] == a["transaction_signatures"],
                int(row["precompile_signatures"]) == precompile, row["compute_unit_limit"] == a["compute_unit_limit"],
                row["loaded_accounts_data_size_limit"] == a["loaded_accounts_data_size_limit"],
                row["cost_units_at_limits"] == a["cost"], row["fee_lamports"] == a["fee_lamports"],
                reward == int(a["reward_lamports"]), priority == int(a["priority"]))
        for field, ok in zip(fields, same):
            disagreements[field] += not ok
        same_cost_both_ways += a["cost"] == a["cost_by_calculate_cost"]
        simple_votes += a["simple_vote"] == "1"
        costs += int(a["cost"])
        rewards += int(a["reward_lamports"])
    lock = (Path(__file__).resolve().parent.parent / "cost-check" / "Cargo.lock").read_text(encoding="utf-8")
    versions = {name: re.search(rf'name = "{name}"\nversion = "([^"]+)"', lock).group(1) for name in CRATES}
    record = {
        "what": "every sampled transaction, as it is on the wire, given to the crates that Agave is built from (cost-check/), "
                "and the answers compared with the transaction's row in data/mainnet_txs.csv.gz",
        "steps": "those of calculate_priority_from_bytes and calculate_priority_and_cost in core/src/transaction_priority.rs, "
                 "Agave v4.4.1; the limits, the cost and the fee come from the crates, and cost-check computes the reward as "
                 "Bank::calculate_reward_and_burn_fee_details does and the priority as calculate_priority_and_cost does",
        "crates": versions,
        "features_switched_off": len(inactive_features(data)),
        "features_source": "data/features_mainnet.json: the features that solana feature status lists as inactive on mainnet",
        "transactions": len(rows),
        "sha256_of_the_rows_compared": hashlib.sha256(text).hexdigest(),
        "compared": list(fields),
        "transactions_that_disagree": disagreements,
        "transactions_whose_cost_is_the_same_by_calculate_cost": same_cost_both_ways,
        "simple_vote_transactions": simple_votes,
        "sum_of_the_costs_at_the_limits": costs,
        "sum_of_the_rewards_lamports": rewards,
        "sha256_of_the_answers": hashlib.sha256(answers).hexdigest(),
    }
    out_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, indent=2))
    assert not any(disagreements.values()), "a transaction disagrees with Agave's cost model"
    assert same_cost_both_ways == len(rows), "calculate_cost gives another cost than the priority's cost"


if sys.argv[1] == "feed":
    feed(Path(sys.argv[2]), Path(sys.argv[3]))
elif sys.argv[1] == "compare":
    compare(Path(sys.argv[2]), Path(sys.argv[3]))
else:
    raise SystemExit(__doc__)
