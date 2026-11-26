"""Enrollment rate and days on Solana mainnet from the sampled blocks and the local runs.

python -X utf8 -I analyze.py DATA_DIR RESULTS_DIR

Reads
  DATA_DIR/mainnet_blocks.csv          one row per sampled slot (parse_blocks.py)
  DATA_DIR/mainnet_txs.csv.gz          one row per sampled transaction (parse_blocks.py)
  DATA_DIR/mainnet_params.json         mainnet's limits and the sources they were read from
  DATA_DIR/populations.json            address counts by balance, with their sources
  RESULTS_DIR/local-run-*/             the local runs; local-run-200ms is the one in mainnet's slot parameters
  RESULTS_DIR/bench_verify.json        ML-DSA-44 and Ed25519 verification times on the run's machine
  RESULTS_DIR/verify-in-vm.json        one ML-DSA-44 verification inside the virtual machine (program-verify)
and writes RESULTS_DIR/SOLANA.json and RESULTS_DIR/SOLANA.md.

Rate. A block offers the migration the entry bytes and the cost units that ordinary traffic leaves under the two
per-block limits. An account needs one enrollment and one activation. Its bytes are the two transactions plus the
entry overhead of each; its cost units are the two measured costs plus the charge for two ML-DSA-44 verifications.
The charge is Solana's price for a signature that its Ed25519 precompile verifies, 2,400 cost units, times the
ratio of the ML-DSA-44 and the Ed25519 verification times on the run's machine. Accounts per slot is the mean over
every sampled slot of min(free bytes / bytes per account, free cost / cost per account); a skipped slot offers no
room. The second rate also caps the migration's entry bytes in a block at the entry bytes of that block's
ordinary traffic.

Order of inclusion. A leader that runs Agave gives a transaction the priority reward x 1,000,000 / (1 + cost),
rounded down, and takes the cost at the limits the transaction asks for (core/src/transaction_priority.rs in
Agave v4.4.1). The reward is the fee less the burnt half of the signature fees. For the migration the reward and
the limits are known exactly (run.json records the limits its transactions ask for), and the charge for a
verification is added to its cost. For an ordinary transaction the sample has the cost units it used, which are at most the cost at
the limits it asked for, and its reward computed here counts 2,500 burnt lamports per transaction signature,
which is at least the true reward (signatures that a precompile verifies burn more). Both errors make an
ordinary transaction rank higher here than that rule ranks it, so by fees alone the share of ordinary traffic
that ranks below the migration is a lower bound, and so is the fee each such transaction would add. A tip is not
part of the fee: the script also reports the shares with every transaction's tip counted as reward.
"""
import csv
import gzip
import json
import math
import statistics
import sys
from pathlib import Path

data = Path(sys.argv[1])
results = Path(sys.argv[2])

params = json.loads((data / "mainnet_params.json").read_text(encoding="utf-8"))
populations = json.loads((data / "populations.json").read_text(encoding="utf-8"))
run = json.loads((results / "local-run-200ms" / "run.json").read_text(encoding="utf-8"))
bench = json.loads((results / "bench_verify.json").read_text(encoding="utf-8"))

ENTRY_BYTES = params["max_entry_bytes_per_slot"]
BLOCK_COST = params["block_cost_limit"]
ENTRY_OVERHEAD = params["entry_overhead_bytes"]
CU_PER_US = params["cost_units_per_microsecond"]
ED25519_PRECOMPILE_COST = params["ed25519_precompile_signature_cost_units"]
LAMPORTS_PER_SIGNATURE = 5000
PAGE = 32 * 1024
BURN = 2500
MAX_TX_COMPUTE_UNITS = 1_400_000
PRIORITY_MULTIPLIER = 1_000_000


def priority(reward, cost):
    """Agave's priority of a transaction (core/src/transaction_priority.rs): whole numbers, rounded down."""
    return reward * PRIORITY_MULTIPLIER // (cost + 1)


# Sums of floating-point numbers use math.fsum, which rounds the exact sum once: the result is the same on every
# Python version (the built-in sum changed its method in Python 3.12). p90 is the nearest-rank percentile: the
# smallest value with at least nine tenths of the values at or below it.
def spread(values):
    v = sorted(values)
    if not v:
        return None
    return {"min": v[0], "median": statistics.median(v), "mean": math.fsum(v) / len(v), "p90": v[-(-len(v) * 9 // 10) - 1],
            "max": v[-1]}


# ---- measured transactions (every one of the run's enrollments and activations has the same size and cost)
tx = run["transactions"]
for kind in ("enroll", "activate"):
    for field in ("bytes", "cost_units", "compute_units", "fee_lamports"):
        assert tx[kind][field]["min"] == tx[kind][field]["max"], (kind, field)
    assert tx[kind]["failed"] == 0, kind
enroll_bytes, activate_bytes = tx["enroll"]["bytes"]["min"], tx["activate"]["bytes"]["min"]
enroll_cost, activate_cost = tx["enroll"]["cost_units"]["min"], tx["activate"]["cost_units"]["min"]
fee_one_signature = tx["enroll"]["fee_lamports"]["min"]
assert fee_one_signature == tx["activate"]["fee_lamports"]["min"] == LAMPORTS_PER_SIGNATURE == 2 * BURN, fee_one_signature

# The charge. Solana prices a signature that its Ed25519 precompile verifies at 2,400 cost units: 30 per microsecond
# of a reference time of 80 microseconds. An ML-DSA-44 verification is charged in proportion: that price times the
# ratio of the two verification times on the run's machine (each the median, over the five rounds, of the round's
# median). The lower variant applies the 30 cost units per microsecond to the time on the run's machine alone.
verify_ns = statistics.median(r["ml_dsa_44_verify_ns"]["median"] for r in bench["rounds"])
ed_ns = statistics.median(r["ed25519_verify_ns"]["median"] for r in bench["rounds"])
verify_charge = round(ED25519_PRECOMPILE_COST * verify_ns / ed_ns)
verify_charge_by_machine_time = round(CU_PER_US * verify_ns / 1000)
assert ED25519_PRECOMPILE_COST == CU_PER_US * 80
assert verify_charge_by_machine_time < verify_charge, (
    "an Ed25519 verification takes 80 microseconds or more on the run's machine: "
    "the charge by machine time is not the lower variant")

bytes_per_account = enroll_bytes + activate_bytes + 2 * ENTRY_OVERHEAD
cost_per_account = enroll_cost + activate_cost + 2 * verify_charge

# the cost a leader ranks the two transactions by: the cost at the limits they ask for, plus the charge
phases = {p["phase"]: p for p in run["phases"]}
simulated = {s["step"]: s for s in run["simulations"]}
cost_at_limits, rank_cost = {}, {}
for kind, executed in (("enroll", enroll_cost), ("activate", activate_cost)):
    asked = phases[kind]["compute_unit_limit"]
    used = tx[kind]["compute_units"]["min"]
    assert asked >= used, kind
    # the loaded-accounts charge is the same at the limit asked for and at the size loaded
    assert phases[kind]["loaded_accounts_data_size_limit"] // PAGE == -(-simulated[kind]["loadedAccountsDataSize"] // PAGE), kind
    cost_at_limits[kind] = executed - used + asked
    rank_cost[kind] = cost_at_limits[kind] + verify_charge
migration_priority = min(priority(fee_one_signature - BURN, c) for c in rank_cost.values())
migration_priority_without_charge = min(priority(fee_one_signature - BURN, c) for c in cost_at_limits.values())

# ---- sampled mainnet slots
rows = list(csv.DictReader((data / "mainnet_blocks.csv").open(encoding="utf-8")))
blocks = [r for r in rows if r["status"] == "ok"]
assert all(r["block_time"] for r in blocks), "a block without a time"
n_slots, n_blocks = len(rows), len(blocks)
times = [int(r["block_time"]) for r in blocks]
seconds = times[-1] - times[0]
# block times have a resolution of one second; the slot time is taken over the slots between the first and the
# last produced block
ms_per_slot = 1000 * seconds / (int(blocks[-1]["slot"]) - int(blocks[0]["slot"]))
slots_per_day = 86_400_000 / ms_per_slot


def col(name):
    return [int(r[name]) for r in blocks]


# the cluster's transaction rate per minute around the sample, to place the sample
perf = params["recent_performance_samples"]
perf_first = min(p["slot"] - p["slots"] + 1 for p in perf)
perf_last = max(p["slot"] for p in perf)
assert perf_first <= int(rows[0]["slot"]) and int(rows[-1]["slot"]) <= perf_last, \
    "the performance samples do not cover the sampled slots"
per_minute = sorted(p["transactions"] / p["seconds"] for p in perf)
window_rate = sum(col("txs")) * 1000 / (n_slots * ms_per_slot)
cluster_rate = {"minutes": len(per_minute), "from_slot": perf_first, "to_slot": perf_last,
                "min": per_minute[0], "median": statistics.median(per_minute), "max": per_minute[-1],
                "share_of_minutes_slower_than_the_sample": sum(1 for v in per_minute if v < window_rate) / len(per_minute)}


def room(cost_units_per_account, cap_at_ordinary=None):
    """Mean accounts per sampled slot. cap_at_ordinary: None, "entry bytes" or "transaction bytes"."""
    per_slot, binds = [], {"bytes": 0, "cost": 0}
    for r in rows:
        if r["status"] != "ok":
            per_slot.append(0.0)
            continue
        used_bytes = int(r["tx_bytes"]) + ENTRY_OVERHEAD * int(r["txs"])
        free_bytes = max(0, ENTRY_BYTES - used_bytes)
        free_cost = max(0, BLOCK_COST - int(r["cost_units"]))
        if cap_at_ordinary == "entry bytes":
            free_bytes = min(free_bytes, used_bytes)
        elif cap_at_ordinary == "transaction bytes":
            free_bytes = min(free_bytes, int(r["tx_bytes"]))
        by_bytes = free_bytes / bytes_per_account
        by_cost = free_cost / cost_units_per_account
        per_slot.append(min(by_bytes, by_cost))
        binds["bytes" if by_bytes <= by_cost else "cost"] += 1
    return math.fsum(per_slot) / len(per_slot), binds


scenarios = {
    "first": "the migration takes every entry byte and cost unit that ordinary traffic leaves under the block limits",
    "second": "as the first, and the migration takes no more entry bytes in a block than that block's ordinary traffic",
}
rates = {}
first_mean, bound_by = room(cost_per_account)
second_mean, _ = room(cost_per_account, "entry bytes")
for name, mean in (("first", first_mean), ("second", second_mean)):
    rates[name] = {"what": scenarios[name], "accounts_per_slot": mean, "accounts_per_second": mean * 1000 / ms_per_slot,
                   "accounts_per_day": mean * slots_per_day}
second_tx_bytes_only = room(cost_per_account, "transaction bytes")[0] * slots_per_day
used_entry_bytes = sum(int(r["tx_bytes"]) + ENTRY_OVERHEAD * int(r["txs"]) for r in blocks)

# how much the two rates depend on the charge for a verification
charge_sensitivity = []
for label, units_charged in ([("none", 0), ("30 cost units per microsecond of the time on the run's machine", verify_charge_by_machine_time),
                              ("the charge", verify_charge)] + [(f"{k} times the charge", k * verify_charge) for k in (2, 5, 10)]):
    mean, binds = room(enroll_cost + activate_cost + 2 * units_charged)
    mean_second, _ = room(enroll_cost + activate_cost + 2 * units_charged, "entry bytes")
    charge_sensitivity.append({"charge": label, "cost_units_per_verification": units_charged,
                               "accounts_per_day": mean * slots_per_day, "accounts_per_day_second_rate": mean_second * slots_per_day,
                               "blocks_where_cost_binds": binds["cost"]})
assert charge_sensitivity[2]["accounts_per_day"] == rates["first"]["accounts_per_day"]
assert charge_sensitivity[2]["accounts_per_day_second_rate"] == rates["second"]["accounts_per_day"]

# ---- order of inclusion: ordinary transactions that Agave's rule ranks below the migration at the signature fee
with gzip.open(data / "mainnet_txs.csv.gz", "rt", encoding="utf-8", newline="") as f:
    txs = list(csv.DictReader(f))
keys = ("transactions", "bytes", "cost_units")
total = dict.fromkeys(keys, 0)
rule_reward = total_fees = tips = tipping = 0
ordinary = []  # (reward by the rule, cost units, bytes, tip) of every sampled transaction
for r in txs:
    fee, sigs, cost, size, tip = (int(r[k]) for k in ("fee_lamports", "signatures", "cost_units", "bytes", "tip_lamports"))
    assert cost > 0, r
    reward = fee - BURN * sigs
    assert reward >= 0, r
    rule_reward += reward
    total_fees += fee
    tips += tip
    tipping += tip > 0
    for k, v in zip(keys, (1, size, cost)):
        total[k] += v
    ordinary.append((reward, cost, size, tip))


def ranked_below(threshold, count_tips=False):
    """The ordinary transactions with a priority below the threshold: their counts, and the fewest whole lamports
    each would add to its fee to reach the threshold."""
    counts, added = dict.fromkeys(keys, 0), []
    for reward, cost, size, tip in ordinary:
        if priority(reward + (tip if count_tips else 0), cost) < threshold:
            added.append(-(-threshold * (cost + 1) // PRIORITY_MULTIPLIER) - reward)
            for k, v in zip(keys, (1, size, cost)):
                counts[k] += v
    return counts, added


below, top_ups = ranked_below(migration_priority)
below_with_tips, _ = ranked_below(migration_priority, count_tips=True)
# two other pricings of the migration's transactions: as they are today, without a charge; and with the charge and a
# signature fee for the ML-DSA-44 signature, as every signature that a precompile verifies pays one
reward_with_a_second_fee = fee_one_signature + LAMPORTS_PER_SIGNATURE - 2 * BURN
priority_with_a_second_fee = min(priority(reward_with_a_second_fee, c) for c in rank_cost.values())
pricings = {}
for name, threshold in (("without_the_charge", migration_priority_without_charge),
                        ("with_the_charge_and_a_signature_fee_for_the_ml_dsa_signature", priority_with_a_second_fee)):
    counts, _ = ranked_below(threshold)
    pricings[name] = {"migration_priority": threshold, "migration_reward_per_cost_unit_lamports": threshold / PRIORITY_MULTIPLIER,
                      "ordinary_below_the_migration_at_least": {k: counts[k] / total[k] for k in keys}}
assert total["transactions"] == sum(col("txs")), "the two files disagree"
assert tips == sum(col("tips_lamports")), "the two files disagree on tips"
reported_reward = sum(col("leader_fee_reward_lamports"))
extra_signatures = (rule_reward - reported_reward) / BURN
assert extra_signatures >= 0 and extra_signatures == int(extra_signatures), extra_signatures
ordering = {
    "source": "core/src/transaction_priority.rs, Agave v4.4.1: priority = reward x 1,000,000 / (1 + cost at the limits "
              "asked for), rounded down",
    "migration_priority": migration_priority,
    "migration_priority_without_the_charge": migration_priority_without_charge,
    "migration_cost_units_at_its_limits": cost_at_limits,
    "migration_cost_units_at_its_limits_with_the_charge": rank_cost,
    "migration_reward_per_cost_unit_lamports": migration_priority / PRIORITY_MULTIPLIER,
    "migration_reward_per_cost_unit_lamports_without_the_charge": migration_priority_without_charge / PRIORITY_MULTIPLIER,
    "ordinary_below_the_migration_at_least": {k: below[k] / total[k] for k in keys},
    "ordinary_below_the_migration_counts": below,
    "fee_top_up_to_rank_level_lamports_at_least": spread(top_ups),
    "fee_top_ups_over_all_ordinary_fees": sum(top_ups) / total_fees,
    "other_pricings_of_the_migration": pricings,
    "ordinary_totals": total,
    "leader_fee_reward_by_rule_lamports": rule_reward,
    "leader_fee_reward_reported_lamports": reported_reward,
    "fee_reward_difference_lamports": rule_reward - reported_reward,
    "precompile_signatures_implied": int(extra_signatures),
    "tips": {"what": "increase of the balance of one of Jito's eight tip accounts (data/jito_tip_accounts.json) by a transaction",
             "transactions_with_a_tip": tipping, "share_of_transactions": tipping / total["transactions"],
             "blocks_with_a_tip": sum(1 for v in col("tips_lamports") if v > 0),
             "tips_lamports": tips, "tips_over_fee_rewards": tips / reported_reward,
             "ordinary_below_the_migration_with_tips_counted": {k: below_with_tips[k] / total[k] for k in keys}},
}

fee_per_account = 2 * fee_one_signature
deposit_per_account = params["rent_exempt_lamports_activated_record"]
days = []
for p in populations["counts"]:
    row = {"population": p["label"], "accounts": p["count"],
           "fees_sol": p["count"] * fee_per_account / 1e9,
           "rent_exempt_deposits_sol": p["count"] * deposit_per_account / 1e9,
           "new_account_data_gib": p["count"] * params["record_bytes_activated"] / 2**30}
    for name in scenarios:
        d = p["count"] / rates[name]["accounts_per_day"]
        row[name] = {"days": d, "hours": d * 24}
    days.append(row)

# ---- the local runs: what a block held at most, and how often
local_runs = {}
for path in sorted(results.glob("local-run-*")):
    d = json.loads((path / "run.json").read_text(encoding="utf-8"))
    lb = list(csv.DictReader((path / "blocks.csv").open(encoding="utf-8")))
    t = d["transactions"]
    top = {k: max(int(b[k]) for b in lb) for k in ("enroll", "activate")}
    args = (path / "validator_args.txt").read_text(encoding="utf-8").split()
    flags = [a for a in ("--alpenglow",) if a in args]
    for name in ("--slots-per-epoch", "--ticks-per-slot"):
        if name in args:
            flags += [name, args[args.index(name) + 1]]
    timed = [b for b in lb if int(b["block_time"]) and int(b["slot"])]  # slot 0 carries the genesis time
    full_slots = {k: [int(b["slot"]) for b in lb if int(b[k]) == top[k]] for k in top}
    local_runs[path.name] = {
        "node_flags": " ".join(flags),
        "wallets": d["wallets"],
        "bulk_wallets": d["phases"][0]["wallets"],
        "sending_connections": d["send_threads"],
        "largest_block": top,
        "blocks_at_the_largest_count": {k: len(full_slots[k]) for k in top},
        "those_blocks_are_consecutive": {k: full_slots[k] == list(range(full_slots[k][0], full_slots[k][-1] + 1)) for k in top},
        "largest_block_tx_bytes": max(int(b["tx_bytes"]) for b in lb),
        "largest_block_cost_units": max(int(b["cost_units"]) for b in lb),
        "landed": {k: t[k]["landed_ok"] for k in top},
        "failed": {k: t[k]["failed"] for k in top},
        "sent_again": {p["phase"]: sum(w["sent"] for w in p["waves"][1:]) for p in d["phases"]},
        "sent_per_second": {p["phase"]: p["waves"][0]["sent"] / p["waves"][0]["send_seconds"] for p in d["phases"]},
        "checks_passed": sum(1 for c in d["checks"] if c.get("pass")), "checks": len(d["checks"]),
        "blocks_read": len(lb),
        "milliseconds_per_slot": 1000 * (int(timed[-1]["block_time"]) - int(timed[0]["block_time"]))
                                 / (int(timed[-1]["slot"]) - int(timed[0]["slot"])),
        "transactions": {k: {"bytes": t[k]["bytes"]["min"], "compute_units": t[k]["compute_units"]["min"],
                             "cost_units": t[k]["cost_units"]["min"]} for k in top},
    }
    for k in top:  # the same program and client in every run
        assert t[k]["bytes"]["min"] == t[k]["bytes"]["max"] == tx[k]["bytes"]["min"], (path.name, k)
        assert t[k]["cost_units"]["min"] == t[k]["cost_units"]["max"] == tx[k]["cost_units"]["min"], (path.name, k)
main = local_runs["local-run-200ms"]
cap = {"enroll": ENTRY_BYTES // (enroll_bytes + ENTRY_OVERHEAD), "activate": ENTRY_BYTES // (activate_bytes + ENTRY_OVERHEAD)}

# ---- the verification executed by a program instead of charged by rule
# runs.default_limit and runs.lifted_limit hold the output of `pqsol verify-in-vm` (its simulations); the figures
# are taken from there, and the record's own summary must agree.
vm = json.loads((results / "verify-in-vm.json").read_text(encoding="utf-8"))
lifted = vm["runs"]["lifted_limit"]["simulations"]
default = vm["runs"]["default_limit"]["simulations"]
valid = sorted(x["unitsConsumed"] for x in lifted if x["signature"] == "valid")
assert valid and all(x["err"] is None for x in lifted if x["signature"] == "valid"), "a valid signature failed"
assert all(x["err"] is not None for x in lifted if x["signature"] != "valid"), "an altered signature passed"
units = {"min": valid[0], "median": statistics.median(valid), "max": valid[-1]}
assert units == {k: vm["valid_signature_unitsConsumed"][k] for k in units}, "the record's summary differs from its simulations"
assert vm["fits_in_1400000"] == (units["max"] <= MAX_TX_COMPUTE_UNITS)
stops_at_the_limit = all(x["err"] is not None and x["unitsConsumed"] == MAX_TX_COMPUTE_UNITS for x in default)
control = vm["fips204_in_the_virtual_machine"]
assert control["frame_of_the_verification_bytes"] > control["frame_limit_bytes"]
assert all(r["err_of_every_simulation"] is not None for r in control["runs"].values())
differential = vm["tests"]["differential_against_fips204"]
assert differential["passed"] and differential["comparisons_with_different_answers"] == 0
edges = vm["tests"]["edge_cases"]
assert edges["inputs_with_different_answers"] == 0 and vm["tests"]["tests_failed"] == 0
cost_vm = enroll_cost + activate_cost + 2 * units["median"]
mean_vm, binds_vm = room(cost_vm)
in_vm = {"compute_units_per_verification": {k: units[k] for k in ("min", "median", "max")},
         "fits_one_transaction": vm["fits_in_1400000"],
         "every_simulation_stops_at_the_limit_of_a_transaction": stops_at_the_limit,
         "simulations": {"valid_signatures": len(valid), "altered_signatures": len(lifted) - len(valid)},
         "max_compute_units_per_transaction": MAX_TX_COMPUTE_UNITS,
         "times_the_maximum_of_a_transaction": units["median"] / MAX_TX_COMPUTE_UNITS,
         "program_sha256": vm["program"]["so_sha256"],
         "differential_test": {"pairs_of_key_and_message": differential["pairs_of_key_and_message"],
                               "comparisons": differential["comparisons"], "different_answers": 0},
         "edge_case_test": {"inputs": edges["inputs"], "different_answers": 0},
         "tests": {"passed": vm["tests"]["tests_passed"], "failed": vm["tests"]["tests_failed"]},
         "fips204_control": {"frame_of_the_verification_bytes": control["frame_of_the_verification_bytes"],
                             "frame_limit_bytes": control["frame_limit_bytes"],
                             "functions_over_the_frame_limit": control["functions_over_the_frame_limit"],
                             "simulations_that_failed": sum(r["simulations"] for r in control["runs"].values()),
                             "simulations": sum(r["simulations"] for r in control["runs"].values())},
         "if_both_verifications_ran_in_a_program": {
             "cost_units_per_account": cost_vm,
             "accounts_in_an_empty_block": min(ENTRY_BYTES // bytes_per_account, BLOCK_COST // cost_vm),
             "accounts_per_slot": mean_vm, "accounts_per_day": mean_vm * slots_per_day,
             "blocks_where_cost_binds": binds_vm["cost"]}}

entry_bytes_of = [int(r["tx_bytes"]) + ENTRY_OVERHEAD * int(r["txs"]) for r in blocks]
by_bytes_slot = int(max(blocks, key=lambda r: int(r["tx_bytes"]))["slot"])
by_cost_slot = int(max(blocks, key=lambda r: int(r["cost_units"]))["slot"])
out = {
    "mainnet_limits": params,
    "measured_transactions": {
        "enroll": {"bytes": enroll_bytes, "compute_units": tx["enroll"]["compute_units"]["min"], "cost_units": enroll_cost,
                   "landed": tx["enroll"]["landed_ok"]},
        "activate": {"bytes": activate_bytes, "compute_units": tx["activate"]["compute_units"]["min"], "cost_units": activate_cost,
                     "landed": tx["activate"]["landed_ok"]},
        "fee_lamports_per_transaction": fee_one_signature,
    },
    "verification": {"ml_dsa_44_verify_microseconds": verify_ns / 1000, "ed25519_verify_microseconds": ed_ns / 1000,
                     "statistic": "median over the five rounds of each round's median",
                     "ml_dsa_44_time_over_ed25519_time": verify_ns / ed_ns,
                     "ed25519_precompile_signature_cost_units": ED25519_PRECOMPILE_COST,
                     "charge_cost_units_per_ml_dsa_44_verification": verify_charge,
                     "charge_rule": "the cost units of a signature that the Ed25519 precompile verifies, times the ratio of the two times",
                     "charge_at_30_cost_units_per_microsecond_of_the_machine_time": verify_charge_by_machine_time,
                     "library": bench["library"]},
    "per_account": {"transactions": 2, "entry_bytes": bytes_per_account, "cost_units": cost_per_account,
                    "fee_lamports": fee_per_account,
                    "record_bytes": params["record_bytes_activated"],
                    "rent_exempt_deposit_lamports_mainnet": deposit_per_account},
    "full_block": {"enrollments": cap["enroll"], "entry_bytes": cap["enroll"] * (enroll_bytes + ENTRY_OVERHEAD),
                   "cost_units_measured": cap["enroll"] * enroll_cost,
                   "cost_units_with_the_verification_charge": cap["enroll"] * (enroll_cost + verify_charge),
                   "accounts_in_an_empty_block": min(ENTRY_BYTES // bytes_per_account, BLOCK_COST // cost_per_account)},
    "local_run": {"node": run["node_version"], "largest_block": main["largest_block"],
                  "blocks_at_the_largest_count": main["blocks_at_the_largest_count"],
                  "limit_predicted_from_the_entry_byte_budget": cap},
    "local_runs": local_runs,
    "verification_inside_the_virtual_machine": in_vm,
    "mainnet_sample": {
        "first_slot": int(rows[0]["slot"]), "last_slot": int(rows[-1]["slot"]), "slots": n_slots, "blocks": n_blocks,
        "skipped_slots": n_slots - n_blocks, "first_block_time": times[0], "last_block_time": times[-1], "seconds": seconds,
        "milliseconds_per_slot": ms_per_slot, "slots_per_day": slots_per_day,
        "transactions": sum(col("txs")),
        "per_block": {"transactions": spread(col("txs")), "tx_bytes": spread(col("tx_bytes")), "cost_units": spread(col("cost_units")),
                      "compute_units": spread(col("compute_units"))},
        "slot_of_the_most_tx_bytes": by_bytes_slot, "slot_of_the_most_cost_units": by_cost_slot,
        "entry_bytes_per_block_mean": used_entry_bytes / n_blocks,
        "largest_transaction_bytes": max(col("max_tx_bytes")),
        "transactions_per_second": window_rate,
        "cluster_transactions_per_second": cluster_rate,
        "share_of_entry_byte_budget_used_at_most": used_entry_bytes / (n_blocks * ENTRY_BYTES),
        "share_of_block_cost_limit_used": sum(col("cost_units")) / (n_blocks * BLOCK_COST),
        "largest_share_of_entry_byte_budget_in_a_block_at_most": max(entry_bytes_of) / ENTRY_BYTES,
        "largest_share_of_block_cost_limit_in_a_block": max(col("cost_units")) / BLOCK_COST,
        "slot_intervals_between_first_and_last_block": int(blocks[-1]["slot"]) - int(blocks[0]["slot"]),
        "blocks_where_bytes_bind": bound_by["bytes"], "blocks_where_cost_binds": bound_by["cost"],
    },
    "rates": rates,
    "second_rate_capped_at_transaction_bytes_alone": second_tx_bytes_only,
    "rates_by_charge_per_verification": charge_sensitivity,
    "order_of_inclusion": ordering,
    "days": days,
    "population_sources": populations["sources"],
}
(results / "SOLANA.json").write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8", newline="\n")


def duration(d):
    if d < 1 / 1440:
        return f"{d * 86400:.0f} s"
    if d < 1 / 24:
        return f"{d * 1440:.1f} min"
    if d < 1:
        return f"{d * 24:.1f} h"
    return f"{d:.1f} days"


def pct(x):
    return f"{100 * x:.1f} %"


s = out["mainnet_sample"]
c = s["cluster_transactions_per_second"]
o = ordering
tp = o["tips"]
vmx = in_vm["if_both_verifications_ran_in_a_program"]
lines = [
    "# Solana enrollment: results",
    "",
    "Generated by `tools/analyze.py`; every number is in `SOLANA.json`. The README explains the terms.",
    "",
    "| Quantity | Value |",
    "|---|---|",
    f"| Enrollment transaction | {enroll_bytes:,} bytes, {tx['enroll']['compute_units']['min']:,} compute units, {enroll_cost:,} cost units |",
    f"| Activation transaction | {activate_bytes:,} bytes, {tx['activate']['compute_units']['min']:,} compute units, {activate_cost:,} cost units |",
    f"| ML-DSA-44 verification on the run's machine | {verify_ns / 1000:.2f} microseconds, {verify_ns / ed_ns:.4f} times an Ed25519 verification ({ed_ns / 1000:.2f}) |",
    f"| Charge for one ML-DSA-44 verification | {verify_charge:,} cost units: the {ED25519_PRECOMPILE_COST:,} of a signature that the Ed25519 precompile verifies, times {verify_ns / ed_ns:.4f} |",
    f"| One account (both transactions) | {bytes_per_account:,} entry bytes, {cost_per_account:,} cost units |",
    f"| Mainnet limits per block | {ENTRY_BYTES:,} entry bytes, {BLOCK_COST:,} cost units |",
    f"| A block full of enrollments | {cap['enroll']:,} enrollments, {out['full_block']['entry_bytes']:,} entry bytes, {out['full_block']['cost_units_measured']:,} cost units measured, {out['full_block']['cost_units_with_the_verification_charge']:,} with the verification charge |",
    f"| Largest block of `local-run-200ms` | {main['largest_block']['enroll']:,} enrollments ({main['blocks_at_the_largest_count']['enroll']} blocks), {main['largest_block']['activate']:,} activations ({main['blocks_at_the_largest_count']['activate']} blocks) |",
    f"| ML-DSA-44 verification inside the virtual machine | {units['median']:,} compute units (median of {len(valid)} keys; {units['min']:,} to {units['max']:,}), {in_vm['times_the_maximum_of_a_transaction']:.2f} times the {MAX_TX_COMPUTE_UNITS:,} a transaction may use |",
    f"| Mainnet sample | {n_slots:,} slots, {n_blocks:,} blocks, {s['transactions']:,} transactions; {seconds} s from the first block's time to the last, over {s['slot_intervals_between_first_and_last_block']:,} slots: {ms_per_slot:.1f} ms per slot |",
    f"| Transactions per second | {window_rate:,.0f} in the sample; {c['min']:,.0f} to {c['max']:,.0f} (median {c['median']:,.0f}) over the {c['minutes']} minutes of `data/mainnet_params.json` |",
    f"| Ordinary traffic per block (mean) | {s['per_block']['tx_bytes']['mean']:,.0f} bytes of transactions ({s['entry_bytes_per_block_mean']:,.0f} entry bytes at {ENTRY_OVERHEAD} per transaction), {s['per_block']['cost_units']['mean']:,.0f} cost units |",
    f"| Share of the limits that ordinary traffic uses, mean over the blocks | {pct(s['share_of_entry_byte_budget_used_at_most'])} of the entry bytes (with {ENTRY_OVERHEAD} bytes of overhead for every transaction), {pct(s['share_of_block_cost_limit_used'])} of the cost units |",
    f"| The same shares in the fullest blocks | {pct(s['largest_share_of_entry_byte_budget_in_a_block_at_most'])} of the entry bytes, {s['per_block']['cost_units']['max']:,} of the {BLOCK_COST:,} cost units |",
    f"| Per-block maxima of ordinary traffic | {s['per_block']['tx_bytes']['max']:,} bytes (slot {by_bytes_slot:,}); {s['per_block']['cost_units']['max']:,} cost units (slot {by_cost_slot:,}); largest transaction {s['largest_transaction_bytes']:,} bytes |",
    f"| Blocks where the byte limit binds, where the cost limit binds | {s['blocks_where_bytes_bind']:,}, {s['blocks_where_cost_binds']:,} |",
    f"| The migration's reward per cost unit at the signature fee | {o['migration_reward_per_cost_unit_lamports']:.3f} lamports with the verification charge in its cost ({o['migration_reward_per_cost_unit_lamports_without_the_charge']:.3f} without it) |",
    f"| Ordinary transactions that rank below it by fees (at least) | {pct(o['ordinary_below_the_migration_at_least']['transactions'])} of the transactions, {pct(o['ordinary_below_the_migration_at_least']['bytes'])} of their bytes, {pct(o['ordinary_below_the_migration_at_least']['cost_units'])} of their cost units |",
    f"| Fee those transactions would add to rank level with it (at least) | median {o['fee_top_up_to_rank_level_lamports_at_least']['median']:,.0f} lamports, 90th percentile {o['fee_top_up_to_rank_level_lamports_at_least']['p90']:,.0f}; {pct(o['fee_top_ups_over_all_ordinary_fees'])} of all ordinary fees in total |",
    f"| Transactions that also pay a tip | {tp['transactions_with_a_tip']:,} ({pct(tp['share_of_transactions'])}), in {tp['blocks_with_a_tip']:,} blocks; {tp['tips_lamports'] / 1e9:.2f} SOL against {reported_reward / 1e9:.2f} SOL of fee rewards |",
    f"| The same shares with tips counted as reward | {pct(tp['ordinary_below_the_migration_with_tips_counted']['transactions'])}, {pct(tp['ordinary_below_the_migration_with_tips_counted']['bytes'])}, {pct(tp['ordinary_below_the_migration_with_tips_counted']['cost_units'])} |",
    "",
    "| Rate | Accounts per slot | Accounts per day |",
    "|---|---|---|",
    f"| first: the migration takes all the space that ordinary traffic leaves | {rates['first']['accounts_per_slot']:,.0f} | {rates['first']['accounts_per_day']:,.0f} |",
    f"| second: and no more entry bytes per block than ordinary traffic uses | {rates['second']['accounts_per_slot']:,.0f} | {rates['second']['accounts_per_day']:,.0f} |",
    f"| second, capped at the ordinary transactions' bytes without the entry overhead | | {second_tx_bytes_only:,.0f} |",
    f"| first, if a program ran both verifications ({vmx['cost_units_per_account']:,} cost units per account) | {vmx['accounts_per_slot']:,.1f} | {vmx['accounts_per_day']:,.0f} |",
    "",
    "| Charge per verification | Cost units | Accounts per day at the first rate | Blocks where the cost limit binds | Accounts per day at the second rate |",
    "|---|---|---|---|---|",
]
for x in charge_sensitivity:
    lines.append(f"| {x['charge']} | {x['cost_units_per_verification']:,} | {x['accounts_per_day']:,.0f} | {x['blocks_where_cost_binds']:,} of {n_blocks:,} | {x['accounts_per_day_second_rate']:,.0f} |")
lines += ["", "| Pricing of the migration's transactions | Reward per cost unit (lamports) | Ordinary transactions that rank below it by fees (at least) |",
          "|---|---|---|",
          f"| the charge, one signature fee per transaction (as above) | {o['migration_reward_per_cost_unit_lamports']:.3f} | {pct(o['ordinary_below_the_migration_at_least']['transactions'])} of the transactions, {pct(o['ordinary_below_the_migration_at_least']['bytes'])} of their bytes, {pct(o['ordinary_below_the_migration_at_least']['cost_units'])} of their cost units |"]
for name, label in (("without_the_charge", "no charge: the transactions as they are today"),
                    ("with_the_charge_and_a_signature_fee_for_the_ml_dsa_signature", "the charge and a signature fee for the ML-DSA-44 signature")):
    x = pricings[name]
    lines.append(f"| {label} | {x['migration_reward_per_cost_unit_lamports']:.3f} | {pct(x['ordinary_below_the_migration_at_least']['transactions'])}, {pct(x['ordinary_below_the_migration_at_least']['bytes'])}, {pct(x['ordinary_below_the_migration_at_least']['cost_units'])} |")
lines += ["", "| Population | Accounts | First rate | Second rate | Fees (SOL) | Deposits (SOL) | New account data (GiB) |",
          "|---|---|---|---|---|---|---|"]
for row in days:
    lines.append(f"| {row['population']} | {row['accounts']:,} | {duration(row['first']['days'])} | {duration(row['second']['days'])} | "
                 f"{row['fees_sol']:,.1f} | {row['rent_exempt_deposits_sol']:,.0f} | {row['new_account_data_gib']:,.1f} |")
lines += ["", "| Local run | Node flags | Wallets | Largest block: enrollments (blocks), activations (blocks) | Sent per second | Checks |",
          "|---|---|---|---|---|---|"]
for name, r in local_runs.items():
    lines.append(f"| {name} | `{r['node_flags']}` | {r['wallets']:,} | {r['largest_block']['enroll']:,} ({r['blocks_at_the_largest_count']['enroll']}), "
                 f"{r['largest_block']['activate']:,} ({r['blocks_at_the_largest_count']['activate']}) | "
                 f"{r['sent_per_second']['enroll']:,.0f}, {r['sent_per_second']['activate']:,.0f} | {r['checks_passed']} of {r['checks']} |")
(results / "SOLANA.md").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
print("\n".join(lines))
