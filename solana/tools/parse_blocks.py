"""Reduce the sampled mainnet blocks to one row per slot and one row per transaction.

python -X utf8 -I parse_blocks.py SAMPLE_DIR OUT_DIR

SAMPLE_DIR holds index.jsonl and raw/<slot>.json.gz as written by sample_blocks.py. OUT_DIR must hold
jito_tip_accounts.json, the answer of the method getTipAccounts of Jito's block engine. Writes
  OUT_DIR/mainnet_blocks.csv          one row per slot of the window, skipped slots included
  OUT_DIR/mainnet_txs.csv.gz          one row per transaction (columns below)
  OUT_DIR/mainnet_block_index.jsonl   the index, one line per slot

Every raw block is checked against the SHA-256 that the index recorded. Every block must name the block before it
in the window as its parent, the first block a slot before the window, and the last slot of the window must have
a block: together that shows that the window has no gap and that a slot recorded as skipped really has no block.

Columns of mainnet_txs.csv.gz
  slot, version, signatures, bytes   the transaction as it is on the wire
  fee_lamports, cost_units           the fee it paid and the cost units the block was charged for it (from the node)
  tip_lamports                       what it adds to the balance of one of Jito's tip accounts: a bid in the auction
                                     of Jito's block engine that is not part of the transaction's fee
  failed                             1 if it ended with an error (it is in the block and paid its fee), 0 if not
  precompile_signatures              signatures that it has the Ed25519, secp256k1 or secp256r1 precompile verify
  compute_units                      the compute units it used (from the node)
  compute_unit_limit                 the compute-unit limit it runs under
  loaded_accounts_data_size_limit    the limit on the account data it may load, in bytes
  states_compute_unit_limit,
  states_loaded_data_limit           1 if the transaction itself states that limit, 0 if it does not (a legacy or v0
                                     transaction then runs under the default, a v1 transaction under a limit of zero)
  compute_unit_price                 the price a legacy or v0 transaction states for a compute unit of its limit, in
                                     millionths of a lamport; empty if it states none, and for a v1 transaction
  cost_units_at_limits               its cost with the two limits in place of what it used: the cost that a leader
                                     running Agave ranks it by before it has run

The limits and the cost at the limits follow Agave v4.4.1 (cost-model/src/cost_model.rs and block_cost_limits.rs,
compute-budget-instruction/src/compute_budget_instruction_details.rs, runtime-transaction/src/transaction_meta.rs,
builtins-default-costs/src/lib.rs, and program-runtime/src/execution_budget.rs for the default values). The layout
of a v1 transaction is that of the crate agave-transaction-view 7.0.0, which Agave v4.4.1 depends on. A legacy or
v0 transaction states its limits in instructions of the compute-budget program. Without an instruction that sets
the compute-unit limit it runs under 200,000 compute units for every instruction, or 3,000 for an instruction of a
program on Agave's built-in list (the system and compute-budget programs, the four program loaders and the Ed25519
and secp256k1 precompiles), up to 1,400,000. Without one that sets the loaded-data limit it may load 64 MiB of
account data. Its priority fee is the price it states for a compute unit times its compute-unit limit, rounded up
to a lamport. A v1 transaction states its limits and its priority fee, in lamports, in fields of its own, without
instructions, and a limit it does not state is zero. The cost is 720 units for every transaction signature,
2,400, 6,690 or 4,800 for every signature of the Ed25519, secp256k1 or secp256r1 precompile, 300 for every account
it asks to write, one for every four bytes of instruction data, the compute units, and 8 for every 32 KiB of
loaded account data, rounded up.

Three conditions tie what is read here to what the node recorded, for every transaction: the fee is 5,000 lamports
for every signature plus the priority fee read here; the compute units used are within the compute-unit limit; and
the cost units charged, less the parts that do not depend on execution and less the compute units used, are 8 for
each of a whole number of 32 KiB pages that fits under the loaded-data limit.
"""
import base64
import csv
import gzip
import hashlib
import io
import json
import sys
from pathlib import Path

sample = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)

ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58decode(text):
    n = 0
    for ch in text:
        n = n * 58 + ALPHABET.index(ch)
    body = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return b"\x00" * (len(text) - len(text.lstrip("1"))) + body


def key(text):
    k = b58decode(text)
    assert len(k) == 32, text
    return k


tip_names = set(json.loads((out / "jito_tip_accounts.json").read_text(encoding="utf-8"))["result"])
tip_keys = {b58decode(name) for name in tip_names}
assert len(tip_names) == 8 and all(len(k) == 32 for k in tip_keys), "eight tip accounts expected"

# ---- Agave v4.4.1: the constants of its cost model and of its default limits
SIGNATURE_COST = 720                    # cost-model/src/block_cost_limits.rs
ED25519_COST, SECP256K1_COST, SECP256R1_COST = 2400, 6690, 4800
WRITE_LOCK_COST = 300
INSTRUCTION_DATA_BYTES_PER_COST_UNIT = 4
PAGE, PAGE_COST = 32 * 1024, 8          # cost-model/src/cost_model.rs, program-runtime/src/execution_budget.rs
MAX_COMPUTE_UNIT_LIMIT = 1_400_000
DEFAULT_INSTRUCTION_COMPUTE_UNIT_LIMIT = 200_000
BUILTIN_INSTRUCTION_COMPUTE_UNIT_LIMIT = 3_000
MAX_LOADED_ACCOUNTS_DATA_SIZE = 64 * 1024 * 1024
LAMPORTS_PER_SIGNATURE = 5000
COMPUTE_BUDGET = key("ComputeBudget111111111111111111111111111111")
ED25519 = key("Ed25519SigVerify111111111111111111111111111")
SECP256K1 = key("KeccakSecp256k11111111111111111111111111111")
SECP256R1 = key("Secp256r1SigVerify1111111111111111111111111")
# builtins-default-costs/src/lib.rs. The vote program left this list with the feature
# AnAP9zPV4KL7czAPQbFhpDKV2tx7g4UGNbK9wvXwjaRo, active on mainnet since slot 431,568,000 (mainnet_params.json).
BUILTINS = {key(name) for name in (
    "11111111111111111111111111111111", "ComputeBudget111111111111111111111111111111",
    "BPFLoaderUpgradeab1e11111111111111111111111", "BPFLoader1111111111111111111111111111111111",
    "BPFLoader2111111111111111111111111111111111", "LoaderV411111111111111111111111111111111111",
    "KeccakSecp256k11111111111111111111111111111", "Ed25519SigVerify111111111111111111111111111")}


def compact_u16(raw, at):
    """A length as legacy and v0 transactions write it: seven bits a byte, lowest first."""
    value = shift = 0
    while True:
        byte = raw[at]
        at += 1
        value |= (byte & 0x7F) << shift
        if not byte & 0x80:
            return value, at
        shift += 7


def read(raw):
    """The parts of a transaction that its fee, its limits and its cost depend on."""
    t = {"priority_fee": None, "cu_limit": None, "data_limit": None, "cu_price": None, "writable_lookups": 0}
    instructions = []  # (index of the program among the account keys, instruction data)
    if raw[0] & 0x80:  # v1: version, header, mask of the stated settings, blockhash, counts, keys, settings, instructions
        assert raw[0] == 0x81, raw[0]
        t["version"] = "1"
        t["signatures"], readonly_signed, readonly_unsigned = raw[1], raw[2], raw[3]
        mask = int.from_bytes(raw[4:8], "little")
        assert mask < 32 and (mask & 1) == (mask >> 1 & 1), mask
        n_instructions, n_keys = raw[40], raw[41]
        at = 42
        keys = [raw[at + 32 * i:at + 32 * i + 32] for i in range(n_keys)]
        at += 32 * n_keys
        words = [int.from_bytes(raw[at + 4 * i:at + 4 * i + 4], "little") for i in range(bin(mask).count("1"))]
        at += 4 * len(words)

        def stated(bit):
            return words[bin(mask & ((1 << bit) - 1)).count("1")] if mask >> bit & 1 else None

        if mask & 1:
            t["priority_fee"] = words[0] | words[1] << 32
        t["cu_limit"], t["data_limit"] = stated(2), stated(3)
        heads = [(raw[at + 4 * i], raw[at + 4 * i + 1], int.from_bytes(raw[at + 4 * i + 2:at + 4 * i + 4], "little"))
                 for i in range(n_instructions)]
        at += 4 * n_instructions
        for program, n_accounts, n_data in heads:
            at += n_accounts
            instructions.append((program, raw[at:at + n_data]))
            at += n_data
        at += 64 * t["signatures"]
    else:  # legacy and v0: signatures first, then the message
        t["signatures"] = raw[0]
        at = 1 + 64 * raw[0]
        t["version"] = "legacy"
        if raw[at] & 0x80:
            assert raw[at] == 0x80, raw[at]
            t["version"] = "0"
            at += 1
        assert raw[at] == t["signatures"], "as many signatures as the header requires"
        readonly_signed, readonly_unsigned = raw[at + 1], raw[at + 2]
        n_keys, at = compact_u16(raw, at + 3)
        keys = [raw[at + 32 * i:at + 32 * i + 32] for i in range(n_keys)]
        at += 32 * n_keys + 32  # the keys and the blockhash
        n_instructions, at = compact_u16(raw, at)
        for _ in range(n_instructions):
            program = raw[at]
            n_accounts, at = compact_u16(raw, at + 1)
            n_data, at = compact_u16(raw, at + n_accounts)
            instructions.append((program, raw[at:at + n_data]))
            at += n_data
        if t["version"] == "0":
            n_tables, at = compact_u16(raw, at)
            for _ in range(n_tables):
                n_writable, at = compact_u16(raw, at + 32)
                t["writable_lookups"] += n_writable
                n_readonly, at = compact_u16(raw, at + n_writable)
                at += n_readonly
        # the settings of a legacy or v0 transaction are instructions of the compute-budget program
        for program, data in instructions:
            if keys[program] != COMPUTE_BUDGET:
                continue
            kind = data[0]
            if kind == 1:  # heap size
                assert len(data) >= 5
            elif kind == 2:
                assert t["cu_limit"] is None and len(data) >= 5
                t["cu_limit"] = int.from_bytes(data[1:5], "little")
            elif kind == 3:
                assert t["cu_price"] is None and len(data) >= 9
                t["cu_price"] = int.from_bytes(data[1:9], "little")
            elif kind == 4:
                assert t["data_limit"] is None and len(data) >= 5
                t["data_limit"] = int.from_bytes(data[1:5], "little")
                assert t["data_limit"] > 0
            else:
                raise AssertionError(f"compute-budget instruction {kind}")
    assert at == len(raw), (at, len(raw))
    assert len(keys) == n_keys and all(len(k) == 32 for k in keys)
    t["keys"] = keys
    t["write_locks"] = max(0, n_keys - readonly_signed - readonly_unsigned) + t["writable_lookups"]
    t["data_bytes"] = min(0xFFFF, sum(len(data) for _, data in instructions))
    t["ed25519"] = t["secp256k1"] = t["secp256r1"] = 0
    for program, data in instructions:
        for name, precompile in (("ed25519", ED25519), ("secp256k1", SECP256K1), ("secp256r1", SECP256R1)):
            if keys[program] == precompile and data:
                t[name] += data[0]
    t["states_cu_limit"], t["states_data_limit"] = int(t["cu_limit"] is not None), int(t["data_limit"] is not None)
    if t["version"] == "1":  # a limit that a v1 transaction does not state is zero; its priority fee is in lamports
        t["cu_limit"], t["data_limit"], t["priority_fee"] = t["cu_limit"] or 0, t["data_limit"] or 0, t["priority_fee"] or 0
    else:
        if t["cu_limit"] is None:
            builtin = sum(1 for program, _ in instructions if keys[program] in BUILTINS)
            t["cu_limit"] = (builtin * BUILTIN_INSTRUCTION_COMPUTE_UNIT_LIMIT
                             + (len(instructions) - builtin) * DEFAULT_INSTRUCTION_COMPUTE_UNIT_LIMIT)
        if t["data_limit"] is None:
            t["data_limit"] = MAX_LOADED_ACCOUNTS_DATA_SIZE
    t["cu_limit"] = min(t["cu_limit"], MAX_COMPUTE_UNIT_LIMIT)
    t["data_limit"] = min(t["data_limit"], MAX_LOADED_ACCOUNTS_DATA_SIZE)
    if t["version"] != "1":  # a price in millionths of a lamport for every compute unit of the limit, rounded up
        t["priority_fee"] = -(-(t["cu_price"] or 0) * t["cu_limit"] // 1_000_000)
    t["precompile_signatures"] = t["ed25519"] + t["secp256k1"] + t["secp256r1"]
    t["fixed_cost"] = (SIGNATURE_COST * t["signatures"] + ED25519_COST * t["ed25519"] + SECP256K1_COST * t["secp256k1"]
                       + SECP256R1_COST * t["secp256r1"] + WRITE_LOCK_COST * t["write_locks"]
                       + t["data_bytes"] // INSTRUCTION_DATA_BYTES_PER_COST_UNIT)
    t["cost_at_limits"] = t["fixed_cost"] + t["cu_limit"] + -(-t["data_limit"] // PAGE) * PAGE_COST
    return t


index = {}
for line in (sample / "index.jsonl").read_text(encoding="utf-8").splitlines():
    rec = json.loads(line)
    if rec["status"] in ("ok", "skipped") or rec["slot"] not in index:
        index[rec["slot"]] = rec
slots = sorted(index)
assert slots == list(range(slots[0], slots[-1] + 1)), "the window has gaps"
assert all(index[s]["status"] in ("ok", "skipped") for s in slots), "a slot was not fetched"
assert index[slots[-1]]["status"] == "ok", "the last slot of the window has no block"

rows = []
versions = {"legacy": 0, "0": 0, "1": 0}
previous_block = None
tx_text = io.StringIO()
tx_rows = csv.writer(tx_text, lineterminator="\n")
tx_rows.writerow(["slot", "version", "signatures", "bytes", "fee_lamports", "cost_units", "tip_lamports", "failed",
                  "precompile_signatures", "compute_units", "compute_unit_limit", "loaded_accounts_data_size_limit",
                  "states_compute_unit_limit", "states_loaded_data_limit", "compute_unit_price", "cost_units_at_limits"])
for slot in slots:
    rec = index[slot]
    if rec["status"] != "ok":
        rows.append([slot, "skipped", "", "", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
        continue
    payload = gzip.decompress((sample / "raw" / f"{slot}.json.gz").read_bytes())
    assert hashlib.sha256(payload).hexdigest() == rec["sha256"], slot
    block = json.loads(payload)
    assert block.get("blockTime") is not None, slot
    if previous_block is None:
        assert block["parentSlot"] < slots[0], (slot, block["parentSlot"])
    else:
        assert block["parentSlot"] == previous_block, (slot, block["parentSlot"], previous_block)
    previous_block = slot
    n = failed = sigs = size = fees = cu = cost = largest = tips = 0
    for number, t in enumerate(block["transactions"]):
        raw = base64.b64decode(t["transaction"][0])
        meta = t["meta"]
        tx = read(raw)
        k, version, keys = tx["signatures"], tx["version"], tx["keys"]
        where = (slot, number)
        assert version == str(t["version"]), where
        versions[version] += 1
        assert meta.get("costUnits") and meta.get("computeUnitsConsumed") is not None, where
        loaded = meta.get("loadedAddresses") or {"writable": [], "readonly": []}
        pre, post = meta["preBalances"], meta["postBalances"]
        assert len(pre) == len(post) == len(keys) + len(loaded["writable"]) + len(loaded["readonly"]), where
        assert len(loaded["writable"]) == tx["writable_lookups"], where
        # the three conditions against what the node recorded
        assert meta["fee"] == LAMPORTS_PER_SIGNATURE * (k + tx["precompile_signatures"]) + tx["priority_fee"], where
        assert meta["computeUnitsConsumed"] <= tx["cu_limit"], where
        loaded_cost = meta["costUnits"] - tx["fixed_cost"] - meta["computeUnitsConsumed"]
        assert loaded_cost % PAGE_COST == 0 and 0 <= loaded_cost <= -(-tx["data_limit"] // PAGE) * PAGE_COST, where
        tip = sum(max(0, post[i] - pre[i]) for i, account in enumerate(keys) if account in tip_keys)
        tip += sum(max(0, post[len(keys) + i] - pre[len(keys) + i]) for i, name in enumerate(loaded["writable"]) if name in tip_names)
        tx_rows.writerow([slot, version, k, len(raw), meta["fee"], meta["costUnits"], tip, int(meta["err"] is not None),
                          tx["precompile_signatures"],
                          meta["computeUnitsConsumed"], tx["cu_limit"], tx["data_limit"], tx["states_cu_limit"],
                          tx["states_data_limit"], "" if tx["cu_price"] is None else tx["cu_price"], tx["cost_at_limits"]])
        n += 1
        failed += meta["err"] is not None
        sigs += k
        size += len(raw)
        largest = max(largest, len(raw))
        fees += meta["fee"]
        cu += meta["computeUnitsConsumed"]
        cost += meta["costUnits"]
        tips += tip
    fee_reward = sum(r["lamports"] for r in (block.get("rewards") or []) if r.get("rewardType") == "Fee")
    rows.append([slot, "ok", block.get("blockTime"), block.get("blockHeight"), n, failed, sigs, size, fees, cu, cost, fee_reward,
                 largest, tips])

with (out / "mainnet_blocks.csv").open("w", encoding="utf-8", newline="\n") as f:
    w = csv.writer(f, lineterminator="\n")
    w.writerow(["slot", "status", "block_time", "block_height", "txs", "failed_txs", "signatures", "tx_bytes", "fees_lamports",
                "compute_units", "cost_units", "leader_fee_reward_lamports", "max_tx_bytes", "tips_lamports"])
    w.writerows(rows)
with (out / "mainnet_txs.csv.gz").open("wb") as f:
    with gzip.GzipFile(filename="", fileobj=f, mode="wb", compresslevel=9, mtime=0) as z:
        z.write(tx_text.getvalue().encode())
with (out / "mainnet_block_index.jsonl").open("w", encoding="utf-8", newline="\n") as f:
    for slot in slots:
        f.write(json.dumps(index[slot], sort_keys=True) + "\n")

ok = [r for r in rows if r[1] == "ok"]
print(f"slots {len(slots)} ({slots[0]}..{slots[-1]}), blocks {len(ok)}, skipped {len(slots) - len(ok)}")
print(f"transactions {sum(r[4] for r in ok)} by version {versions}; tips {sum(r[13] for r in ok)} lamports")
