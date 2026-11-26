"""Reduce the sampled mainnet blocks to one row per slot and one row per transaction.

python -X utf8 -I parse_blocks.py SAMPLE_DIR OUT_DIR

SAMPLE_DIR holds index.jsonl and raw/<slot>.json.gz as written by sample_blocks.py. OUT_DIR must hold
jito_tip_accounts.json, the answer of the method getTipAccounts of Jito's block engine. Writes
  OUT_DIR/mainnet_blocks.csv          one row per slot of the window, skipped slots included
  OUT_DIR/mainnet_txs.csv.gz          one row per transaction: slot, version, signatures, bytes, fee, cost units, tip
  OUT_DIR/mainnet_block_index.jsonl   the index, one line per slot

Every raw block is checked against the SHA-256 that the index recorded. Every block must name the block before it
in the window as its parent, the first block a slot before the window, and the last slot of the window must have
a block: together that shows that the window has no gap and that a slot recorded as skipped really has no block.

The tip of a transaction is what it adds to the balance of one of Jito's tip accounts: a bid in the auction of
Jito's block engine that is not part of the transaction's fee.
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


tip_names = set(json.loads((out / "jito_tip_accounts.json").read_text(encoding="utf-8"))["result"])
tip_keys = {b58decode(name) for name in tip_names}
assert len(tip_names) == 8 and all(len(k) == 32 for k in tip_keys), "eight tip accounts expected"

index = {}
for line in (sample / "index.jsonl").read_text(encoding="utf-8").splitlines():
    rec = json.loads(line)
    if rec["status"] in ("ok", "skipped") or rec["slot"] not in index:
        index[rec["slot"]] = rec
slots = sorted(index)
assert slots == list(range(slots[0], slots[-1] + 1)), "the window has gaps"
assert all(index[s]["status"] in ("ok", "skipped") for s in slots), "a slot was not fetched"
assert index[slots[-1]]["status"] == "ok", "the last slot of the window has no block"


def static_keys(raw):
    """(number of signatures, version, the account keys written in the transaction itself)."""
    if raw[0] == 0x81:  # v1: prefix, 3 header bytes, mask, blockhash, instruction count, address count, addresses
        count, start, signatures, version = raw[41], 42, raw[1], "1"
    else:  # legacy and v0: signatures first, then the message
        signatures = raw[0]
        assert signatures < 0x80, signatures
        at = 1 + 64 * signatures
        version = "legacy"
        if raw[at] & 0x80:
            version = "0"
            at += 1
        at += 3
        count = raw[at] & 0x7F
        if raw[at] & 0x80:  # a count of 128 or more takes two bytes
            count |= raw[at + 1] << 7
            at += 1
        start = at + 1
    return signatures, version, [raw[start + 32 * i:start + 32 * i + 32] for i in range(count)]


rows = []
versions = {"legacy": 0, "0": 0, "1": 0}
previous_block = None
tx_text = io.StringIO()
tx_rows = csv.writer(tx_text, lineterminator="\n")
tx_rows.writerow(["slot", "version", "signatures", "bytes", "fee_lamports", "cost_units", "tip_lamports"])
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
    for t in block["transactions"]:
        raw = base64.b64decode(t["transaction"][0])
        meta = t["meta"]
        k, version, keys = static_keys(raw)
        versions[version] += 1
        assert meta.get("costUnits") and meta.get("computeUnitsConsumed") is not None, slot
        loaded = meta.get("loadedAddresses") or {"writable": [], "readonly": []}
        pre, post = meta["preBalances"], meta["postBalances"]
        assert len(pre) == len(post) == len(keys) + len(loaded["writable"]) + len(loaded["readonly"]), slot
        tip = sum(max(0, post[i] - pre[i]) for i, key in enumerate(keys) if key in tip_keys)
        tip += sum(max(0, post[len(keys) + i] - pre[len(keys) + i]) for i, name in enumerate(loaded["writable"]) if name in tip_names)
        tx_rows.writerow([slot, version, k, len(raw), meta["fee"], meta["costUnits"], tip])
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
