"""Download consecutive finalized Solana mainnet blocks (raw transactions + metadata) from a public RPC.

python -X utf8 -I sample_blocks.py OUT_DIR FIRST_SLOT COUNT [RPC_URL]

Each block is stored as OUT_DIR/raw/<slot>.json.gz (the JSON-RPC result, written out compactly, gzip).
OUT_DIR/index.jsonl gets one line per slot: status (ok / skipped / error), sizes and the SHA-256 of the JSON as
stored. The RPC answers a slot without a block with an error that also covers a block it no longer has, so
"skipped" is confirmed later: parse_blocks.py checks that every block's parent is the block before it and that
the window ends with a block. Existing slots are not fetched
again, so the script can be restarted. One request at a time, at most about one per second; a failed request is
repeated with a growing pause. Run one copy at a time: two at once were slowed down by the public RPC.
"""
import gzip
import hashlib
import http.client
import json
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

out = Path(sys.argv[1])
first = int(sys.argv[2])
count = int(sys.argv[3])
rpc = sys.argv[4] if len(sys.argv) > 4 else "https://api.mainnet-beta.solana.com"
raw_dir = out / "raw"
raw_dir.mkdir(parents=True, exist_ok=True)
index_path = out / "index.jsonl"
done = set()
if index_path.exists():
    for line in index_path.read_text(encoding="utf-8").splitlines():
        rec = json.loads(line)
        if rec["status"] in ("ok", "skipped"):
            done.add(rec["slot"])

OPTS = {"encoding": "base64", "transactionDetails": "full", "rewards": True,
        "maxSupportedTransactionVersion": 1, "commitment": "finalized"}
SKIP_CODES = {-32007, -32009}  # slot skipped, or missing in long-term storage


def fetch(slot):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "getBlock", "params": [slot, OPTS]}).encode()
    req = urllib.request.Request(rpc, data=body, headers={
        "Content-Type": "application/json", "Accept-Encoding": "gzip", "User-Agent": "block-sampler/1.0"})
    with urllib.request.urlopen(req, timeout=120) as r:
        data = r.read()
        wire = len(data)
        if r.headers.get("Content-Encoding") == "gzip":
            data = gzip.decompress(data)
    return data, wire


t_start = time.time()
n_ok = n_skip = 0
with index_path.open("a", encoding="utf-8", newline="\n") as index:
    for slot in range(first, first + count):
        if slot in done:
            continue
        delay = 2.0
        for attempt in range(12):
            t0 = time.time()
            try:
                data, wire = fetch(slot)
                doc = json.loads(data)
                if "error" in doc:
                    code = doc["error"].get("code")
                    if code in SKIP_CODES:
                        rec = {"slot": slot, "status": "skipped", "code": code}
                        n_skip += 1
                        break
                    raise RuntimeError(f"rpc error {doc['error']}")
                result = doc["result"]
                if result is None:
                    raise RuntimeError("the RPC returned no block")
                payload = json.dumps(result, separators=(",", ":")).encode()
                (raw_dir / f"{slot}.json.gz").write_bytes(gzip.compress(payload, 6))
                rec = {"slot": slot, "status": "ok", "blockTime": result.get("blockTime"),
                       "blockHeight": result.get("blockHeight"), "parentSlot": result.get("parentSlot"),
                       "txs": len(result["transactions"]), "jsonBytes": len(payload), "wireBytes": wire,
                       "sha256": hashlib.sha256(payload).hexdigest()}
                n_ok += 1
                break
            except (urllib.error.URLError, http.client.HTTPException, RuntimeError, OSError, EOFError,
                    json.JSONDecodeError) as exc:
                rec = {"slot": slot, "status": "error", "error": str(exc)[:200]}
                time.sleep(delay)
                delay = min(delay * 2, 60.0)
        index.write(json.dumps(rec) + "\n")
        index.flush()
        if (n_ok + n_skip) % 50 == 0:
            print(f"{time.strftime('%H:%M:%S')} slot {slot} ok {n_ok} skipped {n_skip} "
                  f"elapsed {time.time() - t_start:.0f} s", flush=True)
        spent = time.time() - t0
        if spent < 1.0:
            time.sleep(1.0 - spent)
print(f"done: ok {n_ok} skipped {n_skip} in {time.time() - t_start:.0f} s", flush=True)
