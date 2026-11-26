"""Save the tip accounts that Jito's block engine names.

python -X utf8 -I tip_accounts.py OUT_FILE [URL]

A transaction can pay a tip outside its fee, by a transfer to one of Jito's tip accounts: a bid in the auction of
Jito's block engine. parse_blocks.py counts such transfers to the eight accounts that the method getTipAccounts
of the block engine returns.
"""
import json
import sys
import time
import urllib.request

out_file = sys.argv[1]
url = sys.argv[2] if len(sys.argv) > 2 else "https://mainnet.block-engine.jito.wtf/api/v1/bundles"

body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "getTipAccounts", "params": []}).encode()
req = urllib.request.Request(url, data=body, headers={"Content-Type": "application/json", "User-Agent": "tip-accounts-read/1.0"})
with urllib.request.urlopen(req, timeout=60) as r:
    doc = json.load(r)
out = {"source": url, "method": "getTipAccounts", "read_at_unix": int(time.time()), "result": sorted(doc["result"])}
with open(out_file, "w", encoding="utf-8", newline="\n") as f:
    f.write(json.dumps(out, indent=2) + "\n")
print(len(out["result"]), "tip accounts")
