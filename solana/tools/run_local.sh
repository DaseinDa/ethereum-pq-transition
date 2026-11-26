#!/bin/bash
# Run the enrollment client against the local node and keep the node's records next to the results.
#
#   bash tools/run_local.sh N_WALLETS SEED NAME
#
# Needs the node of tools/start_node.sh (same WORK and RPC_PORT) and the client built with
#   cargo build --release --manifest-path harness/Cargo.toml
# Writes $WORK/run/NAME/: run.json and blocks.csv from the client, features_local.json, genesis_hash.txt,
# validator_args.txt and build_info.txt (the program's SHA-256 and the versions of the tools).
# PQSOL_SEND_THREADS sets the number of sending connections (16 if unset).
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
WORK=${WORK:-$HERE/work}
RPC_PORT=${RPC_PORT:-8899}
PQSOL=${PQSOL:-$HERE/harness/target/release/pqsol}
N=$1; SEED=$2; OUT="$WORK/run/$3"
URL=http://127.0.0.1:$RPC_PORT
mkdir -p "$OUT"
solana -u "$URL" slot >/dev/null    # ends here, with the client's error, if no node answers
# A node started with --slots-per-epoch 32 has mainnet's 200 ms parameters from slot 32; wait until slot 96.
if grep -q -- '--slots-per-epoch 32' "$WORK/run/node_args.txt"; then
  until [ "$(solana -u "$URL" epoch)" -ge 3 ]; do sleep 1; done
fi
"$PQSOL" run "$URL" "$WORK/keys/funder.json" "$(cat "$WORK/run/program_id.txt")" "$N" "$SEED" "$OUT" > "$OUT/summary.json"
solana feature status -u "$URL" --output json > "$OUT/features_local.json"
solana -u "$URL" genesis-hash > "$OUT/genesis_hash.txt"
cp "$WORK/run/node_args.txt" "$OUT/validator_args.txt"
{
  echo "program sha256: $(sha256sum "$WORK/out/pq_enroll_registry.so" | cut -d' ' -f1)"
  echo "client sha256: $(sha256sum "$PQSOL" | cut -d' ' -f1)"
  solana --version
  solana-test-validator --version
  cargo-build-sbf --version | tr '\n' ';'
  echo
  rustc --version
} > "$OUT/build_info.txt"
rm -f "$OUT/summary.json"
python3 - "$OUT/run.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
print("checks passed:", sum(1 for c in d["checks"] if c.get("pass")), "of", len(d["checks"]))
for kind in ("enroll", "activate"):
    t = d["transactions"][kind]
    print(kind, "landed", t["landed_ok"], "failed", t["failed"], "| bytes", t["bytes"]["median"], "| cost units", t["cost_units"]["median"])
PY
