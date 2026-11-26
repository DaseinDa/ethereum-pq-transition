#!/bin/bash
# Start one local Agave node for the enrollment run.
#
#   bash tools/start_node.sh [extra solana-test-validator flags]
#
# Needs solana-test-validator, solana and solana-keygen of Agave v4.4.1 on PATH, and the program built with
#   cargo-build-sbf --manifest-path program/Cargo.toml --sbf-out-dir "$WORK/out"
# WORK (default: ./work) receives the ledger, the funder's key and the node's log. RPC_PORT (default 8899) is the
# node's RPC port.
#
# The node gets the features that are inactive on mainnet turned off (data/features_mainnet.json, the output of
# `solana feature status -u mainnet-beta --output json`). The main run passes `--alpenglow --slots-per-epoch 32`:
# the slot-time feature is active from genesis and takes effect at the start of the next epoch, so with 32-slot
# epochs the node runs with mainnet's 200 ms slot parameters from slot 32. A node that an earlier call started
# from the same WORK is stopped first.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
WORK=${WORK:-$HERE/work}
RPC_PORT=${RPC_PORT:-8899}
URL=http://127.0.0.1:$RPC_PORT
mkdir -p "$WORK/keys" "$WORK/run"
[ -s "$WORK/keys/funder.json" ] || solana-keygen new --no-bip39-passphrase --silent --force -o "$WORK/keys/funder.json" >/dev/null
PROGRAM_ID=$(solana-keygen pubkey "$WORK/out/pq_enroll_registry-keypair.json")
FUNDER=$(solana-keygen pubkey "$WORK/keys/funder.json")
DEACTIVATE=$(python3 -c "
import json, sys
d = json.load(open(sys.argv[1]))
print(' '.join('--deactivate-feature ' + f['id'] for f in d['features'] if f['status'] != 'active'))" "$HERE/data/features_mainnet.json")
# stop the node of an earlier call: only a process that still runs on this WORK's ledger
if [ -s "$WORK/run/node.pid" ] && ps -ww -o args= -p "$(cat "$WORK/run/node.pid")" 2>/dev/null | grep -qF -- "--ledger $WORK/ledger"; then
  kill "$(cat "$WORK/run/node.pid")"
  sleep 2
fi
if solana -u "$URL" slot >/dev/null 2>&1; then
  echo "a node still answers on $URL: stop it before starting another" >&2
  exit 1
fi
rm -rf "$WORK/ledger"
echo "$PROGRAM_ID" > "$WORK/run/program_id.txt"
# shellcheck disable=SC2086
set -- --ledger "$WORK/ledger" --reset --quiet --mint "$FUNDER" \
  --bpf-program "$PROGRAM_ID" "$WORK/out/pq_enroll_registry.so" $DEACTIVATE \
  --rpc-port "$RPC_PORT" --bind-address 127.0.0.1 "$@"
echo "solana-test-validator $*" > "$WORK/run/node_args.txt"
nohup solana-test-validator "$@" > "$WORK/run/validator.log" 2>&1 &
echo $! > "$WORK/run/node.pid"
echo "node pid $(cat "$WORK/run/node.pid"), program $PROGRAM_ID, funder $FUNDER"
for _ in $(seq 1 60); do
  solana -u "$URL" slot >/dev/null 2>&1 && break
  kill -0 "$(cat "$WORK/run/node.pid")" 2>/dev/null || break
  sleep 1
done
if ! kill -0 "$(cat "$WORK/run/node.pid")" 2>/dev/null || ! SLOT=$(solana -u "$URL" slot 2>/dev/null); then
  echo "the node did not start: see $WORK/run/validator.log" >&2
  exit 1
fi
echo "node version $(solana -u "$URL" cluster-version), slot $SLOT"
