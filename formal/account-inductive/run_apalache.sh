#!/usr/bin/env bash
# Apalache checks of AccountInductive.tla (run inside WSL):
#   bash run_apalache.sh [OUTPUT_DIR]
# Writes logs/<job>.txt and summary.txt. Small heap on purpose: other jobs share the laptop.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
APALACHE="${APALACHE:-$HOME/tools/apalache-0.62.4/apalache-0.62.4/bin/apalache-mc}"
export JVM_ARGS="${JVM_ARGS:--Xmx1500m}"
OUT="${1:-$HERE/apalache-out}"
mkdir -p "$OUT/logs"
WORK="$(mktemp -d)"
tr -d '\r' < "$HERE/AccountInductive.tla" > "$WORK/AccountInductive.tla"
cd "$WORK" || exit 2
SUM="$OUT/summary.txt"
{
  echo "module sha256: $(sha256sum AccountInductive.tla | cut -d' ' -f1) (CR stripped)"
  echo "apalache: $("$APALACHE" version 2>/dev/null | tail -1)"
  echo "java: $(java -version 2>&1 | head -1)"
  echo "date (UTC): $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo
  echo "job | expected | outcome | as expected | seconds"
} > "$SUM"

run() {  # name expected(holds|violated) apalache-args...
  local name="$1" expect="$2"; shift 2
  local log="$OUT/logs/$name.txt" t0 t1 rc outcome ok
  t0=$(date +%s)
  "$APALACHE" check --out-dir="$WORK/out-$name" --next=Next "$@" AccountInductive.tla > "$log" 2>&1
  rc=$?
  t1=$(date +%s)
  if grep -q "The outcome is: NoError" "$log"; then outcome="holds"
  elif grep -q "The outcome is: Error" "$log"; then outcome="violated"
  else outcome="tool-error(rc=$rc)"; fi
  if [ "$outcome" = "$expect" ]; then ok="yes"; else ok="NO"; fi
  echo "$name | $expect | $outcome | $ok | $((t1 - t0))" >> "$SUM"
}

run INIT              holds    --init=Init    --inv=IndInv          --length=0
run STEP              holds    --init=IndInit --inv=IndInvAndProps  --length=1
run CTRL_OVERRIDE     violated --init=IndInit --inv=NoOverride      --length=1
run CTRL_ADV_ENROLL   violated --init=IndInit --inv=NoAdvEnroll     --length=1
run CTRL_ADV_ROTATE   violated --init=IndInit --inv=NoAdvRotate     --length=1
run CTRL_FROZEN       violated --init=IndInit --inv=NoFrozenRecovery --length=1
run CTRL_PRE_T        violated --init=IndInit --inv=NoPreTMigration --length=1

cat "$SUM"
rm -rf "$WORK"
