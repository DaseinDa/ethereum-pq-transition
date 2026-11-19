#!/usr/bin/env python3
"""Mutation controls for AccountInductive.tla (run inside WSL, after run_apalache.sh, with the same output folder):
    python3 mutation_check.py [OUTPUT_DIR]

Each mutation weakens one rule of the model. The inductive step (IndInit, IndInvAndProps, length 1) must then be
VIOLATED; a mutation that still passes would mean that the properties do not depend on that rule. Appends to
OUTPUT_DIR/summary.txt, writes OUTPUT_DIR/logs/MUT_*.txt and, from summary.txt, OUTPUT_DIR/summary.json.
OUTPUT_DIR defaults to apalache-out beside this file.
"""
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
APALACHE = os.path.expanduser(os.environ.get(
    "APALACHE", "~/tools/apalache-0.62.4/apalache-0.62.4/bin/apalache-mc"))
OUT = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.join(HERE, "apalache-out")
os.makedirs(os.path.join(OUT, "logs"), exist_ok=True)

with open(os.path.join(HERE, "AccountInductive.tla"), encoding="utf-8") as f:
    SRC = f.read().replace("\r", "")

# (name, exact old text, new text, the rule that is weakened)
MUTATIONS = [
    ("MUT_ROTATE_IN_WINDOW",
     '/\\ k # "none" /\\ Final(m, k, t)',
     '/\\ k # "none"',
     "rotate no longer needs a final account"),
    ("MUT_FORGED_PROOF",
     '/\\ m\' = "BYPROOF" /\\ c\' = "O" /\\ k\' = "none" /\\ n\' = n + 1',
     '/\\ m\' = "BYPROOF" /\\ (\\E x \\in {"O", "A"} : c\' = x) /\\ k\' = "none" /\\ n\' = n + 1',
     "a migration may carry a commitment the owner did not prove"),
    ("MUT_ENROLL_AFTER_T",
     '/\\ m = "LEGACY" /\\ T0 <= t /\\ t < T\n    /\\ \\E cls',
     '/\\ m = "LEGACY" /\\ T0 <= t\n    /\\ \\E cls',
     "an enrollment is valid after T"),
    ("MUT_ECDSA_AFTER_ENROLLMENT",
     '/\\ m = "LEGACY" /\\ t < T\n    /\\ UNCHANGED <<m, c, k, n, ma, enr, t>>\n    /\\ Hist("ecdsa", "E")',
     '/\\ t < T\n    /\\ UNCHANGED <<m, c, k, n, ma, enr, t>>\n    /\\ Hist("ecdsa", "E")',
     "an ECDSA transaction is valid for an account that is not LEGACY"),
    ("MUT_UNBOUND_ACTIVATION",
     '/\\ k\' = c\n    /\\ UNCHANGED <<m, c, n, ma, enr, t>>',
     '/\\ (\\E x \\in {"O", "A"} : k\' = x)\n    /\\ UNCHANGED <<m, c, n, ma, enr, t>>',
     "an activation may install a key that the commitment does not fix"),
    ("MUT_NONCE_NOT_RAISED",
     '/\\ m\' = "BYPROOF" /\\ c\' = "O" /\\ k\' = "none" /\\ n\' = n + 1\n    /\\ ma\' = n',
     '/\\ m\' = "BYPROOF" /\\ c\' = "O" /\\ k\' = "none" /\\ n\' = n\n    /\\ ma\' = n',
     "a migration does not raise the migration nonce"),
]

env = dict(os.environ)
env.setdefault("JVM_ARGS", "-Xmx1500m")
lines = []
for name, old, new, what in MUTATIONS:
    if SRC.count(old) != 1:
        lines.append(f"{name} | violated | mutation-not-applied({SRC.count(old)} matches) | NO | 0")
        continue
    work = tempfile.mkdtemp(prefix="apalache-mut-")
    with open(os.path.join(work, "AccountInductive.tla"), "w", encoding="utf-8") as f:
        f.write(SRC.replace(old, new))
    t0 = time.time()
    res = subprocess.run(
        [APALACHE, "check", "--out-dir=" + os.path.join(work, "out"), "--next=Next", "--init=IndInit",
         "--inv=IndInvAndProps", "--length=1", "AccountInductive.tla"],
        cwd=work, env=env, capture_output=True, text=True)
    log = res.stdout + res.stderr
    with open(os.path.join(OUT, "logs", name + ".txt"), "w", encoding="utf-8") as f:
        f.write(f"mutation: {what}\n\n" + log)
    if "The outcome is: NoError" in log:
        outcome = "holds"
    elif "The outcome is: Error" in log:
        outcome = "violated"
    else:
        outcome = f"tool-error(rc={res.returncode})"
    ok = "yes" if outcome == "violated" else "NO"
    lines.append(f"{name} ({what}) | violated | {outcome} | {ok} | {int(time.time() - t0)}")

with open(os.path.join(OUT, "summary.txt"), "a", encoding="utf-8", newline="\n") as f:
    f.write("\n".join(lines) + "\n")
print("\n".join(lines))

# machine-readable summary of every job in summary.txt
import hashlib
import json
import re

with open(os.path.join(OUT, "summary.txt"), encoding="utf-8") as f:
    txt = f.read().replace("\r", "")
head = dict(re.findall(r"^(module sha256|apalache|java|date \(UTC\)): (.*)$", txt, flags=re.M))
jobs = []
for line in txt.splitlines():
    parts = [p.strip() for p in line.split(" | ")]
    if len(parts) == 5 and parts[0] != "job":
        name, what = re.match(r"^(\S+)(?: \((.*)\))?$", parts[0]).groups()
        kind = "check" if parts[1] == "holds" else ("mutation" if name.startswith("MUT_") else "scenario")
        jobs.append(dict(name=name, kind=kind, what=what, tool="Apalache", expected=parts[1], outcome=parts[2],
                         as_expected=(parts[3] == "yes"), seconds=int(parts[4])))
summary = dict(
    module="AccountInductive.tla",
    module_sha256_cr_stripped=hashlib.sha256(SRC.encode()).hexdigest(),
    recorded_module_sha256=head.get("module sha256", "").split(" ")[0],
    apalache=head.get("apalache"), java=head.get("java"), date_utc=head.get("date (UTC)"),
    bound="all integers: T0 < T, W >= 1, time, migration nonce; one account; ideal proofs and signatures",
    jobs=jobs, all_as_expected=all(j["as_expected"] for j in jobs),
    counts=dict(checks=sum(j["kind"] == "check" for j in jobs),
                scenarios=sum(j["kind"] == "scenario" for j in jobs),
                mutations=sum(j["kind"] == "mutation" for j in jobs)),
    status="in the research repository since 2026-11-11 (code/formal-model-20261027/account-inductive) and rerun "
           "from there; the module is the draft of 2026-11-10, byte for byte; an external reviewer read the module "
           "and the first run's record twice and did not rerun it")
with open(os.path.join(OUT, "summary.json"), "w", encoding="utf-8", newline="\n") as f:
    json.dump(summary, f, indent=1)
print("summary.json:", summary["counts"], "all as expected:", summary["all_as_expected"])
