#!/usr/bin/env python3
"""Render recorded outcomes; missing or failed steps never appear as passing."""
import argparse
import html
import json
from pathlib import Path


def render(run):
    top = json.loads((run / "RUN.json").read_text())
    p = run / "network/result.json"
    network = json.loads(p.read_text()) if p.exists() else {}
    rows = []
    txs = run / "network/txs/txs.json"
    carriers = json.loads(txs.read_text()) if txs.exists() else {}
    extra = run / "network/txs/l1-carriers.json"
    if extra.exists():
        carriers.update(json.loads(extra.read_text())["carriers"])
    stages = [("Recovery after reorg", "migrate", network.get("recoveryReinclusion", {}))]
    stages.extend((name, name, value) for name, value in network.get("preT", {}).get("steps", {}).items())
    stages.extend((name, name, value) for name, value in network.get("l1", {}).get("steps", {}).items())
    stages.extend([( "Activation", "activate", network.get("activation", {})),
                   ("First PQ spend", "spend", network.get("spend", {}))])
    for label, name, step in stages:
        rec = step.get("receipts", {})
        a, b = rec.get("A"), rec.get("B")
        ok = bool(a and a == b and a.get("status") == "0x1")
        rows.append({"step": label, "status": "PASS" if ok else "NOT VERIFIED",
                     "block": int(a["blockNumber"], 16) if a else None,
                     "gas": int(a["gasUsed"], 16) if a else None,
                     "carrierBytes": carriers.get(name, {}).get("bytes"),
                     "accountAddress": step.get("accountAddress"), "beforeAccounts": step.get("beforeAccounts", step.get("beforeAccount")), "accounts": step.get("accounts", step.get("account")), "beforeBalances": step.get("beforeBalances"),
                     "afterBalances": step.get("afterBalances")})
    rows.sort(key=lambda x: x["block"] if x["block"] is not None else 10**20)
    summary = {"status": top["status"], "steps": rows, "restart": bool(network.get("historyAppendOnly")),
               "reorg": network.get("reorg"), "failure": top.get("failure", network.get("failure")),
               "preTEnrollment": network.get("preT", {}).get("status", "NOT VERIFIED"), "legacyAfterT": network.get("legacyAfterT", "NOT VERIFIED"),
               "scope": "Synthetic state, three public-test validators on two local nodes. Internal regression only. No production or target-security acceptance."}
    (run / "SUMMARY.json").write_text(json.dumps(summary, indent=2) + "\n")
    esc = lambda value: html.escape(str(value))
    body = "".join("<tr>" + "".join("<td>" + esc(row[k]) + "</td>" for k in ["step", "status", "block", "gas", "carrierBytes"]) + "</tr>" for row in rows)
    detail = "".join("<details><summary>" + esc(row["step"]) + " — account state and balances</summary><pre>" + esc(json.dumps(row, indent=2)) + "</pre></details>" for row in rows)
    page = '<!doctype html><html lang="en"><meta charset="utf-8"><title>PQ-Migrate local demo</title><style>body{font:16px system-ui;max-width:1050px;margin:40px auto;padding:0 20px;color:#172739}table{border-collapse:collapse;width:100%}td,th{padding:10px;border-bottom:1px solid #ccd7df;text-align:left}pre{overflow:auto;background:#f2f5f7;padding:16px}details{margin:16px 0}</style>'
    page += '<h1>PQ-Migrate local demo: ' + esc(top["status"]) + '</h1><p>' + esc(summary["scope"]) + '</p>'
    page += '<p>loop-internal self-review; not independently reviewed</p><table><tr><th>Lifecycle step</th><th>A / B</th><th>Block</th><th>Gas</th><th>Carrier bytes</th></tr>' + body + '</table>'
    page += '<h2>Restart and reorg</h2><pre>' + esc(json.dumps({k: summary[k] for k in ["restart", "reorg", "preTEnrollment", "legacyAfterT", "failure"]}, indent=2)) + '</pre>' + detail + '</html>'
    (run / "report.html").write_text(page)
    print(json.dumps({"status": top["status"], "report": str(run / "report.html")}))


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run", type=Path, required=True)
    render(ap.parse_args().run)
