#!/usr/bin/env python3
"""Assemble an immutable local runtime without credentials or expiring proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from build_provenance import capture_source, verify_build, verify_source
from n1_dependencies import verify_wheelhouse


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--client-build", type=Path, required=True)
    ap.add_argument("--prover-build", type=Path, required=True)
    ap.add_argument("--aggregate-build", type=Path, required=True)
    ap.add_argument("--n1-dependencies", type=Path, required=True, help="verified offline N1 Python wheel bundle")
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    clients, prover, aggregate, out = a.client_build.resolve(), a.prover_build.resolve(), a.aggregate_build.resolve(), a.out.resolve()
    source_identity = capture_source(ROOT)
    n1_dependencies = a.n1_dependencies.resolve()
    n1_record = verify_wheelhouse(n1_dependencies)
    client_record = json.loads((clients / "BUILD.json").read_text())
    tools = json.loads((clients / "DEMO-TOOLS.json").read_text())
    prover_record = json.loads((prover / "BUILD.json").read_text())
    aggregate_record = json.loads((aggregate / "BUILD.json").read_text())
    client_names = ["geth", "ream", "profile-tool", "profile-tool-three", "fresh-public-keys", "export-signed", "audit-history", "pqlean-txs", "pq-n1-txs"]
    verify_build(ROOT, client_record, ["bin/geth", "bin/ream", "lib/libpq_final_native.so", "lib/libpq_migrate_tree.so"], clients, identity=source_identity)
    verify_build(ROOT, tools, client_names[2:], clients / "bin", identity=source_identity)
    verify_build(ROOT, prover_record, ["pq-migrate-leaf", "pq-migrate-tree", "pq-test-crypto", "pq-final-verify"], prover / "bin", identity=source_identity)
    verify_build(ROOT, aggregate_record, ["lib/libpq_migrate_tree.so", "bin/pq-migrate-tree", "bin/aggregate-verify"], aggregate, identity=source_identity)
    records = {"clients": client_record, "demo-tools": tools, "prover": prover_record, "aggregate": aggregate_record}
    dependency_hashes = {r.get("dependencyManifestSHA256") for r in records.values()}
    if len(dependency_hashes) != 1 or None in dependency_hashes:
        raise ValueError("builds used different or unauthenticated dependency bundles")
    for name in ("geth", "ream"):
        pin = json.loads((ROOT / "client" / name / "source.json").read_text())
        matching = [row for row in client_record["sources"] if row.get("client") == name]
        if len(matching) != 1 or matching[0].get("sourceManifestSHA256") != pin["treeManifestSHA256"]:
            raise ValueError("client build source manifest mismatch: " + name)
    if sha(clients / "lib/libpq_migrate_tree.so") != sha(aggregate / "lib/libpq_migrate_tree.so"):
        raise ValueError("client and aggregate build use different C verifiers")
    out.mkdir(parents=True, exist_ok=False)

    def put(source, relative, mode=0o644):
        target = out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        target.chmod(mode)

    for name in client_names:
        put(clients / "bin" / name, "libexec/" + name, 0o755)
    put(clients / "lib/libpq_final_native.so", "lib/libpq_final_native.so")
    put(clients / "lib/libpq_migrate_tree.so", "lib/libpq_migrate_tree.so")
    for relative in aggregate_record["binaries"]:
        put(aggregate / relative, "aggregate-runtime/" + relative, 0o755 if relative.startswith("bin/") else 0o644)
    put(aggregate / "BUILD.json", "aggregate-runtime/BUILD.json")
    for name in prover_record["binaries"]:
        put(prover / "bin" / name, "prover-runtime/bin/" + name, 0o755)
    put(prover / "BUILD.json", "prover-runtime/BUILD.json")
    for name in client_names:
        target = out / "bin" / name
        target.parent.mkdir(exist_ok=True)
        target.write_text("#!/bin/sh\nset -eu\nBASE=$(CDPATH= cd -- \"$(dirname -- \"$0\")/..\" && pwd)\nunset LD_PRELOAD LD_AUDIT\nexport LD_LIBRARY_PATH=\"$BASE/lib\"\nexec \"$BASE/libexec/" + name + "\" \"$@\"\n")
        target.chmod(0o755)
    for name in ["prove.py", "statement.py", "custody.py", "aggregate.py"]:
        put(ROOT / "prover" / name, "prover/" + name)
    for name in ["aggregate_support.py", "build_provenance.py", "dependency_integrity.py", "heavy_job.py", "n1_dependencies.py"]:
        put(ROOT / "tools" / name, "tools/" + name)
    for file in (ROOT / "demo/n1").rglob("*"):
        if file.is_file() and "__pycache__" not in file.parts:
            put(file, "tools/n1/" + file.relative_to(ROOT / "demo/n1").as_posix())
    for name in ("N1-CHECKPOINT.md", "BATCH-VERIFIER.md"):
        put(ROOT / "docs" / name, "share/docs/" + name)
    for file in n1_dependencies.rglob("*"):
        if file.is_file():
            put(file, "share/n1-wheels/" + file.relative_to(n1_dependencies).as_posix())
    for file in (ROOT / "prover/keys").iterdir():
        put(file, "prover/keys/" + file.name)
    for name in ["wallet.py", "wallet_epochs.py", "authorization_tracking.py", "reachability.py", "wire.py", "cli.py", "enrollment_watch.py"]:
        put(ROOT / "wallet" / name, "wallet/" + name)
    for file in (ROOT / "demo/runtime").glob("*.py"):
        put(file, "tools/lean/" + file.name)
    put(ROOT / "demo/install.py", "tools/install.py")
    put(ROOT / "demo/run.py", "tools/run_demo.py")
    put(ROOT / "demo/report.py", "tools/report.py")
    put(ROOT / "demo/start.py", "start.py")
    for folder in ["templates", "identity"]:
        for file in (ROOT / "demo" / folder).glob("*.json"):
            put(file, "share/" + folder + "/" + file.name)
    put(ROOT / "demo/public-sponsor.json", "share/l1/PUBLIC-sponsor.json")
    put(ROOT / "demo/profile.json", "share/profile.json")
    put(ROOT / "demo/public-input.json", "share/public-input.json")
    put(clients / "ream/Cargo.lock", "share/source-locks/ream-Cargo.lock")
    for name in ["LICENSE-MIT", "LICENSE-APACHE", "THIRD_PARTY.md"]:
        put(ROOT / name, name)
    put(clients / "geth/COPYING", "share/licenses/geth-COPYING")
    put(clients / "geth/COPYING.LESSER", "share/licenses/geth-COPYING.LESSER")
    put(clients / "ream/LICENSE", "share/licenses/ream-LICENSE")
    if (ROOT / "third_party").is_dir():
        for file in (ROOT / "third_party").rglob("*"):
            if file.is_file():
                put(file, str(file.relative_to(ROOT)))
    ream_pin = json.loads((ROOT / "client/ream/source.json").read_text())
    build_records = out / "share/build"
    build_records.mkdir(parents=True, exist_ok=True)
    (build_records / "source-identity.json").write_text(json.dumps(source_identity, sort_keys=True, indent=2) + "\n")
    for name, record in records.items():
        (build_records / (name + ".json")).write_text(json.dumps(record, sort_keys=True, indent=2) + "\n")
    verify_source(ROOT, source_identity)
    manifest = {"format": 1, "profile": "pq-lean-f-native-lab-v1", "productionEnabled": False,
                "sourceIdentity": source_identity, "dependencyManifestSHA256": next(iter(dependency_hashes)),
                "n1DependencyManifestSHA256": n1_record["manifestSHA256"],
                "gethSourceManifestSHA256": json.loads((ROOT / "client/geth/source.json").read_text())["treeManifestSHA256"],
                "reamSourceManifestSHA256": ream_pin["treeManifestSHA256"],
                "proofsIncluded": False, "publicTestKeysOnly": True,
                "payloads": {str(p.relative_to(out)): {"sha256": sha(p), "bytes": p.stat().st_size,
                             "mode": oct(p.stat().st_mode & 0o777)} for p in out.rglob("*") if p.is_file()}}
    (out / "manifest.json").write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"files": len(manifest["payloads"]), "manifestSHA256": sha(out / "manifest.json"), "proofsIncluded": False}))


if __name__ == "__main__":
    main()
