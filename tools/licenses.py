#!/usr/bin/env python3
"""Collect pinned dependency licence declarations and verbatim notice files offline."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
# Path packages under these directories are modified copies of third-party crates and are listed with their own
# notices (including MODIFICATIONS.md); every other path package is this project's code under its top-level licence.
VENDORED = [ROOT / "prover/pinned-deps", ROOT / "prover/crates", ROOT / "prover/final-verifier/crates"]


def notice(name):
    n = Path(name).name.lower()
    return n.startswith(("license", "licence", "copying", "notice", "copyright")) and not n.endswith((".rs", ".go", ".py"))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sources", type=Path, required=True)
    ap.add_argument("--dependencies", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=False)
    (a.out / "licenses").mkdir()
    env = dict(os.environ, CARGO_NET_OFFLINE="true", RUSTUP_TOOLCHAIN="1.98.0")

    def save(data):
        name = hashlib.sha256(data).hexdigest() + ".txt"
        (a.out / "licenses" / name).write_bytes(data)
        return "licenses/" + name

    packages = {}
    for work in [a.sources / "ream", ROOT / "prover/native", ROOT / "prover/leaf", ROOT / "prover/tree", ROOT / "wallet/crypto"]:
        meta = json.loads(subprocess.check_output(["cargo", "metadata", "--offline", "--locked", "--format-version", "1"], cwd=work, env=env))
        for p in meta["packages"]:
            directory = Path(p["manifest_path"]).parent.resolve()
            source = p["source"]
            if not source:
                if not any(directory.is_relative_to(v.resolve()) for v in VENDORED):
                    continue
                source = "path+" + directory.relative_to(ROOT.resolve()).as_posix()
            key = (p["name"], p["version"], source)
            if key in packages:
                continue
            candidates = [(f, f.name) for f in directory.iterdir() if f.is_file() and
                          (notice(f.name) or (source.startswith("path+") and f.name == "MODIFICATIONS.md"))]
            if p.get("license_file"):
                f = directory / p["license_file"]
                if f.is_file():
                    candidates.append((f, p["license_file"]))
            # Workspace members inherit the licence at the Git checkout root.
            if not candidates and source.startswith("git+"):
                for ancestor in directory.parents:
                    if ancestor.name == "checkouts":
                        break
                    candidates = [(f, str(f.relative_to(ancestor))) for f in ancestor.iterdir() if f.is_file() and notice(f.name)]
                    if candidates:
                        break
            packages[key] = {"name": p["name"], "version": p["version"], "source": source,
                             "license": p["license"], "notices": [{"originalName": name, "file": save(f.read_bytes())} for f, name in candidates]}
    (a.out / "rust-dependencies.json").write_text(json.dumps(list(packages.values()), indent=2) + "\n")
    modules = json.loads((a.dependencies / "DEPENDENCIES.json").read_text())["go"]
    for module in modules:
        escaped = "".join("!" + c.lower() if c.isupper() else c for c in module["module"])
        archive = a.dependencies / "go-proxy" / escaped / "@v" / (module["version"] + ".zip")
        with zipfile.ZipFile(archive) as z:
            module["notices"] = [{"originalName": name.split("/", 1)[-1], "file": save(z.read(name))}
                                 for name in z.namelist() if not name.endswith("/") and notice(name)]
            if not module["notices"]:
                for name in z.namelist():
                    if name.endswith(".go"):
                        header = z.read(name).split(b"\npackage ", 1)[0]
                        if b"Copyright" in header and b"license" in header.lower():
                            module["notices"].append({"originalName": name + " (source header)", "file": save(header + b"\n")})
                            break
        module["license"] = "See verbatim upstream notices"
    (a.out / "go-dependencies.json").write_text(json.dumps(modules, indent=2) + "\n")
    summary = {"rustPackages": len(packages), "goModules": len(modules),
               "rustWithoutBundledNotice": sum(not p["notices"] for p in packages.values()),
               "rustWithoutSPDX": sum(not p["license"] for p in packages.values()),
               "goWithoutBundledNotice": sum(not p["notices"] for p in modules),
               "noticeFiles": len(list((a.out / "licenses").iterdir())),
               "scope": "Dependency metadata and verbatim notices; not a legal compatibility opinion."}
    (a.out / "INVENTORY.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
