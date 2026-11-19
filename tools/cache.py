#!/usr/bin/env python3
"""Export only the dependencies named by Cargo metadata and Go package metadata.

Run on a prepared build machine. This command never downloads dependencies.
It does not copy credentials, user configuration, compiler outputs or proofs.
Cargo keeps Git sources separate, including distinct revisions with identical
package names and versions. A recipient must verify CACHE-SHA256.json before use.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
from dependency_integrity import content, identity, export_checkout, verify_bundle


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def objects(text):
    decoder = json.JSONDecoder()
    while text.strip():
        text = text.lstrip()
        value, end = decoder.raw_decode(text)
        yield value
        text = text[end:]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sources", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--cargo-home", type=Path,
                    default=Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo")))
    a = ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    target = a.out.resolve()
    target.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, CARGO_NET_OFFLINE="true", RUSTUP_TOOLCHAIN="1.98.0",
               GOTOOLCHAIN="local", GOPROXY="off", GOSUMDB="off", GOFLAGS="-mod=readonly")
    cargo = a.cargo_home.resolve()
    env["CARGO_HOME"] = str(cargo)
    copied = set()
    git_crates, git_checkouts = {}, {}

    def copy(source, dest):
        if dest in copied:
            return
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)
        copied.add(dest)

    inventory = []
    workspaces = [a.sources / "ream", root / "prover/native"]
    workspaces += [root / rel for rel in ("prover/leaf", "prover/tree", "prover/aggregate", "wallet/crypto")
                   if (root / rel / "Cargo.toml").is_file()]
    for work in workspaces:
        meta = json.loads(subprocess.check_output(
            ["cargo", "metadata", "--locked", "--offline", "--format-version", "1"], cwd=work, env=env))
        for package in meta["packages"]:
            source = package["source"] or ""
            inventory.append({k: package[k] for k in ("name", "version", "source", "license")})
            if source.startswith("registry+"):
                manifest = Path(package["manifest_path"])
                registry = manifest.parent.parent.name
                name = package["name"].lower()
                index_path = ("1/" + name if len(name) == 1 else "2/" + name if len(name) == 2
                              else "3/" + name[0] + "/" + name if len(name) == 3
                              else name[:2] + "/" + name[2:4] + "/" + name)
                files = [Path("registry/cache") / registry / f"{package['name']}-{package['version']}.crate",
                         Path("registry/index") / registry / ".cache" / index_path,
                         Path("registry/index") / registry / "config.json"]
                for rel in files:
                    copy(cargo / rel, target / "cargo" / rel)
            elif source.startswith("git+"):
                rel = Path(package["manifest_path"]).relative_to(cargo)
                checkout = Path(*rel.parts[:4])
                dest = target / "cargo" / checkout
                if dest not in copied:
                    commit = source.rsplit("#", 1)[-1]
                    files = export_checkout(cargo / checkout, dest, commit)
                    git_checkouts[checkout.as_posix()] = {"commit": commit, "files": files, "contentSHA256": identity(files)}
                    copied.add(dest)
                crate_root = rel.parent.relative_to(checkout)
                git_crates[(package["name"], package["version"], source)] = {
                    "name": package["name"], "version": package["version"], "source": source,
                    "commit": source.rsplit("#", 1)[-1], "checkout": checkout.as_posix(),
                    "crateRoot": crate_root.as_posix(), "contentSHA256": identity(content(dest / crate_root))}
                db = Path("git/db") / rel.parts[2]
                dest = target / "cargo" / db
                if dest not in copied:
                    shutil.copytree(cargo / db, dest)
                    # Bare cache configuration is reconstructed without local paths.
                    (dest / "config").write_text("[core]\n\tbare = true\n")
                    copied.add(dest)

    geth = a.sources / "geth"
    command = ["go", "list", "-deps", "-test", "-json", "-tags", "pq_final,pq_aggregate",
               "./cmd/geth", "./core", "./core/vm", "./core/types", "./core/txpool/...",
               "./miner", "./eth", "./eth/catalyst", "./eth/fetcher", "./eth/protocols/eth", "./internal/ethapi", "./graphql"]
    packages = list(objects(subprocess.check_output(command, cwd=geth, env=env, text=True)))
    modules = {(p["Module"]["Path"], p["Module"].get("Version")): p["Module"]
               for p in packages if p.get("Module", {}).get("Version")}
    module_cache = Path(subprocess.check_output(["go", "env", "GOMODCACHE"], env=env, text=True).strip())
    download = module_cache / "cache/download"
    # Lazy loading also consults module metadata outside the compile closure.
    # Restrict that metadata to this project's go.sum, never the whole user cache.
    sums = {(line.split()[0], line.split()[1].removesuffix("/go.mod"))
            for line in (geth / "go.sum").read_text().splitlines() if line.strip()}
    for path, version in sums:
        escaped = "".join("!" + c.lower() if c.isupper() else c for c in path)
        for suffix in (".mod", ".info"):
            rel = Path(escaped) / "@v" / (version + suffix)
            if (download / rel).is_file():
                copy(download / rel, target / "go-proxy" / rel)
    for (path, version), module in modules.items():
        escaped = "".join("!" + c.lower() if c.isupper() else c for c in path)
        for suffix in (".zip", ".mod", ".info"):
            rel = Path(escaped) / "@v" / (version + suffix)
            copy(download / rel, target / "go-proxy" / rel)
    (target / "DEPENDENCIES.json").write_text(json.dumps({
        "rust": list({json.dumps(p, sort_keys=True): p for p in inventory}.values()),
        "go": [{"module": p, "version": v} for p, v in sorted(modules)]}, indent=2) + "\n")
    (target / "GIT-CRATES.json").write_text(json.dumps({"schema": 1, "crates": list(git_crates.values()),
        "checkouts": git_checkouts}, sort_keys=True, indent=2) + "\n")
    checks = {str(p.relative_to(target)): sha(p) for p in target.rglob("*") if p.is_file()}
    (target / "CACHE-SHA256.json").write_text(json.dumps(checks, sort_keys=True, indent=2) + "\n")
    verify_bundle(target)
    print(json.dumps({"gitCrates": len(git_crates), "files": len(checks), "bytes": sum(p.stat().st_size for p in target.rglob("*") if p.is_file())}))


if __name__ == "__main__":
    main()
