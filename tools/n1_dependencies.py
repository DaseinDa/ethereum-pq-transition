#!/usr/bin/env python3
"""Collect, verify and install the N1 Python closure without network access.

Collection accepts exactly one pre-downloaded wheel for each pinned package. Each
wheel must match the committed PyPI filename, size and SHA-256 inventory. The
resulting bundle's manifest digest must be fixed separately before installation.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path, PurePosixPath


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def default_inventory():
    here = Path(__file__).resolve().parent
    installed = here / "n1/DEPENDENCIES.json"
    return installed if installed.is_file() else here.parent / "demo/n1/DEPENDENCIES.json"


def approved_wheels(inventory):
    approved = {}
    for package, info in inventory["packages"].items():
        for filename, digest in info["wheels"].items():
            approved[filename] = (package, info["version"], digest)
    return approved


def collect(wheelhouse, output, inventory_path):
    inventory = json.loads(inventory_path.read_text(encoding="utf-8"))
    approved, selected = approved_wheels(inventory), {}
    for source in sorted(wheelhouse.glob("*.whl")):
        if source.is_symlink() or source.name not in approved:
            raise ValueError("unapproved wheel: " + source.name)
        package, version, expected = approved[source.name]
        if source.stat().st_size != expected["bytes"] or sha(source) != expected["sha256"]:
            raise ValueError("wheel content differs from the pinned inventory: " + source.name)
        if package in selected:
            raise ValueError("supply one compatible wheel per package: " + package)
        selected[package] = (source, version, expected["sha256"])
    if selected.keys() != inventory["packages"].keys():
        raise ValueError("incomplete wheelhouse: " + ", ".join(sorted(inventory["packages"].keys() - selected.keys())))
    output.mkdir(parents=True, exist_ok=False)
    wheels = output / "wheels"
    wheels.mkdir()
    shutil.copyfile(inventory_path, output / "DEPENDENCIES.json")
    requirements = []
    for name, (source, version, digest) in sorted(selected.items()):
        shutil.copyfile(source, wheels / source.name)
        requirements.append(f"{name}=={version} --hash=sha256:{digest}")
    (output / "requirements.lock").write_text("\n".join(requirements) + "\n", encoding="utf-8", newline="\n")
    files = {p.relative_to(output).as_posix(): {"sha256": sha(p), "bytes": p.stat().st_size}
             for p in sorted(output.rglob("*")) if p.is_file()}
    manifest = {"format": 1, "inventorySHA256": sha(inventory_path), "files": files}
    (output / "MANIFEST.json").write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")
    return sha(output / "MANIFEST.json")


def verify(bundle, expected_manifest, inventory_path):
    if not re.fullmatch(r"[0-9a-fA-F]{64}", expected_manifest or ""):
        raise ValueError("a separately trusted manifest SHA-256 is required")
    bundle = bundle.resolve()
    manifest_path = bundle / "MANIFEST.json"
    if manifest_path.is_symlink() or sha(manifest_path) != expected_manifest.lower():
        raise ValueError("bundle manifest digest mismatch")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("format") != 1 or manifest.get("inventorySHA256") != sha(inventory_path):
        raise ValueError("bundle uses a different dependency inventory")
    files = manifest["files"]
    for name, expected in files.items():
        relative = PurePosixPath(name)
        if not name or relative.is_absolute() or ".." in relative.parts or "\\" in name or str(relative) != name:
            raise ValueError("unsafe bundle path")
        path = bundle / name
        parents = [bundle.joinpath(*relative.parts[:i]) for i in range(1, len(relative.parts) + 1)]
        if any(p.is_symlink() for p in parents) or not path.resolve().is_relative_to(bundle):
            raise ValueError("bundle contains a symlink or escaping path")
        if not path.is_file() or path.stat().st_size != expected["bytes"] or sha(path) != expected["sha256"]:
            raise ValueError("bundle content mismatch: " + name)
    actual = {p.relative_to(bundle).as_posix() for p in bundle.rglob("*") if p.is_file() or p.is_symlink()}
    if actual != set(files) | {"MANIFEST.json"}:
        raise ValueError("bundle inventory mismatch")
    if sha(bundle / "DEPENDENCIES.json") != sha(inventory_path):
        raise ValueError("dependency inventory content mismatch")
    # Recheck approved wheel hashes and exact closure even when a bundle manifest
    # has been re-created: a new manifest cannot bless a changed wheel.
    inventory = json.loads(inventory_path.read_text(encoding="utf-8"))
    approved, found, requirements = approved_wheels(inventory), set(), []
    for path in sorted((bundle / "wheels").glob("*.whl")):
        if path.name not in approved:
            raise ValueError("unapproved bundled wheel")
        name, version, expected = approved[path.name]
        if name in found or sha(path) != expected["sha256"] or path.stat().st_size != expected["bytes"]:
            raise ValueError("changed or duplicate bundled wheel")
        found.add(name)
        requirements.append((name, f"{name}=={version} --hash=sha256:{expected['sha256']}"))
    expected_lock = "\n".join(line for _, line in sorted(requirements)) + "\n"
    if found != inventory["packages"].keys() or (bundle / "requirements.lock").read_text(encoding="utf-8") != expected_lock:
        raise ValueError("bundle closure/requirements mismatch")
    allowed = {"DEPENDENCIES.json", "requirements.lock"} | {
        "wheels/" + p.name for p in (bundle / "wheels").glob("*.whl")}
    if set(files) != allowed:
        raise ValueError("unexpected file in dependency bundle")
    return manifest


def verify_wheelhouse(path, lock_path=None):
    """Assembly API: verify a collected bundle against the committed wheel pins.

    The lock is the approved DEPENDENCIES.json inventory, not a requirements file.
    A bundle manifest alone never approves different wheel content.
    """
    path = Path(path)
    lock_path = Path(lock_path) if lock_path is not None else default_inventory()
    digest = sha(path / "MANIFEST.json")
    manifest = verify(path, digest, lock_path)
    return {"manifestSHA256": digest, "inventorySHA256": manifest["inventorySHA256"],
            "wheels": sum(name.startswith("wheels/") for name in manifest["files"]),
            "files": len(manifest["files"]) + 1}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, default=default_inventory())
    commands = parser.add_subparsers(dest="command", required=True)
    c = commands.add_parser("collect")
    c.add_argument("--wheelhouse", type=Path, required=True)
    c.add_argument("--out", type=Path, required=True)
    for name in ("verify", "install"):
        c = commands.add_parser(name)
        c.add_argument("--bundle", type=Path, required=True)
        c.add_argument("--expect-manifest-sha256", required=True)
        if name == "install":
            c.add_argument("--python", type=Path, required=True, help="Python inside a dedicated N1 virtual environment")
    args = parser.parse_args()
    if args.command == "collect":
        print(json.dumps({"manifestSHA256": collect(args.wheelhouse, args.out, args.inventory)}))
    else:
        manifest = verify(args.bundle, args.expect_manifest_sha256, args.inventory)
        if args.command == "install":
            subprocess.run([str(args.python), "-I", "-m", "pip", "--isolated", "install", "--no-index", "--no-deps",
                            "--require-hashes", "--only-binary=:all:", "--find-links", str(args.bundle / "wheels"),
                            "-r", str(args.bundle / "requirements.lock")], check=True)
        print(json.dumps({"status": "verified" if args.command == "verify" else "installed", "files": len(manifest["files"])}))


if __name__ == "__main__":
    main()
