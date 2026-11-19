"""Content identities for the Git crates in an offline dependency bundle."""
import hashlib
import io
import json
import posixpath
from pathlib import Path, PurePosixPath
import subprocess
import tarfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def content(root, checkout_boundary=None):
    files = {}
    for p in sorted(root.rglob("*")):
        # Cargo reconstructs checkout-local .git metadata from the bundled bare
        # database. It is not source content and is allowed only in the build copy.
        if checkout_boundary is not None and ".git" in p.relative_to(checkout_boundary).parts:
            continue
        effective = p
        if p.is_symlink():
            if checkout_boundary is None:
                raise ValueError("symlink in Git dependency bundle: " + str(p))
            effective = p.resolve(strict=True)
            if not effective.is_relative_to(checkout_boundary.resolve()) or not effective.is_file():
                raise ValueError("escaping/non-file link in Git dependency checkout")
        if p.is_file():
            files[p.relative_to(root).as_posix()] = {
                "sha256": sha(effective), "executable": bool(effective.stat().st_mode & 0o111)}
    return files


def identity(files):
    return hashlib.sha256(json.dumps(files, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def relative(root, name):
    p = PurePosixPath(name)
    if p.is_absolute() or not p.parts or ".." in p.parts or "\\" in name:
        raise ValueError("invalid bundle-relative path")
    return root.joinpath(*p.parts)


def export_checkout(checkout, dest, revision):
    """Only committed files are eligible; local additions are never copied."""
    git = lambda *args: subprocess.check_output(["git", "-C", str(checkout), *args])
    if git("rev-parse", "HEAD").decode().strip() != revision:
        raise ValueError("Git checkout revision differs from Cargo's resolved source")
    subprocess.run(["git", "-C", str(checkout), "diff", "--quiet", "HEAD", "--"], check=True)
    dest.mkdir(parents=True, exist_ok=False)
    with tarfile.open(fileobj=io.BytesIO(git("archive", "--format=tar", revision))) as archive:
        members = {item.name.rstrip("/"): item for item in archive.getmembers()}
        def regular(item, seen=()):
            if item.name in seen:
                raise ValueError("cyclic Git dependency link")
            if item.isfile():
                return archive.extractfile(item).read(), item.mode
            if item.issym():
                name = posixpath.normpath(posixpath.join(posixpath.dirname(item.name), item.linkname))
                relative(dest, name)  # Reject escaping or absolute links, including dangling links.
                if name not in members:
                    raise ValueError("dangling Git dependency link")
                return regular(members[name], (*seen, item.name))
            raise ValueError("unsupported Git dependency entry: " + item.name)
        for item in archive.getmembers():
            target = relative(dest, item.name)
            if item.isdir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                data, mode = regular(item)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                target.chmod(0o755 if mode & 0o111 else 0o644)
    (dest / ".cargo-ok").write_bytes(b"")
    return content(dest)


def verify_git(bundle, cargo_override=None):
    inventory = json.loads((bundle / "DEPENDENCIES.json").read_text())["rust"]
    manifest = json.loads((bundle / "GIT-CRATES.json").read_text())
    if manifest["schema"] != 1:
        raise ValueError("unknown Git crate identity schema")
    key = lambda row: (row["name"], row["version"], row["source"])
    required = {key(row) for row in inventory if (row.get("source") or "").startswith("git+")}
    supplied = [key(row) for row in manifest["crates"]]
    if required != set(supplied) or len(supplied) != len(set(supplied)):
        raise ValueError("Git crate inventory coverage mismatch")
    cargo = cargo_override or bundle / "cargo"
    roots = {}
    for checkout, record in manifest["checkouts"].items():
        if not checkout.startswith("git/checkouts/"):
            raise ValueError("invalid Git checkout location")
        root = relative(cargo, checkout)
        observed = content(root, checkout_boundary=root if cargo_override is not None else None)
        if not observed or observed != record["files"] or identity(observed) != record["contentSHA256"]:
            raise ValueError("Git checkout content mismatch: " + checkout)
        roots[checkout] = root
    used = set()
    for crate in manifest["crates"]:
        used.add(crate["checkout"])
        root = roots[crate["checkout"]]
        revision = crate["source"].rsplit("#", 1)[-1]
        if revision != crate["commit"] or manifest["checkouts"][crate["checkout"]]["commit"] != revision:
            raise ValueError("Git source/commit binding mismatch")
        directory = root if crate["crateRoot"] == "." else relative(root, crate["crateRoot"])
        if not (directory / "Cargo.toml").is_file() or identity(content(directory, checkout_boundary=root if cargo_override is not None else None)) != crate["contentSHA256"]:
            raise ValueError("Git crate content mismatch: " + crate["name"])
    if used != set(roots):
        raise ValueError("unaccounted Git checkout")
    return len(supplied)


def verify_bundle(bundle, expected_manifest_sha256=None):
    manifest = bundle / "CACHE-SHA256.json"
    if expected_manifest_sha256 is not None:
        expected = expected_manifest_sha256.lower()
        if len(expected) != 64 or any(ch not in "0123456789abcdef" for ch in expected):
            raise ValueError("expected cache hash must be 64 hexadecimal characters")
        if manifest.is_symlink() or sha(manifest) != expected:
            raise ValueError("dependency manifest differs from the trusted cache hash")
    checks = json.loads(manifest.read_text())
    actual = {p.relative_to(bundle).as_posix() for p in bundle.rglob("*") if p.is_file()}
    if actual != set(checks) | {"CACHE-SHA256.json"}:
        raise ValueError("dependency bundle file set mismatch")
    for name, expected in checks.items():
        path = relative(bundle, name)
        if path.is_symlink() or sha(path) != expected:
            raise ValueError("dependency hash mismatch: " + name)
    verify_git(bundle)
    return checks
