"""Bind build inputs and output records to one committed source snapshot."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git(root, *args):
    command = ["git"]
    marker = root / ".git"
    if marker.is_file() and os.name != "nt":
        target = marker.read_text().removeprefix("gitdir: ").strip()
        if len(target) > 2 and target[1] == ":":
            target = subprocess.check_output(["wslpath", "-u", target], text=True).strip()
            command += ["--git-dir=" + target, "--work-tree=" + str(root)]
    return subprocess.check_output(command + list(args), cwd=root,
                                   env=dict(os.environ, GIT_OPTIONAL_LOCKS="0"))


def file_path(root, relative):
    path = PurePosixPath(relative)
    if path.is_absolute() or not path.parts or ".." in path.parts or "\\" in relative:
        raise ValueError("invalid source path: " + relative)
    current = root
    for part in path.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError("source symlink is not a regular build input: " + relative)
    return current


def identity_hash(files):
    return hashlib.sha256(json.dumps(files, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def check_files(root, identity):
    if identity.get("format") != 1 or not identity.get("files"):
        raise ValueError("missing source identity")
    if identity_hash(identity["files"]) != identity.get("filesSHA256"):
        raise ValueError("source manifest identity mismatch")
    for relative, row in identity["files"].items():
        path = file_path(root, relative)
        if row["mode"] not in ("100644", "100755") or not path.is_file() or sha(path) != row["sha256"]:
            raise ValueError("source content mismatch: " + relative)


def capture_source(root):
    root = Path(root).resolve()
    if not (root / ".git").exists():
        identity = json.loads((root / "SOURCE-IDENTITY.json").read_text())
        if (root / "SOURCE-COMMIT").read_text().strip() != identity.get("commit"):
            raise ValueError("archive source commit mismatch")
        check_files(root, identity)
        return identity
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError("commit the complete source tree before building or packaging")
    files = {}
    for entry in git(root, "ls-tree", "-rz", "HEAD").split(b"\0"):
        if not entry:
            continue
        metadata, name = entry.split(b"\t", 1)
        mode, kind, blob = metadata.decode().split()
        relative = name.decode("utf-8")
        path = file_path(root, relative)
        if kind != "blob" or mode not in ("100644", "100755") or not path.is_file():
            raise ValueError("unsupported source object: " + relative)
        # Check bytes against Git too: an ignored stat change or index flag must
        # not make a modified file eligible for a committed-source attestation.
        h = hashlib.sha1(("blob " + str(path.stat().st_size) + "\0").encode())
        digest = hashlib.sha256()
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                h.update(chunk)
                digest.update(chunk)
        if h.hexdigest() != blob:
            raise ValueError("working bytes differ from committed blob: " + relative)
        files[relative] = {"mode": mode, "sha256": digest.hexdigest()}
    return {"format": 1, "commit": git(root, "rev-parse", "HEAD").decode().strip(),
            "tree": git(root, "rev-parse", "HEAD^{tree}").decode().strip(),
            "files": files, "filesSHA256": identity_hash(files)}


def verify_source(root, identity):
    if not identity or capture_source(root) != identity:
        raise ValueError("build source identity differs from the current source snapshot")
    return identity


def copy_tracked(root, relative, dest, identity):
    """Copy only attested files, excluding ignored caches and build artifacts."""
    root, dest = Path(root), Path(dest)
    prefix = relative.rstrip("/") + "/" if relative else ""
    selected = {name: row for name, row in identity["files"].items() if name.startswith(prefix)}
    if not selected:
        raise ValueError("no tracked files under " + relative)
    dest.mkdir(parents=True, exist_ok=False)
    for name, row in selected.items():
        source = file_path(root, name)
        if not source.is_file() or sha(source) != row["sha256"]:
            raise ValueError("source changed while copying: " + name)
        target = file_path(dest, name[len(prefix):])
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        target.chmod(int(row["mode"], 8) & 0o777)
        if sha(target) != row["sha256"]:
            raise ValueError("source copy changed: " + name)


def verify_build(root, record, required_binaries, binary_root, *, identity=None):
    if record.get("status") != "PASS":
        raise ValueError("build has not passed")
    if record.get("optionalProfiles", []) != []:
        raise ValueError("unsupported optional profile in build record")
    expected = identity if identity is not None else capture_source(root)
    if record.get("sourceIdentity") != expected:
        raise ValueError("missing or stale build source identity")
    binaries = record.get("binaries", {})
    if not set(required_binaries).issubset(binaries):
        raise ValueError("build record omits required binaries")
    for relative, digest in binaries.items():
        path = file_path(Path(binary_root), relative)
        if not path.is_file() or sha(path) != digest:
            raise ValueError("build output mismatch: " + relative)
    return expected


def verify_runtime(root, runtime, manifest):
    """Recheck the assembly's source/output bindings before a release archive."""
    if manifest.get("optionalProfiles", []) != []:
        raise ValueError("unsupported optional profile in runtime manifest")
    identity = capture_source(root)
    if manifest.get("sourceIdentity") != identity:
        raise ValueError("runtime was assembled from another source snapshot")
    if json.loads((runtime / "share/build/source-identity.json").read_text()) != identity:
        raise ValueError("runtime source record differs from its manifest")
    specifications = {
        "clients": (runtime, ["bin/geth", "bin/ream", "lib/libpq_final_native.so", "lib/libpq_migrate_tree.so"]),
        "demo-tools": (runtime / "libexec", ["profile-tool", "profile-tool-three", "fresh-public-keys", "export-signed", "audit-history", "pqlean-txs", "pq-n1-txs"]),
        "prover": (runtime / "prover-runtime/bin", ["pq-migrate-leaf", "pq-migrate-tree", "pq-test-crypto", "pq-final-verify"]),
        "aggregate": (runtime / "aggregate-runtime", ["bin/pq-migrate-tree", "bin/aggregate-verify", "lib/libpq_migrate_tree.so"]),
    }
    for name, (binary_root, required) in specifications.items():
        record = json.loads((runtime / "share/build" / (name + ".json")).read_text())
        if name == "clients":
            # Client executables live behind relocatable wrappers in runtime/bin.
            record = dict(record, binaries={"libexec/" + p[4:] if p.startswith("bin/") else p: d
                                            for p, d in record.get("binaries", {}).items()})
            required = ["libexec/" + p[4:] if p.startswith("bin/") else p for p in required]
        verify_build(root, record, required, binary_root, identity=identity)
        if not record.get("dependencyManifestSHA256") or record["dependencyManifestSHA256"] != manifest.get("dependencyManifestSHA256"):
            raise ValueError("runtime dependency provenance mismatch: " + name)
    for name in ("geth", "ream"):
        pin = json.loads((root / "client" / name / "source.json").read_text())
        if manifest.get(name + "SourceManifestSHA256") != pin["treeManifestSHA256"]:
            raise ValueError("runtime client source manifest mismatch: " + name)
    return identity
