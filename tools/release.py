#!/usr/bin/env python3
"""Create local runtime and offline source archives; never upload or publish."""
import argparse
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tarfile
from dependency_integrity import verify_bundle
from build_provenance import capture_source, verify_runtime
from n1_dependencies import verify_wheelhouse

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    command = ["git"]
    marker = ROOT / ".git"
    if marker.is_file():
        target = marker.read_text().removeprefix("gitdir: ").strip()
        # WSL can read a worktree made by Windows Git without rewriting its
        # ownership metadata. Ordinary Linux checkouts use Git's default path.
        if len(target) > 2 and target[1] == ":":
            target = subprocess.check_output(["wslpath", "-u", target], text=True).strip()
            command += ["--git-dir=" + target, "--work-tree=" + str(ROOT)]
    return subprocess.check_output(command + list(args), cwd=ROOT)


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as file:
        for chunk in iter(lambda: file.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def archive(path, entries):
    with path.open("xb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode="w|") as tar:
            for name, source, mode in entries:
                info = tarfile.TarInfo(name)
                info.mode = mode
                info.uid = info.gid = info.mtime = 0
                if isinstance(source, bytes):
                    info.size = len(source)
                    tar.addfile(info, io.BytesIO(source))
                else:
                    if source.is_symlink() or not source.is_file():
                        raise ValueError("only regular files can be packaged: " + name)
                    info.size = source.stat().st_size
                    with source.open("rb") as file:
                        tar.addfile(info, file)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runtime", type=Path, required=True)
    ap.add_argument("--cache", type=Path, required=True)
    ap.add_argument("--dependencies", type=Path, required=True)
    ap.add_argument("--expect-cache-sha256", required=True, help="trusted SHA-256 of CACHE-SHA256.json")
    ap.add_argument("--n1-dependencies", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    runtime, cache, deps, out = [p.resolve() for p in (a.runtime, a.cache, a.dependencies, a.out)]
    if git("status", "--porcelain"):
        raise ValueError("commit the reviewed source tree before packaging")
    commit = git("rev-parse", "HEAD").decode().strip()
    source_identity = capture_source(ROOT)
    spec = importlib.util.spec_from_file_location("installer", ROOT / "demo/install.py")
    installer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(installer)
    manifest = installer.check_payloads(runtime)
    verify_runtime(ROOT, runtime, manifest)
    if manifest.get("proofsIncluded") is not False:
        raise ValueError("runtime must not include expiring migration proofs")
    for name in ("geth", "ream"):
        pin = json.loads((ROOT / "client" / name / "source.json").read_text())
        if sha(cache / pin["archive"]) != pin["sha256"]:
            raise ValueError("upstream archive mismatch: " + name)
    dependency_hashes = verify_bundle(deps, expected_manifest_sha256=a.expect_cache_sha256)
    if manifest.get("dependencyManifestSHA256") != a.expect_cache_sha256.lower():
        raise ValueError("runtime and release use different dependency bundles")
    n1_deps = a.n1_dependencies.resolve()
    n1_record = verify_wheelhouse(n1_deps)
    runtime_n1_record = verify_wheelhouse(runtime / "share/n1-wheels")
    if n1_record != runtime_n1_record or manifest.get("n1DependencyManifestSHA256") != n1_record["manifestSHA256"]:
        raise ValueError("runtime and release use different N1 dependency bundles")
    out.mkdir(parents=True, exist_ok=False)
    runtime_entries = [("pq-migrate-runtime/" + rel, runtime / rel, int(row["mode"], 8))
                       for rel, row in sorted(manifest["payloads"].items())]
    runtime_entries.append(("pq-migrate-runtime/manifest.json", runtime / "manifest.json", 0o644))
    archive(out / "runtime.tar.gz", runtime_entries)
    # Read committed blobs, not working-tree files or ignored outputs.
    source_tar = git("archive", "--format=tar", commit)
    entries = []
    with tarfile.open(fileobj=io.BytesIO(source_tar)) as tar:
        for item in tar:
            if item.isfile():
                entries.append(("pq-migrate-source/" + item.name, tar.extractfile(item).read(), item.mode))
            elif not item.isdir():
                raise ValueError("unexpected non-regular Git object: " + item.name)
    entries.append(("pq-migrate-source/SOURCE-COMMIT", (commit + "\n").encode(), 0o644))
    entries.append(("pq-migrate-source/SOURCE-IDENTITY.json", (json.dumps(source_identity, sort_keys=True, indent=2) + "\n").encode(), 0o644))
    for name in ("geth.tar", "ream.tar"):
        entries.append(("pq-migrate-source/cache/" + name, cache / name, 0o644))
    for rel in sorted(set(dependency_hashes) | {"CACHE-SHA256.json"}):
        entries.append(("pq-migrate-source/dependencies/" + rel, deps / rel,
                        0o755 if (deps / rel).stat().st_mode & 0o111 else 0o644))
    for file in sorted(n1_deps.rglob("*")):
        if file.is_file():
            entries.append(("pq-migrate-source/n1-dependencies/" + file.relative_to(n1_deps).as_posix(), file, 0o644))
    archive(out / "offline-source.tar.gz", entries)
    result = {"sourceCommit": commit, "sourceFilesSHA256": source_identity["filesSHA256"], "runtimeManifestSHA256": sha(runtime / "manifest.json"),
              "dependencyManifestSHA256": sha(deps / "CACHE-SHA256.json"),
              "n1DependencyManifestSHA256": n1_record["manifestSHA256"],
              "publication": "local-only", "productionEnabled": False,
              "toolchainsIncluded": False, "proofsIncluded": False,
              "archives": {p.name: {"sha256": sha(p), "bytes": p.stat().st_size} for p in sorted(out.glob("*.tar.gz"))}}
    (out / "RELEASE.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "SHA256SUMS").write_text("".join(sha(p) + "  " + p.name + "\n" for p in sorted(out.iterdir()) if p.is_file()))
    print(json.dumps(result))


if __name__ == "__main__":
    main()
