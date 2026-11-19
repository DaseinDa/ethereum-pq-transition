#!/usr/bin/env python3
"""Refuse garbled or unexpected non-ASCII text in authored files and in patch additions.

The package once carried the GBK misdecoding of the section sign: a console round trip
turned U+00A7 into U+6402 inside a client patch and three authored files. This guard refuses
that whole class, not the one code point that was seen. Every character outside ASCII in an
authored text file, or in an added line of a shipped client patch, must belong to the short
allow list of typographic and mathematical symbols below. CJK ideographs, fullwidth forms,
C1 controls, the replacement character and private-use code points are therefore refused, and
so is any other character the list does not name, which keeps a new misdecoding from slipping
through because it happens to land outside the CJK blocks. The one intentional non-ASCII test
string of the wallet suite is allowed by file and content.

Authored text is the demo, wallet, tools, tests, docs, bench and formal trees, the top-level
Markdown files and the client replay tool. Vendored or imported sources under prover/ and the licence
texts under third_party/ are pinned by their own manifests and are not audited here. Removed and
context lines of a patch are historical input, so check_patch reads only the added lines of
unified-diff hunks, and client/sources.py calls it before every patch is applied.

This file and its tests spell every non-ASCII code point with chr(), so that they pass the
audit themselves.
"""
import argparse
import json
from pathlib import Path
import unicodedata

ROOT = Path(__file__).resolve().parents[1]
# Typographic and mathematical symbols that authored prose and comments may use.
ALLOWED_NON_ASCII = frozenset(map(chr, (
    0x00A7,  # section sign
    0x00B1,  # plus-minus sign
    0x00B7,  # middle dot
    0x00D7,  # multiplication sign
    0x2013,  # en dash
    0x2014,  # em dash
    0x2016,  # double vertical line (concatenation)
    0x2018, 0x2019, 0x201C, 0x201D,  # curly quotes
    0x2026,  # horizontal ellipsis
    0x2032,  # prime
    0x2192,  # rightwards arrow
    0x2208,  # element of
    0x2212,  # minus sign
    0x2248,  # almost equal to
    0x2260,  # not equal to
    0x2261,  # identical to
    0x2264, 0x2265,  # less-than or greater-than or equal to
)))
SECTION_SIGN_CORRUPTION = chr(0x6402)  # what a GBK round trip makes of the section sign
# Intentional non-ASCII content, by authored file and exact substring.
ALLOWED_CONTENT = {"wallet/test_wallet_epochs.py": (chr(0x975E) + "ASCII",)}
AUTHORED_DIRECTORIES = ("demo", "wallet", "tools", "tests", "docs", "bench", "formal")
AUTHORED_FILES = ("client/sources.py",)
TEXT_SUFFIXES = {".py", ".go", ".rs", ".toml", ".lock", ".json", ".md", ".txt",
                 ".sh", ".yaml", ".yml", ".sol", ".bin-runtime", ".tla"}


class ForbiddenTextError(ValueError):
    """An authored line or patch addition holds a character outside ASCII and the allow list."""


def _describe(character):
    name = unicodedata.name(character, "unnamed")
    return f"U+{ord(character):04X} ({name})"


def check_line(path, number, line, allowed_content=()):
    """Raise ForbiddenTextError for the first character of the line outside ASCII and the allow list."""
    for content in allowed_content:
        line = line.replace(content, "")
    for character in line:
        if ord(character) < 0x80 or character in ALLOWED_NON_ASCII:
            continue
        reason = "forbidden non-ASCII character"
        if character == SECTION_SIGN_CORRUPTION:
            reason = "forbidden U+6402 section-sign corruption"
        raise ForbiddenTextError(f"{path}:{number}: {reason} {_describe(character)}")


def check_patch(path):
    """Check the UTF-8 unified-diff additions of a patch before publishing or applying it."""
    path = Path(path)
    in_hunk = False
    with path.open(encoding="utf-8") as stream:
        for number, line in enumerate(stream, 1):
            if line.startswith("diff --git "):
                in_hunk = False
            elif line.startswith("@@ "):
                in_hunk = True
            elif in_hunk and line.startswith("+"):
                check_line(path, number, line[1:])
    return path


def check_file(path, root):
    """Check every line of one authored text file; the allow list by content applies per file."""
    path = Path(path)
    allowed = ALLOWED_CONTENT.get(path.relative_to(root).as_posix(), ())
    with path.open(encoding="utf-8") as stream:
        for number, line in enumerate(stream, 1):
            check_line(path, number, line, allowed)
    return path


def authored_files(root):
    root = Path(root)
    files = []
    for directory in AUTHORED_DIRECTORIES:
        for path in sorted((root / directory).rglob("*")):
            if path.is_file() and path.suffix in TEXT_SUFFIXES and "__pycache__" not in path.parts:
                files.append(path)
    files.extend(sorted(p for p in root.glob("*.md") if p.is_file()))
    files.extend(root / name for name in AUTHORED_FILES if (root / name).is_file())
    return files


def audit_package(root):
    """Audit the authored text and every shipped client patch's additions under root."""
    root = Path(root)
    files = authored_files(root)
    for path in files:
        check_file(path, root)
    patches = sorted((root / "client").rglob("*.patch"))
    for path in patches:
        check_patch(path)
    return {"authoredFiles": len(files), "patches": len(patches),
            "allowedNonASCII": "".join(sorted(ALLOWED_NON_ASCII)), "matches": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=ROOT, help="package root for the full audit")
    parser.add_argument("--patch", type=Path, action="append", help="check only this generated patch; repeatable")
    args = parser.parse_args()
    if args.patch:
        for path in args.patch:
            check_patch(path)
        result = {"patches": len(args.patch), "allowedNonASCII": "".join(sorted(ALLOWED_NON_ASCII)), "matches": 0}
    else:
        result = audit_package(args.root)
    print(json.dumps({"status": "PASS", **result}, ensure_ascii=True))


if __name__ == "__main__":
    main()
