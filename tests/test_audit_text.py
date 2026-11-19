"""Tests of the text guard that refuses garbled or unexpected non-ASCII characters (fix list F-20).

They run the guard on synthetic files and patches in a temporary tree, and once on the shipped
package. No client source is reconstructed and nothing is built. Non-ASCII code points are
spelled with chr() so that this file passes the audit it tests.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("audit_text", ROOT / "tools/audit_text.py")
audit_text = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit_text)

CORRUPTION = chr(0x6402)  # the GBK misdecoding of U+00A7 that the package once carried
CJK = chr(0x975E)  # the first character of the wallet suite's intentional test string
SECTION, DASH, CONCAT, LEQ, TIMES, ARROW, PRIME = map(chr, (0x00A7, 0x2014, 0x2016, 0x2264, 0x00D7, 0x2192, 0x2032))


def patch_text(added_lines, removed_lines=(), context_lines=()):
    lines = ["diff --git a/x.go b/x.go", "--- a/x.go", "+++ b/x.go", "@@ -1,3 +1,3 @@"]
    lines += [" " + line for line in context_lines]
    lines += ["-" + line for line in removed_lines]
    lines += ["+" + line for line in added_lines]
    return "\n".join(lines) + "\n"


class AuditTextTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for directory in audit_text.AUTHORED_DIRECTORIES + ("client",):
            (self.root / directory).mkdir()

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def test_patch_addition_with_the_known_corruption_is_refused_by_name(self):
        path = self.write("client/geth/0001.patch", patch_text([f"// see {CORRUPTION}14.9"]))
        with self.assertRaisesRegex(audit_text.ForbiddenTextError, r"0001\.patch:5: forbidden U\+6402 section-sign corruption U\+6402"):
            audit_text.check_patch(path)

    def test_patch_addition_with_any_other_unlisted_character_is_refused(self):
        # CJK, fullwidth, ideographic space, replacement, C1 control, private use, and a plain accented letter.
        for code in (0x975E, 0xFF21, 0x3000, 0xFFFD, 0x0085, 0xE000, 0x00E9):
            path = self.write("client/geth/0001.patch", patch_text(["// " + chr(code)]))
            with self.assertRaisesRegex(audit_text.ForbiddenTextError, f"forbidden non-ASCII character U\\+{code:04X}"):
                audit_text.check_patch(path)

    def test_patch_removed_and_context_lines_are_not_checked(self):
        path = self.write("client/geth/0001.patch", patch_text(["// clean"], removed_lines=["// " + CORRUPTION],
                                                             context_lines=["// " + CJK]))
        self.assertEqual(audit_text.check_patch(path), path)

    def test_patch_addition_with_allowed_typography_passes(self):
        line = f"// {SECTION}14.9 (b): RLP(entries) {CONCAT} carrier {CONCAT} sponsor_sig {DASH} tokens {LEQ} 4 {TIMES} bytes, a {ARROW} b, x{PRIME}"
        path = self.write("client/geth/0001.patch", patch_text([line]))
        self.assertEqual(audit_text.check_patch(path), path)

    def test_lines_outside_hunks_are_not_checked(self):
        text = f"Subject: {CORRUPTION} in the header only\n" + patch_text(["// clean"])
        path = self.write("client/geth/0001.patch", text)
        self.assertEqual(audit_text.check_patch(path), path)

    def test_authored_file_with_cjk_is_refused_and_the_location_is_named(self):
        self.write("demo/report.py", f"x = 1\ny = '{CJK}'\n")
        with self.assertRaisesRegex(audit_text.ForbiddenTextError, r"report\.py:2: forbidden non-ASCII character U\+975E"):
            audit_text.audit_package(self.root)

    def test_authored_markdown_at_the_root_and_the_replay_tool_are_audited(self):
        self.write("README.md", f"# Title\n\n{CJK}\n")
        with self.assertRaisesRegex(audit_text.ForbiddenTextError, r"README\.md:3"):
            audit_text.audit_package(self.root)
        (self.root / "README.md").unlink()
        self.write("client/sources.py", f"# {CJK}\n")
        with self.assertRaisesRegex(audit_text.ForbiddenTextError, r"sources\.py:1"):
            audit_text.audit_package(self.root)

    def test_vendored_prover_and_licence_trees_are_outside_the_audit(self):
        self.write("prover/crates/x/src/lib.rs", f"// {CJK} {chr(0x2208)} {chr(0x2261)}\n")
        self.write("third_party/licenses/x.txt", f"{chr(0xA9)} {chr(0x201C)}quoted{chr(0x201D)} {chr(0xE9)}\n")
        self.assertEqual(audit_text.audit_package(self.root)["matches"], 0)

    def test_named_wallet_test_string_is_allowed_only_in_its_file(self):
        self.write("wallet/test_wallet_epochs.py", f"for name in ('', 'ML/DSA', '{CJK}ASCII'):\n    pass\n")
        self.assertEqual(audit_text.audit_package(self.root)["authoredFiles"], 1)
        self.write("wallet/test_wallet_epochs.py", f"x = '{CJK}'\n")
        with self.assertRaisesRegex(audit_text.ForbiddenTextError, r"test_wallet_epochs\.py:1"):
            audit_text.audit_package(self.root)
        self.write("wallet/test_wallet_epochs.py", "x = 1\n")
        self.write("wallet/wallet.py", f"x = '{CJK}ASCII'\n")
        with self.assertRaisesRegex(audit_text.ForbiddenTextError, r"wallet\.py:1"):
            audit_text.audit_package(self.root)

    def test_binary_and_non_text_suffixes_are_skipped(self):
        (self.root / "demo/carrier.bin").write_bytes(bytes(range(256)))
        self.write("demo/notes.rst", CJK + "\n")
        self.assertEqual(audit_text.audit_package(self.root)["authoredFiles"], 0)

    def test_the_shipped_package_passes_the_full_audit(self):
        result = audit_text.audit_package(ROOT)
        self.assertEqual(result["matches"], 0)
        self.assertGreaterEqual(result["patches"], 5)
        self.assertGreater(result["authoredFiles"], 50)
        self.assertIn(SECTION, result["allowedNonASCII"])

    def test_command_line_patch_mode_reports_and_refuses(self):
        good = self.write("good.patch", patch_text([f"// {SECTION} clean"]))
        bad = self.write("bad.patch", patch_text(["// " + CORRUPTION]))
        tool = str(ROOT / "tools/audit_text.py")
        done = subprocess.run([sys.executable, "-B", tool, "--patch", str(good)], capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(json.loads(done.stdout)["status"], "PASS")
        done = subprocess.run([sys.executable, "-B", tool, "--patch", str(good), "--patch", str(bad)], capture_output=True, text=True)
        self.assertNotEqual(done.returncode, 0)
        self.assertIn("U+6402", done.stderr)


if __name__ == "__main__":
    unittest.main()
