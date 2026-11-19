"""Offline artifact-integrity tests with small synthetic wheel fixtures."""
import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve()
TOOL = HERE.parents[2] / "n1_dependencies.py"
if not TOOL.exists():
    TOOL = HERE.parents[3] / "tools/n1_dependencies.py"
spec = importlib.util.spec_from_file_location("n1_dependencies", TOOL)
dependencies = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dependencies)


class DependenciesTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.wheels = self.root / "input"
        self.wheels.mkdir()
        self.wheel = self.wheels / "fixture-1.0-py3-none-any.whl"
        self.wheel.write_bytes(b"small fixture: no installation performed")
        self.inventory = self.root / "inventory.json"
        self.inventory.write_text(json.dumps({"packages": {"fixture": {"version": "1.0", "wheels": {
            self.wheel.name: {"sha256": dependencies.sha(self.wheel), "bytes": self.wheel.stat().st_size}}}}}))
        self.bundle = self.root / "bundle"

    def test_roundtrip_and_tampering(self):
        digest = dependencies.collect(self.wheels, self.bundle, self.inventory)
        dependencies.verify(self.bundle, digest, self.inventory)
        (self.bundle / "wheels" / self.wheel.name).write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "content mismatch"):
            dependencies.verify(self.bundle, digest, self.inventory)

    def test_manifest_cannot_bless_changed_wheel(self):
        dependencies.collect(self.wheels, self.bundle, self.inventory)
        path = self.bundle / "wheels" / self.wheel.name
        path.write_bytes(b"changed")
        manifest_path = self.bundle / "MANIFEST.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["files"]["wheels/" + self.wheel.name] = {"sha256": dependencies.sha(path), "bytes": path.stat().st_size}
        manifest_path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "changed or duplicate"):
            dependencies.verify(self.bundle, dependencies.sha(manifest_path), self.inventory)

    def test_unapproved_and_missing_wheels_refused_before_output(self):
        self.wheel.unlink()
        with self.assertRaisesRegex(ValueError, "incomplete"):
            dependencies.collect(self.wheels, self.bundle, self.inventory)
        self.assertFalse(self.bundle.exists())
        self.wheel.write_bytes(b"unapproved content")
        with self.assertRaisesRegex(ValueError, "differs"):
            dependencies.collect(self.wheels, self.bundle, self.inventory)
        self.assertFalse(self.bundle.exists())

    def test_untrusted_digest_and_escaping_manifest_refused(self):
        digest = dependencies.collect(self.wheels, self.bundle, self.inventory)
        with self.assertRaisesRegex(ValueError, "digest mismatch"):
            dependencies.verify(self.bundle, "0" * 64, self.inventory)
        manifest_path = self.bundle / "MANIFEST.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["files"]["../outside"] = {"sha256": "0" * 64, "bytes": 0}
        manifest_path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "unsafe"):
            dependencies.verify(self.bundle, dependencies.sha(manifest_path), self.inventory)


if __name__ == "__main__":
    unittest.main()
