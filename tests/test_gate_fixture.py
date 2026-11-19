"""The second public four-owner C fixture (four-owner-gates) matches its provenance record.

Hash and layout checks only: no native verification, no proving, no claim that the proof is
accepted beyond the recorded aggregate run.
"""
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "prover/aggregate/fixtures/four-owner-gates"
HEADER = bytes.fromhex("000480000008")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class GateFixtureTests(unittest.TestCase):
    def setUp(self):
        self.provenance = json.loads((FIXTURE / "PROVENANCE.json").read_text(encoding="utf-8"))
        self.statement = (FIXTURE / "statement.bin").read_bytes()
        self.pis = [self.statement[6 + i * 198:6 + (i + 1) * 198] for i in range(4)]

    def test_files_match_the_recorded_digests_and_sizes(self):
        self.assertTrue(self.provenance["publicTestOnly"])
        for name, row in self.provenance["files"].items():
            path = FIXTURE / name
            self.assertEqual(path.stat().st_size, row["bytes"], name)
            self.assertEqual(sha(path), row["sha256"], name)
        self.assertLessEqual((FIXTURE / "carrier.bin").stat().st_size, 196608)
        self.assertEqual(len(self.statement), 798)
        self.assertEqual(self.statement[:6], HEADER)

    def test_owners_inputs_and_records_agree_with_the_statement(self):
        owners = self.provenance["owners"]
        self.assertEqual(len(owners), 4)
        aggregate = json.loads((FIXTURE / self.provenance["records"]["aggregate"]).read_text(encoding="utf-8"))
        self.assertEqual(aggregate["status"], "PASS")
        self.assertEqual(aggregate["carrierSHA256"], self.provenance["files"]["carrier.bin"]["sha256"])
        self.assertEqual(aggregate["statementSHA256"], self.provenance["files"]["statement.bin"]["sha256"])
        for i, (owner, pi) in enumerate(zip(owners, self.pis)):
            self.assertEqual(owner["pi198SHA256"], hashlib.sha256(pi).hexdigest(), i)
            self.assertEqual(owner["legacyAddress"], "0x" + pi[64:84].hex(), i)
            self.assertEqual(owner["migrationNonce"], int.from_bytes(pi[84:92], "big"), i)
            self.assertEqual(owner["feeMode"], pi[169], i)
            self.assertEqual(owner["expiry"], int.from_bytes(pi[129:137], "big"), i)
            self.assertEqual(owner["feeSponsor"], "0x" + pi[170:190].hex(), i)
            inp = json.loads((FIXTURE / owner["input"]).read_text(encoding="utf-8"))
            self.assertTrue(inp["credential"]["public"])
            self.assertEqual(inp["path"], owner["path"])
            self.assertEqual(inp["pi"]["fee_mode"], owner["feeMode"])
            self.assertEqual(int(inp["pi"]["migration_nonce"]), owner["migrationNonce"])
            record = json.loads((FIXTURE / owner["record"]).read_text(encoding="utf-8"))
            self.assertEqual(record["status"], "PASS")
            self.assertTrue(record["publicTestOnly"])
            self.assertEqual(record["proofSHA256"], owner["fProofSHA256"])
            self.assertEqual(record["piSHA256"], owner["pi198SHA256"])
            self.assertEqual(aggregate["inputs"][i]["fSHA256"], owner["fProofSHA256"])
        # The gate layout the client test relies on.
        self.assertEqual([o["feeMode"] for o in owners], [2, 3, 1, 2])
        self.assertEqual([o["migrationNonce"] for o in owners], [0, 0, 0, 1])
        self.assertLess(owners[0]["expiry"] + 3600, owners[1]["expiry"])
        self.assertEqual({o["expiry"] for o in owners[1:]}, {owners[1]["expiry"]})
        self.assertEqual(owners[2]["feeSponsor"], "0x1c128b257dbe0311896a5e177f5d8db8cbdbd21b")
        self.assertEqual(len({o["legacyAddress"] for o in owners}), 4)


if __name__ == "__main__":
    unittest.main()
