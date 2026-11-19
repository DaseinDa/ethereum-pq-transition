"""Small schedule and canonical-evidence tests; no clients or native crypto run."""
import copy
import hashlib
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "demo/runtime"))
from request_boundary import REQUEST_TARGETS, boundary_schedule, check_boundary_pair, request_hash


class RequestDeadlineTests(unittest.TestCase):
    def setUp(self):
        self.genesis, self.fork, self.window = 1000, 1180, 612
        self.deadline = self.fork + self.window
        self.source = "0x" + "45" * 20
        self.payloads = {"7002": b"\x42" * 48 + bytes(8), "7251": b"\x42" * 96}

    def evidence(self, phase):
        accepted = phase != "before"
        receipts = {}
        bodies = {}
        for kind in REQUEST_TARGETS:
            body = bytes.fromhex(self.source[2:]) + self.payloads[kind]
            receipts[kind] = {"status": "0x1" if accepted else "0x0", "blockHash": "0xabc",
                              "logs": [{"address": REQUEST_TARGETS[kind], "data": "0x" + body.hex()}] if accepted else []}
            if accepted:
                bodies[kind] = body
        # Expected hash assembled independently from the two request-type digests.
        outer = hashlib.sha256()
        if accepted:
            outer.update(hashlib.sha256(b"\x01" + bodies["7002"]).digest())
            outer.update(hashlib.sha256(b"\x02" + bodies["7251"]).digest())
        block = {"hash": "0xabc", "requestsHash": "0x" + outer.hexdigest()}
        return receipts, block

    def test_schedule_hits_before_at_and_after_actual_a_proposals(self):
        schedule = boundary_schedule(self.genesis, self.fork, self.window)
        self.assertEqual(schedule, [("before", 1756, 0), ("at", 1792, 1), ("after", 1828, 1)])
        self.assertTrue(all((timestamp - self.genesis) % 36 == 0 for _, timestamp, _ in schedule))
        for args in [(1000, 1180, 600), (1000, 1180, 613), (1000, 1181, 612)]:
            with self.assertRaises(ValueError):
                boundary_schedule(*args)

    def test_all_three_canonical_pairs_checked(self):
        for phase, timestamp, status in boundary_schedule(self.genesis, self.fork, self.window):
            with self.subTest(phase=phase):
                receipts, block = self.evidence(phase)
                row = check_boundary_pair(phase, self.deadline, timestamp, receipts, block, self.source, self.payloads)
                self.assertEqual(row["expectedStatus"], status)
                self.assertEqual(row["canonicalTimestamp"], timestamp)

    def test_missed_exact_boundary_never_counts_as_success(self):
        receipts, block = self.evidence("at")
        for timestamp in (self.deadline - 1, self.deadline + 1, self.deadline + 12, self.deadline + 36):
            with self.assertRaisesRegex(ValueError, "missed"):
                check_boundary_pair("at", self.deadline, timestamp, receipts, block, self.source, self.payloads)

    def test_different_blocks_status_or_missing_contract_fail(self):
        receipts, block = self.evidence("at")
        variants = []
        altered = copy.deepcopy(receipts); altered["7251"]["blockHash"] = "0xdef"; variants.append(altered)
        altered = copy.deepcopy(receipts); altered["7251"]["status"] = "0x0"; variants.append(altered)
        variants.append({"7002": receipts["7002"]})
        for altered in variants:
            with self.assertRaises(ValueError):
                check_boundary_pair("at", self.deadline, self.deadline, altered, block, self.source, self.payloads)

    def test_queue_side_effects_and_wrong_sources_fail(self):
        receipts, block = self.evidence("before")
        receipts["7002"]["logs"] = self.evidence("at")[0]["7002"]["logs"]
        with self.assertRaisesRegex(ValueError, "blocked"):
            check_boundary_pair("before", self.deadline, self.deadline - 36, receipts, block, self.source, self.payloads)
        receipts, block = self.evidence("at")
        with self.assertRaisesRegex(ValueError, "source"):
            check_boundary_pair("at", self.deadline, self.deadline, receipts, block, "0x" + "46" * 20, self.payloads)

    def test_combined_hash_and_type_order_required(self):
        receipts, block = self.evidence("at")
        body = bytes.fromhex(receipts["7002"]["logs"][0]["data"][2:])
        block["requestsHash"] = request_hash({"7002": body})
        with self.assertRaisesRegex(ValueError, "combined"):
            check_boundary_pair("at", self.deadline, self.deadline, receipts, block, self.source, self.payloads)
        self.assertEqual(request_hash({}), "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
        self.assertEqual(request_hash({"7002": b"a", "7251": b"b"}), request_hash({"7251": b"b", "7002": b"a"}))


if __name__ == "__main__":
    unittest.main()
