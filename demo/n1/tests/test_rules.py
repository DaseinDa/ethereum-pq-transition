"""Fast policy regressions; no client, network, keys or third-party packages."""
import copy
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from rules import execution_invariants, resolve_registrations, switch_timeline


def registration(seq, index, label, reason=None):
    return {"seq": seq, "index": index, "valid": reason is None, "reason": reason,
            "reasons": [] if reason is None else [reason],
            "message": {"lean_attestation_pubkey": label + "-att", "lean_proposal_pubkey": label + "-prop"}}


class RulesTests(unittest.TestCase):
    def test_common_deadline_and_preparation_window(self):
        timing = switch_timeline(1000, 22, 180, 240, 65)
        self.assertEqual((timing["S"], timing["T0"], timing["dReg"]), (1444, 1444, 1444))
        self.assertEqual(timing["halt"], 1264)
        self.assertEqual(timing["T"] - timing["T0"], 240)
        for args in ((0, 17, 180, 240, 65), (0, 22, 94, 240, 65), (0, 22, 180, 0, 65),
                     (2**64 - 1, 22, 180, 240, 65), (-1, 22, 180, 240, 65)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                switch_timeline(*args)

    def test_seven_of_ten_with_conflicts_invalid_and_duplicate(self):
        snapshot = {i: {"withdrawalCredentials": "0x" + ("00" if i == 9 else "01") + "00" * 31}
                    for i in range(10)}
        plan = [(i, "H" + str(i), None) for i in range(6)] + [
            (5, "H5", None), (5, "A5x", "bls-invalid"), (6, "A6", None),
            (7, "A7", None), (7, "H7", None), (8, "H8", None), (8, "A8", None),
            (9, "A9x", "bls-invalid"), (9, "H9", "withdrawal-credentials")]
        regs = [registration(seq, *row) for seq, row in enumerate(plan)]
        for rows in (regs, list(reversed(regs))):
            results, included, unknown = resolve_registrations(snapshot, rows)
            self.assertEqual([r["index"] for r in included], list(range(7)))
            self.assertEqual({r["index"]: r["reason"] for r in results if r["result"] == "excluded"},
                             {7: "conflict", 8: "conflict", 9: "withdrawal-credentials-0x00"})
            self.assertEqual(sum(r["attestation"].startswith("A") for r in included), 1)
            self.assertEqual(len(included[5]["valid"]), 2)
            self.assertEqual(unknown, [])

    def test_invalid_unknown_and_missed_do_not_create_conflict(self):
        snapshot = {0: {"withdrawalCredentials": "0x01" + "00" * 31}, 1: {"withdrawalCredentials": "0x01" + "00" * 31}}
        regs = [registration(0, 0, "H0"), registration(1, 0, "A0", "bls-invalid"),
                registration(2, 99, "A99", "unknown-index")]
        results, included, unknown = resolve_registrations(snapshot, regs)
        self.assertEqual([r["index"] for r in included], [0])
        self.assertEqual(results[1]["reason"], "missed")
        self.assertEqual(unknown, [2])

    def test_credential_exclusion_comes_from_snapshot_even_if_registration_missing_or_invalid(self):
        snapshot = {0: {"withdrawalCredentials": "0x01" + "00" * 31},
                    1: {"withdrawalCredentials": "0x00" + "00" * 31}}
        invalid = registration(1, 1, "H1", "lean-interval")
        invalid["reasons"].append("withdrawal-credentials")
        for rows in ([registration(0, 0, "H0")], [registration(0, 0, "H0"), invalid]):
            with self.subTest(rows=len(rows)):
                results, included, unknown = resolve_registrations(snapshot, rows)
                self.assertEqual([r["index"] for r in included], [0])
                self.assertEqual(results[1]["reason"], "withdrawal-credentials-0x00")
                self.assertEqual(unknown, [])

    def test_execution_state_preserved_while_heads_advance(self):
        before = {"gethBinarySHA256": "binary", "elGenesisFileSHA256": "genesis", "genesisBlock": {"H": "g", "X": "g"},
                  "gethPids": {"H": 10, "X": 11}, "gethAlive": {"H": True, "X": True},
                  "bckBlock": {"H": "bck", "X": "bck"}, "balancesAtBck": {"owner": 50},
                  "registrySlots0to2": {node: {"atBck": [100, "acc", 15], "latest": [100, "acc", 15]} for node in ("H", "X")},
                  "heads": {"latest": "old"}}
        after = copy.deepcopy(before)
        after["heads"]["latest"] = "new"
        self.assertTrue(all(execution_invariants(before, after).values()))
        for field in ("gethBinarySHA256", "elGenesisFileSHA256", "genesisBlock", "gethPids", "bckBlock", "balancesAtBck"):
            changed = copy.deepcopy(after)
            changed[field] = "changed"
            with self.subTest(field=field):
                self.assertFalse(execution_invariants(before, changed)[field])
        after["registrySlots0to2"]["H"]["latest"][2] += 1
        self.assertFalse(execution_invariants(before, after)["registry"])
        after["gethAlive"]["X"] = False
        self.assertFalse(execution_invariants(before, after)["clientsAlive"])


if __name__ == "__main__":
    unittest.main()
