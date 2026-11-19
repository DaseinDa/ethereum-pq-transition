"""Tests that tie the formal run of record to the shipped model, without Java or Apalache.

They check that the module, the runner and the mutation script are the research copies (SHA-256 with
CR stripped), that the record names that module, that each of the six mutation controls changes
exactly one place of the module, and that the record lists the 13 jobs of the runner and of the
mutation script, all as expected, each with a log that names its initial predicate, its invariant
and its verdict.
"""
import ast
import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "formal" / "account-inductive"
RECORD = MODEL / "record-20261110"
# Byte copies of research 20d599e9 (code/formal-model-20261027/account-inductive/), SHA-256 with CR stripped.
PINNED = {
    "AccountInductive.tla": "aa1df41d80bcd9caeffa597d30eb23d99778bf279cd907fc63c421e95ee3e7d1",
    "run_apalache.sh": "0820982ead1f569d87a90d0e2c92115187e67a7dbe755cc9eb6fd14400f7e2c2",
    "mutation_check.py": "2a3bde789af173afe4132184367b43f460c20864653444ccf289bb2b5b6eba33",
}
RUN_LINE = re.compile(r"^run (\w+) +(holds|violated) +--init=(\w+) +--inv=(\w+) +--length=(\d+)$", re.M)


def source(name):
    return (MODEL / name).read_bytes().replace(b"\r", b"").decode("utf-8")


def mutation_table():
    tree = ast.parse(source("mutation_check.py"))
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(getattr(t, "id", None) == "MUTATIONS" for t in node.targets):
            return ast.literal_eval(node.value)
    raise AssertionError("mutation_check.py defines no MUTATIONS table")


def expected_jobs():
    """(name, expected, init, invariant, length, mutation text) for every job, in the record's order."""
    jobs = [(n, e, i, v, int(k), None) for n, e, i, v, k in RUN_LINE.findall(source("run_apalache.sh"))]
    jobs += [(row[0], "violated", "IndInit", "IndInvAndProps", 1, row[3]) for row in mutation_table()]
    return jobs


def summary():
    return json.loads((RECORD / "summary.json").read_text(encoding="utf-8"))


class FormalRecordTests(unittest.TestCase):
    def test_sources_are_the_pinned_research_copies(self):
        for name, digest in PINNED.items():
            with self.subTest(file=name):
                self.assertEqual(hashlib.sha256(source(name).encode("utf-8")).hexdigest(), digest)

    def test_record_names_the_shipped_module(self):
        digest = PINNED["AccountInductive.tla"]
        self.assertEqual(summary()["module_sha256_cr_stripped"], digest)
        self.assertEqual(summary()["recorded_module_sha256"], digest)
        self.assertIn("module sha256: " + digest + " (CR stripped)", (RECORD / "summary.txt").read_text(encoding="utf-8"))

    def test_each_mutation_changes_exactly_one_place(self):
        module = source("AccountInductive.tla")
        table = mutation_table()
        self.assertEqual(len(table), 6)
        for name, old, new, _rule in table:
            with self.subTest(mutation=name):
                self.assertEqual(module.count(old), 1)
                self.assertNotEqual(module.replace(old, new), module)

    def test_record_holds_every_job_as_expected_with_its_log(self):
        record = summary()
        jobs = expected_jobs()
        self.assertEqual(len(jobs), 13)
        self.assertEqual([job["name"] for job in record["jobs"]], [job[0] for job in jobs])
        self.assertTrue(record["all_as_expected"])
        self.assertEqual(record["counts"], {"checks": 2, "scenarios": 5, "mutations": 6})
        for job, (name, expected, init, invariant, length, mutation) in zip(record["jobs"], jobs):
            with self.subTest(job=name):
                self.assertEqual((job["expected"], job["outcome"], job["as_expected"]), (expected, expected, True))
                self.assertEqual(job["what"], mutation)
                log = (RECORD / "logs" / (name + ".txt")).read_text(encoding="utf-8")
                self.assertEqual(re.findall(r"Set the initialization predicate to (\w+)", log), [init])
                self.assertEqual(re.findall(r"Set an invariant to (\w+)", log), [invariant])
                if mutation is not None:
                    self.assertTrue(log.startswith("mutation: " + mutation + "\n"))
                if expected == "holds":
                    self.assertIn("The outcome is: NoError", log)
                    self.assertIn("Checker reports no error up to computation length %d" % length, log)
                else:
                    self.assertIn("The outcome is: Error", log)
                    self.assertEqual(re.findall(r"^State (\d+): state invariant \d+ violated\.", log, re.M), [str(length)])


if __name__ == "__main__":
    unittest.main()
