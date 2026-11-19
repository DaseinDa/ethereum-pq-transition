"""Switch orchestration/report regressions; no native programs or real waits."""
import contextlib
import io
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
try:
    import switch
except ModuleNotFoundError as exc:
    if exc.name.split(".")[0] not in {"eth_hash", "py_ecc", "Crypto", "eth_typing", "eth_utils", "cytoolz", "pydantic", "typing_extensions"}:
        raise
    raise unittest.SkipTest("requires the pinned N1 Python environment: " + str(exc))


class SwitchReportTests(unittest.TestCase):
    def make(self):
        run = switch.Switch.__new__(switch.Switch)
        run.rec = {"checks": {}}
        run.a = SimpleNamespace(recovery_proof=None, silent_slots=0)
        run.save = lambda: None
        return run

    def test_missing_proof_and_disabled_silence_are_explicit_not_run(self):
        run = self.make()
        with patch.object(switch, "verify_native", side_effect=AssertionError("must not call native")):
            run.load_proof({})
            run.late_path()
            run.x_silent()
        tests = run.tests()
        self.assertEqual(tests["T8"]["status"], "NOT RUN")
        self.assertIn("--recovery-proof", tests["T8"]["notRun"])
        self.assertEqual(tests["T6b"]["status"], "NOT RUN")
        self.assertIn("--silent-slots=0", tests["T6b"]["notRun"])
        self.assertIn("no CL exit", tests["T8"]["scope"])

    def test_partial_scenario_cannot_report_pass(self):
        run = self.make()
        run.rec["scenarioTimings"] = {"T8": {"startedUnix": 10}}
        run.rec["checks"] = {"T8.recoveryAfterT": {"pass": True, "unix": 11}}
        self.assertEqual(run.tests()["T8"]["status"], "FAIL")
        run.rec["scenarioTimings"]["T8"]["finishedUnix"] = 20
        self.assertEqual(run.tests()["T8"]["status"], "FAIL")
        for name in ("T8.activation", "T8.eip7002RequestLogRequestsHashSource", "T7.migrationAfterSIncludedAndFinalized"):
            run.rec["checks"][name] = {"pass": True, "unix": 19}
        result = run.tests()["T8"]
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["timing"]["seconds"], 10)
        self.assertEqual(result["checkObservations"]["spanSeconds"], 8)
        run.rec["checks"]["T7.migrationAfterSIncludedAndFinalized"]["pass"] = False
        self.assertEqual(run.tests()["T8"]["status"], "FAIL")

    def test_requested_late_path_cannot_complete_when_missing_or_partial(self):
        run = self.make()
        run.a.recovery_proof = Path("requested-proof")
        run.rec["processesStopped"] = True
        run.rec["tests"] = run.tests()
        self.assertFalse(run.passed())
        run.rec["scenarioTimings"] = {"T8": {"startedUnix": 10}}
        run.rec["checks"] = {"T8.recoveryAfterT": {"pass": True, "unix": 11}}
        run.rec["tests"] = run.tests()
        self.assertFalse(run.passed())

    def test_worker_close_failure_preserves_final_result_and_stops_worker(self):
        run = self.make()
        stops = []
        run.lab = SimpleNamespace(nodes={}, stop_all=lambda: True, stop=lambda proc: stops.append(proc))
        def close():
            raise RuntimeError("worker failed")
        run.cr = SimpleNamespace(close=close, proc="worker")
        run.scan_logs = lambda: {}
        run.finish()
        self.assertEqual(stops, ["worker"])
        self.assertIn("worker failed", run.rec["cryptoCloseError"])
        self.assertIn("tests", run.rec)
        self.assertFalse(run.passed())

    def test_submission_race_accepts_only_verified_identical_already_known(self):
        expected = "0x" + "ab" * 32
        for error, returned, accepted in (("already known", expected, True),
                                          ("already known", "0x" + "cd" * 32, False),
                                          ("nonce too low", expected, False)):
            with self.subTest(error=error, returned=returned):
                run = self.make()
                run.cr = lambda operation, raw: bytes.fromhex("ab" * 32)
                run.url = lambda name: name
                calls = []
                def rpc(node, method, params):
                    calls.append((node, method, params))
                    return {"hash": returned}
                run.rpc = rpc
                responses = [{"result": expected}, {"error": {"code": -32000, "message": error}}]
                with patch.object(switch.L, "rpc_raw", side_effect=responses):
                    if accepted:
                        self.assertEqual(run.raw_send("test", b"raw"), expected)
                    else:
                        with self.assertRaisesRegex(ValueError, "submission refused"):
                            run.raw_send("test", b"raw")
                self.assertEqual(len(calls), 1 if error == "already known" else 0)

    def test_silent_window_starts_after_shutdown_and_requires_absent_x_slot(self):
        for x_proposal in (False, True):
            with self.subTest(x_proposal=x_proposal), tempfile.TemporaryDirectory() as directory:
                run = self.make()
                run.out = Path(directory)
                (run.out / "H-ream-1.log").write_text("")
                run.a.silent_slots = 10
                run.S = 1000
                clock = [1120.0]
                stopped = []
                def stop(name):
                    stopped.append(name)
                    clock[0] += 1
                    return (1, 0)
                def rest(name, path):
                    self.assertEqual(name, "H")
                    return {"slot": 9 if not stopped else (17 if path == "blocks/finalized" else 18)}
                run.lab = SimpleNamespace(stop_ream=stop, rest=rest)
                slots = list(range(10, 19))
                if not x_proposal:
                    slots.remove(13)
                blocks = [{"number": i + 1, "timestamp": run.S + slot * 12} for i, slot in enumerate(slots)]
                run.block = lambda name, number: blocks[number - 1] if number > 0 else None
                run.tag = lambda name, tag: blocks[-1] if tag == "latest" else {"number": 2 if not stopped else 8}
                run.dump = lambda name, obj: None
                def sleep(seconds):
                    clock[0] += seconds
                with patch.object(switch.time, "time", side_effect=lambda: clock[0]), \
                        patch.object(switch.time, "sleep", side_effect=sleep), contextlib.redirect_stdout(io.StringIO()):
                    run.x_silent()
                self.assertEqual(stopped, ["X"])
                check = run.rec["checks"]["T6b.sixOfSevenFinalizeWithXSilent"]
                self.assertEqual(check["firstSlotAfterStop"], 11)
                self.assertEqual(check["missedXSlots"], [13])
                self.assertEqual(check["pass"], not x_proposal)
                self.assertEqual(run.tests()["T6b"]["status"], "FAIL" if x_proposal else "PASS")


if __name__ == "__main__":
    unittest.main()
