import tempfile
import unittest
from pathlib import Path

from tools import build_sgb_interface_frontier_trace as TRACE


class SgbInterfaceFrontierTraceTests(unittest.TestCase):
    def test_committed_trace_is_reproducible_and_conservative(self):
        trace = TRACE.build_trace("HEAD")
        summary = trace["frontier_summary"]
        self.assertEqual(8, summary["state_count"])
        self.assertEqual(7, summary["dependency_ordered_closure_count"])
        self.assertEqual(6, summary["statement_fence_count"])
        self.assertFalse(summary["theorem_two_endpoint_verified"])
        self.assertEqual(
            TRACE.EXPECTED_TARGET_SHA256,
            trace["target_freeze"]["sha256"],
        )
        self.assertEqual(
            "SGB-T2-NATIVE-PREFIX-IDENTIFICATION",
            summary["initial_interface"],
        )
        self.assertEqual(
            "SGB-T2-APPENDIX-C-PHASE-TRIGGER",
            summary["current_interface"],
        )
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            json_path = root / "trace.json"
            csv_path = root / "trace.csv"
            TRACE.compare_or_write(json_path, TRACE.json_bytes(trace), False)
            TRACE.compare_or_write(csv_path, TRACE.csv_bytes(trace), False)
            self.assertEqual(TRACE.DEFAULT_JSON.read_bytes(), json_path.read_bytes())
            self.assertEqual(TRACE.DEFAULT_CSV.read_bytes(), csv_path.read_bytes())


if __name__ == "__main__":
    unittest.main()
