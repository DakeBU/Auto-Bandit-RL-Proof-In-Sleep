#!/usr/bin/env python3
"""Dependency-free smoke tests for the ABRL local harness helper."""

from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BANDIT = ROOT / "tools" / "bandit.py"
LIFECYCLE = ROOT / "tools" / "abrl_lifecycle.py"


def load_bandit_module():
    spec = importlib.util.spec_from_file_location("bandit_under_test", BANDIT)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load tools/bandit.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_lifecycle_module():
    spec = importlib.util.spec_from_file_location("abrl_lifecycle_under_test", LIFECYCLE)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load tools/abrl_lifecycle.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class LifecycleFrontierTests(unittest.TestCase):
    def test_analyze_frontier_accepts_null_last_verifier(self) -> None:
        lifecycle = load_lifecycle_module()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runs = root / "runs"
            runs.mkdir()
            (runs / "active_frontier.json").write_text(
                json.dumps({
                    "current_leaf": {"id": "NEW-LEAF"},
                    "last_accepted_verifier": None,
                }),
                encoding="utf-8",
            )

            analysis = lifecycle.analyze_frontier(root)

            self.assertEqual(analysis["recorded_frontier"]["current_leaf"]["id"], "NEW-LEAF")
            self.assertNotIn(
                "missing_recorded_leaf",
                [mismatch["kind"] for mismatch in analysis["mismatches"]],
            )


class LongPathIoTests(unittest.TestCase):
    @unittest.skipUnless(sys.platform == "win32", "Win32 long-path regression")
    def test_read_write_text_supports_extended_repository_path(self) -> None:
        bandit = load_bandit_module()
        with tempfile.TemporaryDirectory() as tmp:
            try:
                path = (
                    Path(tmp)
                    / ("route-" + "a" * 90)
                    / ("leaf-" + "b" * 90)
                    / ("index-" + "c" * 90)
                    / "card.json"
                )
                self.assertGreater(len(str(path.resolve())), 260)

                bandit.write_text(path, "{\"status\": \"leanCompiled\"}\n")

                self.assertEqual(
                    bandit.read_text(path),
                    "{\"status\": \"leanCompiled\"}\n",
                )
            finally:
                shutil.rmtree(bandit.io_path(Path(tmp)), ignore_errors=True)


class ReviewStatusCliTests(unittest.TestCase):
    def run_bandit(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(BANDIT), *args],
            cwd=ROOT,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

    def test_review_status_json_contract(self) -> None:
        proc = self.run_bandit("review-status", "--json")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        payload = json.loads(proc.stdout)
        self.assertEqual(
            payload["boundary"],
            "ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES",
        )
        self.assertIsInstance(payload["responses"], list)
        self.assertIsInstance(payload["incomplete_responses"], list)
        self.assertIsInstance(payload["response_received"], bool)

    def test_require_response_matches_json_status(self) -> None:
        status_proc = self.run_bandit("review-status", "--json")
        payload = json.loads(status_proc.stdout)
        require_proc = self.run_bandit(
            "review-status",
            "--json",
            "--require-response",
        )
        if payload["response_received"]:
            self.assertEqual(require_proc.returncode, 0, require_proc.stdout)
        else:
            self.assertNotEqual(require_proc.returncode, 0, require_proc.stdout)

    def test_prompt_and_template_commands_print_expected_headers(self) -> None:
        prompt_proc = self.run_bandit("review-prompt")
        self.assertEqual(prompt_proc.returncode, 0, prompt_proc.stderr)
        self.assertIn(
            "Local Dual-Agent Review Prompt",
            prompt_proc.stdout,
        )

        template_proc = self.run_bandit("review-response-template")
        self.assertEqual(template_proc.returncode, 0, template_proc.stderr)
        self.assertIn("Save completed response as:", template_proc.stdout)

        handoff_proc = self.run_bandit("review-handoff")
        self.assertEqual(handoff_proc.returncode, 0, handoff_proc.stderr)
        self.assertIn("Local Dual-Agent Review Handoff", handoff_proc.stdout)

        legacy_prompt_proc = self.run_bandit("extended-pro-prompt")
        self.assertEqual(legacy_prompt_proc.returncode, 0, legacy_prompt_proc.stderr)
        self.assertIn("Extended Pro Review Prompt", legacy_prompt_proc.stdout)

    def test_search_memory_finds_route_roadmap_cards(self) -> None:
        route_proc = self.run_bandit("search-memory", "ROUTE-UCB1-FINITE-STOCHASTIC")
        self.assertEqual(route_proc.returncode, 0, route_proc.stderr)
        self.assertIn("route: ROUTE-UCB1-FINITE-STOCHASTIC", route_proc.stdout)

        spine_proc = self.run_bandit("search-memory", "SPINE-CONCENTRATION")
        self.assertEqual(spine_proc.returncode, 0, spine_proc.stderr)
        self.assertIn("spine: SPINE-CONCENTRATION", spine_proc.stdout)

    def test_unfinished_reads_current_lowercase_ledger_schema(self) -> None:
        proc = self.run_bandit("unfinished")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("unfinished leaf rows", proc.stdout)
        self.assertIn("no matching rows", proc.stdout)
        self.assertNotIn("[missing-leaf]", proc.stdout)
        self.assertNotIn("-  []", proc.stdout)
        self.assertNotIn("\ufffd", proc.stdout)

    def test_compact_lean_statement_preserves_result_let(self) -> None:
        bandit = load_bandit_module()
        statement = bandit.compact_lean_statement([
            "theorem example (n : Nat) :",
            "    let doubled := n + n",
            "    doubled = 2 * n := by",
            "  omega",
        ], 0)
        self.assertIn("let doubled := n + n", statement)
        self.assertTrue(statement.endswith("doubled = 2 * n"), statement)
        self.assertNotIn(":= by", statement)

    def test_compact_lean_statement_preserves_result_letI(self) -> None:
        bandit = load_bandit_module()
        statement = bandit.compact_lean_statement([
            "theorem example (witness : forall n, Nat) :",
            "    forall n,",
            "      letI :",
            "          OfNat Nat 0 :=",
            "        inferInstance",
            "      let value := witness n",
            "      value = witness n := by",
            "  intro n",
            "  rfl",
        ], 0)
        self.assertIn("letI : OfNat Nat 0 := inferInstance", statement)
        self.assertIn("let value := witness n", statement)
        self.assertTrue(statement.endswith("value = witness n"), statement)
        self.assertNotIn(":= by", statement)

    def test_compact_lean_statement_preserves_bracketed_result_let(self) -> None:
        bandit = load_bandit_module()
        statement = bandit.compact_lean_statement([
            "theorem example (n : Nat) :",
            "    True /\\",
            "      (forall i : Fin n,",
            "        let value := (i : Nat)",
            "        value = i) /\\",
            "      True := by",
            "  refine ⟨trivial, ?_, trivial⟩",
            "  intro i",
            "  rfl",
        ], 0)
        self.assertIn("let value := (i : Nat)", statement)
        self.assertTrue(statement.endswith("True /\\ (forall i : Fin n, let value := (i : Nat) value = i) /\\ True"), statement)
        self.assertNotIn(":= by", statement)
        self.assertNotIn("refine", statement)

    def test_list_lean_decls_preserves_full_all_windows_statement(self) -> None:
        proc = self.run_bandit(
            "list-lean-decls",
            "exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_"
            "decayingExplorationAverageRealizedBehaviorConsistency_allWindows",
            "--statement",
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("htrajectoryBorel n", proc.stdout)
        self.assertIn("violationSet ⊆ combinedBadEvent", proc.stdout)
        self.assertIn(
            "source.realizedSuccessorAverageRegret trajectory rounds <=",
            proc.stdout,
        )

    def test_compact_lean_statement_preserves_named_arguments(self) -> None:
        bandit = load_bandit_module()
        statement = bandit.compact_lean_statement([
            "theorem example {Feature : Type} (delta : Real) :",
            "    let regret := fun _trajectory => 0",
            "    mu {trajectory |",
            "        explicitBound (Feature := Feature) delta <",
            "          regret trajectory} <=",
            "      ENNReal.ofReal delta := by",
            "  exact tail",
        ], 0)
        self.assertIn("(Feature := Feature)", statement)
        self.assertTrue(
            statement.endswith("ENNReal.ofReal delta"),
            statement,
        )
        self.assertNotIn(":= by", statement)

    def test_compact_recursive_def_stops_before_omit_wrapped_theorem(self) -> None:
        bandit = load_bandit_module()
        statement = bandit.compact_lean_statement([
            "noncomputable def remainingGap : Nat -> Real",
            "  | 0 => 0",
            "  | n + 1 => remainingGap n + 1",
            "",
            "omit [Nonempty Action] in",
            "theorem remainingGap_nonneg (n : Nat) : 0 <= remainingGap n := by",
            "  omega",
        ], 0)
        self.assertIn("| n + 1 => remainingGap n + 1", statement)
        self.assertNotIn("omit", statement)
        self.assertNotIn("theorem", statement)

    def test_scan_lean_declarations_ignores_nested_block_comments(self) -> None:
        bandit = load_bandit_module()
        original_root = bandit.ROOT
        try:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                source_dir = root / "BanditRLProof"
                source_dir.mkdir()
                (source_dir / "Commented.lean").write_text(
                    "/-!\n"
                    "theorem fakeDoc : False := by contradiction\n"
                    "/- def fakeNested := 0 -/\n"
                    "-/\n"
                    "namespace Demo\n"
                    "def marker : String := \"-- /- not comments -/\"\n"
                    "/- inline comment -/ theorem actual : True := by\n"
                    "  trivial\n"
                    "end Demo\n",
                    encoding="utf-8",
                )
                bandit.ROOT = root

                declarations = bandit.scan_lean_declarations()
                names = [declaration["full_name"] for declaration in declarations]

                self.assertEqual(names, ["Demo.marker", "Demo.actual"])
        finally:
            bandit.ROOT = original_root

    def test_scan_lean_declarations_accepts_multiline_headers(self) -> None:
        bandit = load_bandit_module()
        original_root = bandit.ROOT
        try:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                source_dir = root / "BanditRLProof"
                source_dir.mkdir()
                (source_dir / "Multiline.lean").write_text(
                    "namespace Demo\n"
                    "noncomputable def\n"
                    "    longDefinition : Nat := 0\n"
                    "theorem\n"
                    "    longTheorem : True := by\n"
                    "  trivial\n"
                    "end Demo\n",
                    encoding="utf-8",
                )
                bandit.ROOT = root

                declarations = bandit.scan_lean_declarations()
                summary = [
                    (
                        declaration["kind"],
                        declaration["full_name"],
                        declaration["line"],
                    )
                    for declaration in declarations
                ]

                self.assertEqual(summary, [
                    ("def", "Demo.longDefinition", 2),
                    ("theorem", "Demo.longTheorem", 4),
                ])
        finally:
            bandit.ROOT = original_root

    def test_scan_lean_declarations_qualifies_dotted_relative_names(self) -> None:
        bandit = load_bandit_module()
        original_root = bandit.ROOT
        try:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                source_dir = root / "BanditRLProof"
                source_dir.mkdir()
                (source_dir / "RelativeDotted.lean").write_text(
                    "namespace BanditRLProof\n"
                    "namespace DelayedFeedback\n"
                    "structure View where\n"
                    "  marker : Nat\n"
                    "theorem View.ext (left right : View) "
                    "(h : left.marker = right.marker) : left = right := by\n"
                    "  cases left\n"
                    "  cases right\n"
                    "  simp_all\n"
                    "end DelayedFeedback\n"
                    "end BanditRLProof\n",
                    encoding="utf-8",
                )
                bandit.ROOT = root

                declarations = bandit.scan_lean_declarations()
                names = [declaration["full_name"] for declaration in declarations]

                self.assertEqual(names, [
                    "BanditRLProof.DelayedFeedback.View",
                    "BanditRLProof.DelayedFeedback.View.ext",
                ])
        finally:
            bandit.ROOT = original_root

    def test_run_cycle_review_gate_stops_when_response_missing(self) -> None:
        status_proc = self.run_bandit("review-status", "--json")
        payload = json.loads(status_proc.stdout)
        if payload["response_received"]:
            self.skipTest("review response already recorded")

        task_id = "__REVIEW_GATE_TEST__"
        runs_dir = ROOT / "runs"
        before = set(runs_dir.glob(f"*-{task_id}-cycle01")) if runs_dir.exists() else set()
        proc = self.run_bandit("run-cycle", task_id, "--require-review-response")
        after = set(runs_dir.glob(f"*-{task_id}-cycle01")) if runs_dir.exists() else set()

        self.assertNotEqual(proc.returncode, 0, proc.stdout)
        self.assertEqual(before, after)
        self.assertIn("Response: missing", proc.stdout)

    def test_record_response_writes_completed_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            raw = tmp_path / "raw_response.md"
            output = tmp_path / "local_dual_review_test.md"
            raw.write_text(
                "Local dual-agent review chooses Candidate A and recommends "
                "the concrete argmax route card as the next single "
                "theorem-card-only step, with explicit failure policy.",
                encoding="utf-8",
            )
            proc = self.run_bandit(
                "review-record-response",
                "--raw",
                str(raw),
                "--output",
                str(output),
                "--chosen-leaf",
                "Candidate A",
                "--classification",
                "theorem-card-only",
            )
            self.assertEqual(proc.returncode, 0, proc.stderr + proc.stdout)
            text = output.read_text(encoding="utf-8")
            self.assertIn("Chosen next leaf: Candidate A", text)
            self.assertIn("## Raw Local Dual-Agent Review", text)
            self.assertIn("concrete argmax route card", text)

            bandit = load_bandit_module()
            self.assertTrue(bandit.is_completed_review_response(output))

    def test_record_response_rejects_short_raw_text(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            raw = tmp_path / "raw_response.md"
            output = tmp_path / "response.md"
            raw.write_text("too short", encoding="utf-8")
            proc = self.run_bandit(
                "extended-pro-record-response",
                "--raw",
                str(raw),
                "--output",
                str(output),
            )
            self.assertNotEqual(proc.returncode, 0, proc.stdout)
            self.assertFalse(output.exists())


class ReviewResponseDetectionTests(unittest.TestCase):
    def test_read_snapshot_keeps_complete_head_and_tail_lines(self) -> None:
        bandit = load_bandit_module()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "snapshot.md"
            lines = [f"row-{i:03d}" for i in range(200)]
            path.write_text("\n".join(lines) + "\n", encoding="utf-8")

            snapshot = bandit.read_snapshot(path, 240)

            self.assertTrue(snapshot.startswith("row-000\n"))
            self.assertTrue(snapshot.endswith("row-199\n"))
            self.assertIn("characters omitted from the middle", snapshot)
            for line in snapshot.splitlines():
                if line and not line.startswith("<!--"):
                    self.assertIn(line, lines)

    def test_response_detection_ignores_prompts_pending_and_templates(self) -> None:
        bandit = load_bandit_module()
        original_root = bandit.ROOT
        try:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                reports = root / "reports"
                reports.mkdir()
                stem = "extended_pro_after_phase_split_bound"

                ignored_names = [
                    f"{stem}_prompt_2026-06-29.md",
                    f"{stem}_candidate_prompt_2026-06-29.md",
                    f"{stem}_retry_pending_2026-06-29.md",
                    f"{stem}_response_template_2026-06-29.md",
                    f"{stem}_manual_handoff_2026-06-30.md",
                    f"{stem}_handoff_2026-06-30.md",
                ]
                for name in ignored_names:
                    (reports / name).write_text("ignored\n", encoding="utf-8")

                incomplete = reports / f"{stem}_2026-06-29.md"
                incomplete.write_text(
                    "## Raw Extended Pro Response\n"
                    "Paste the complete Extended Pro answer here.\n",
                    encoding="utf-8",
                )

                complete = reports / f"{stem}_manual_2026-06-29.md"
                complete.write_text(
                    "## Raw Extended Pro Response\n"
                    "Extended Pro chose Candidate B and provided a complete "
                    "single-leaf proof route with contracts, imports, "
                    "classification, and failure policy.\n",
                    encoding="utf-8",
                )

                bandit.ROOT = root

                response_files = bandit.extended_pro_response_files(stem)
                self.assertEqual(
                    [path.name for path in response_files],
                    [incomplete.name, complete.name],
                )
                self.assertEqual(
                    [path.name for path in bandit.extended_pro_response_candidates(stem)],
                    [complete.name],
                )
                self.assertEqual(
                    [
                        path.name
                        for path in bandit.incomplete_extended_pro_response_candidates(stem)
                    ],
                    [incomplete.name],
                )
        finally:
            bandit.ROOT = original_root


if __name__ == "__main__":
    unittest.main()
