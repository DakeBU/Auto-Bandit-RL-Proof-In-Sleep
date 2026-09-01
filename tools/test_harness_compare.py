#!/usr/bin/env python3
"""Regression tests for evidence-bounded harness comparison."""

from __future__ import annotations

import sys
import tempfile
import threading
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import harness_compare
import bandit


def row(
    experiment: str,
    harness: str,
    progress: str,
    *,
    status: str = "accepted",
    reviewed: bool = True,
    elapsed: float = 10.0,
) -> dict[str, object]:
    return {
        "task": "TASK",
        "experiment_id": experiment,
        "target_fingerprint": "same-target",
        "harness": harness,
        "run_id": f"{experiment}-{harness}",
        "attempt_id": f"{experiment}-{harness}-attempt",
        "role": "worker" if harness == "master-worker" else "lower",
        "progress_class": progress,
        "status": status,
        "reviewer_validated": reviewed,
        "verifier_evidence": ["lake build"],
        "obligations_before": 2,
        "obligations_after": 1 if progress != "no-progress" else 2,
        "elapsed_seconds": elapsed,
    }


class HarnessComparisonTests(unittest.TestCase):
    def test_historical_unstructured_rows_cannot_choose_a_winner(self) -> None:
        analysis = harness_compare.analyze_trials(
            [{"task": "TASK", "role": "lower", "status": "compiled"}],
            task="TASK",
        )
        self.assertEqual(analysis["eligible_rows"], 0)
        self.assertEqual(analysis["decision"]["status"], "insufficient-evidence")
        self.assertEqual(
            analysis["decision"]["recommended_default"],
            "retain-current-default",
        )

    def test_two_matched_experiments_can_support_master_worker(self) -> None:
        rows = []
        for experiment in ("ab-01", "ab-02"):
            rows.extend(
                [
                    row(experiment, "hierarchical", "diagnostic"),
                    row(experiment, "master-worker", "compiled-leaf"),
                ]
            )
        analysis = harness_compare.analyze_trials(rows, task="TASK")
        self.assertEqual(analysis["matched_experiments"], ["ab-01", "ab-02"])
        self.assertEqual(analysis["decision"]["status"], "measured")
        self.assertEqual(analysis["decision"]["recommended_default"], "master-worker")

    def test_exit_zero_without_review_is_not_substantive(self) -> None:
        unreviewed = row(
            "ab-01",
            "master-worker",
            "compiled-leaf",
            status="executed",
            reviewed=False,
        )
        summary = harness_compare.summarize_arm([unreviewed], "master-worker")
        self.assertEqual(summary["attempts"], 1)
        self.assertEqual(summary["reviewed_attempts"], 0)
        self.assertEqual(summary["substantive_score"], 0.0)

    def test_mermaid_exposes_both_internal_routes(self) -> None:
        rows = [
            row("ab-01", "hierarchical", "diagnostic"),
            row("ab-01", "master-worker", "compiled-leaf"),
        ]
        analysis = harness_compare.analyze_trials(rows, task="TASK")
        mermaid = harness_compare.render_mermaid(rows, analysis)
        self.assertIn("Hierarchical", mermaid)
        self.assertIn("Master–worker", mermaid)
        self.assertIn("compiled-leaf", mermaid)

    def test_gpt_packet_preserves_insufficient_evidence_boundary(self) -> None:
        rows = [
            row("ab-01", "hierarchical", "diagnostic"),
            row("ab-01", "master-worker", "compiled-leaf"),
        ]
        analysis = harness_compare.analyze_trials(rows, task="TASK")
        packet = harness_compare.render_review_prompt(rows, analysis)
        self.assertIn("insufficient-evidence", packet)
        self.assertIn("Do not infer a winner", packet)

    def test_master_worker_executor_overlaps_worker_phase(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            run_dir = Path(temporary)
            prompts = [
                run_dir / "10_master_plan.md",
                run_dir / "30_worker_1.md",
                run_dir / "30_worker_2.md",
                run_dir / "40_master_synthesis.md",
                run_dir / "50_reviewer.md",
            ]
            for prompt in prompts:
                prompt.write_text("test\n", encoding="utf-8")
            barrier = threading.Barrier(2)
            worker_threads: list[int] = []
            original = bandit.execute_prompt

            def fake_execute(_template, prompt, *_args, **_kwargs):
                if prompt.name.startswith("30_worker"):
                    worker_threads.append(threading.get_ident())
                    barrier.wait(timeout=2)
                return 0

            bandit.execute_prompt = fake_execute
            try:
                code = bandit.execute_master_worker_prompt_deck(
                    prompts,
                    fallback="noop",
                    profile={},
                    run_dir=run_dir,
                    task_id="TASK",
                    cycle=1,
                    experiment_id="ab-01",
                    target_fingerprint="same-target",
                    stop_on_error=True,
                )
            finally:
                bandit.execute_prompt = original
            self.assertEqual(code, 0)
            self.assertEqual(len(set(worker_threads)), 2)


if __name__ == "__main__":
    unittest.main()
