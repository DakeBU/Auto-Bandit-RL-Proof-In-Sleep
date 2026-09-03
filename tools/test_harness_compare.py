#!/usr/bin/env python3
"""Regression tests for evidence-bounded harness comparison."""

from __future__ import annotations

import argparse
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
    status: str = "executed",
    elapsed: float = 10.0,
    route_packet_hash: str = "same-routes",
) -> dict[str, object]:
    return {
        "task": "TASK",
        "experiment_id": experiment,
        "target_fingerprint": "same-target",
        "harness": harness,
        "run_id": f"{experiment}-{harness}",
        "attempt_id": f"{experiment}-{harness}-attempt",
        "role": "worker" if harness == "master-worker" else "lower",
        "progress_class": "unreviewed",
        "status": status,
        "reviewer_validated": False,
        "verifier_evidence": [],
        "route_packet_hash": route_packet_hash,
        "route_fingerprint": f"route-{experiment}",
        "obligations_before": 2,
        "obligations_after": 2,
        "elapsed_seconds": elapsed,
    }


def reviewed_rows(
    experiment: str,
    harness: str,
    progress: str,
    *,
    status: str = "accepted",
    route_packet_hash: str = "same-routes",
) -> list[dict[str, object]]:
    execution = row(
        experiment,
        harness,
        progress,
        route_packet_hash=route_packet_hash,
    )
    verdict = {
        **execution,
        "role": "reviewer",
        "status": status,
        "progress_class": progress,
        "reviewer_validated": True,
        "verifier_evidence": ["lake build"],
        "obligations_after": 1 if progress != "no-progress" else 2,
        "elapsed_seconds": 0.0,
        "prompt_chars": 0,
        "input_tokens": 0,
        "output_tokens": 0,
    }
    return [execution, verdict]


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
            rows.extend(reviewed_rows(experiment, "hierarchical", "diagnostic"))
            rows.extend(reviewed_rows(experiment, "master-worker", "compiled-leaf"))
        analysis = harness_compare.analyze_trials(rows, task="TASK")
        self.assertEqual(analysis["matched_experiments"], ["ab-01", "ab-02"])
        self.assertEqual(analysis["decision"]["status"], "measured")
        self.assertEqual(analysis["decision"]["recommended_default"], "master-worker")

    def test_exit_zero_without_review_is_not_substantive(self) -> None:
        unreviewed = row("ab-01", "master-worker", "compiled-leaf")
        summary = harness_compare.summarize_arm([unreviewed], "master-worker")
        self.assertEqual(summary["attempts"], 1)
        self.assertEqual(summary["reviewed_attempts"], 0)
        self.assertEqual(summary["substantive_score"], 0.0)

    def test_worker_cannot_self_validate_compiled_progress(self) -> None:
        self_report = row("ab-01", "master-worker", "compiled-leaf")
        self_report.update({
            "status": "compiled",
            "progress_class": "compiled-leaf",
            "reviewer_validated": True,
            "verifier_evidence": ["lake build"],
        })
        summary = harness_compare.summarize_arm([self_report], "master-worker")
        self.assertEqual(summary["reviewed_attempts"], 0)
        self.assertEqual(summary["substantive_score"], 0.0)

    def test_trial_log_rejects_worker_owned_reviewer_flag(self) -> None:
        args = argparse.Namespace(
            role="worker",
            kind="attempt",
            status="compiled",
            harness="master-worker",
            progress_class="compiled-leaf",
            reviewer_validated=True,
            attempt_id="attempt-1",
            verifier_evidence=["lake build"],
        )
        with self.assertRaisesRegex(SystemExit, "only by --role reviewer"):
            bandit.cmd_trial_log(args)

    def test_reviewer_verdict_preserves_worker_measurements(self) -> None:
        rows = reviewed_rows("ab-01", "master-worker", "compiled-leaf")
        rows[0]["input_tokens"] = 123
        summary = harness_compare.summarize_arm(rows, "master-worker")
        self.assertEqual(summary["reviewed_attempts"], 1)
        self.assertEqual(summary["critical_path_seconds"], 10.0)
        self.assertEqual(summary["input_tokens"], 123)

    def test_reviewer_join_is_scoped_to_arm_run_and_route_packet(self) -> None:
        execution = row("ab-01", "hierarchical", "compiled-leaf")
        execution["attempt_id"] = "shared-name"
        wrong_arm_review = dict(execution)
        wrong_arm_review.update(
            {
                "harness": "master-worker",
                "role": "reviewer",
                "reviewer_validated": True,
                "status": "compiled",
                "verifier_evidence": ["lake build"],
            }
        )
        wrong_route_review = dict(execution)
        wrong_route_review.update(
            {
                "role": "reviewer",
                "reviewer_validated": True,
                "status": "compiled",
                "verifier_evidence": ["lake build"],
                "route_packet_hash": "different-routes",
            }
        )
        summary = harness_compare.summarize_arm(
            [execution, wrong_arm_review, wrong_route_review], "hierarchical"
        )
        self.assertEqual(summary["reviewed_attempts"], 0)
        self.assertEqual(summary["unreviewed_attempts"], 1)

    def test_route_packet_mismatch_excludes_experiment(self) -> None:
        rows = reviewed_rows(
            "ab-01", "hierarchical", "diagnostic", route_packet_hash="routes-a"
        )
        rows.extend(
            reviewed_rows(
                "ab-01",
                "master-worker",
                "compiled-leaf",
                route_packet_hash="routes-b",
            )
        )
        analysis = harness_compare.analyze_trials(rows, task="TASK")
        self.assertEqual(analysis["matched_experiments"], [])
        self.assertIn("route-packet hash", analysis["excluded_experiments"]["ab-01"])

    def test_mermaid_exposes_both_internal_routes(self) -> None:
        rows = reviewed_rows("ab-01", "hierarchical", "diagnostic")
        rows.extend(reviewed_rows("ab-01", "master-worker", "compiled-leaf"))
        analysis = harness_compare.analyze_trials(rows, task="TASK")
        mermaid = harness_compare.render_mermaid(rows, analysis)
        self.assertIn("Hierarchical", mermaid)
        self.assertIn("Master–worker", mermaid)
        self.assertIn("compiled-leaf", mermaid)

    def test_gpt_packet_preserves_insufficient_evidence_boundary(self) -> None:
        rows = reviewed_rows("ab-01", "hierarchical", "diagnostic")
        rows.extend(reviewed_rows("ab-01", "master-worker", "compiled-leaf"))
        analysis = harness_compare.analyze_trials(rows, task="TASK")
        packet = harness_compare.render_review_prompt(rows, analysis)
        self.assertIn("insufficient-evidence", packet)
        self.assertIn("Do not infer a winner", packet)

    def test_gpt_review_parser_requires_structured_advisory_and_diagram(self) -> None:
        response = """Evidence is insufficient, so no winner is selected.

```mermaid
flowchart LR
  G[Target governor] --> I{Independent leaves?}
  I --> R[Reviewer gate]
```

```json
{
  "recommended_default": "retain-current-default",
  "confidence": "low",
  "evidence": ["No matched experiment is available."],
  "risks": ["The master bottleneck is unmeasured."],
  "next_matched_experiment": {"target": "TASK", "arms": ["hierarchical", "master-worker"]},
  "proposed_change": "Keep hierarchy as governor and test bounded parallel leaves."
}
```
"""
        parsed = harness_compare.parse_gpt_review_response(response)
        self.assertEqual(
            parsed["review"]["recommended_default"], "retain-current-default"
        )
        self.assertTrue(parsed["mermaid"].startswith("flowchart LR"))
        self.assertEqual(parsed["review"]["next_matched_experiment"]["target"], "TASK")

    def test_gpt_review_parser_rejects_unstructured_prose(self) -> None:
        with self.assertRaisesRegex(ValueError, "exactly one fenced JSON"):
            harness_compare.parse_gpt_review_response("I prefer master-worker.")

    def test_agent_command_quotes_windows_paths_with_spaces(self) -> None:
        original_name = bandit.os.name
        original_root = bandit.ROOT
        bandit.os.name = "nt"
        bandit.ROOT = Path("E:/ABRL paper/repository")
        try:
            command = bandit.format_agent_command(
                "codex exec --cd {root} - < {prompt}",
                Path("E:/ABRL paper/input prompt.md"),
                Path("E:/ABRL paper/run"),
                "TASK WITH SPACE",
                1,
            )
        finally:
            bandit.os.name = original_name
            bandit.ROOT = original_root
        self.assertIn('"E:\\ABRL paper\\repository"', command)
        self.assertIn('< "E:\\ABRL paper\\input prompt.md"', command)

    def test_hierarchical_deck_receives_the_same_frozen_route_packet(self) -> None:
        routes = [
            {
                "id": "route-a",
                "fingerprint": "a",
                "owned_files": ["BanditRLProof/A.lean"],
                "expected_information_gain": "close leaf A",
            },
            {
                "id": "route-b",
                "fingerprint": "b",
                "owned_files": ["BanditRLProof/B.lean"],
                "expected_information_gain": "diagnose leaf B",
            },
        ]
        route_hash = bandit.frozen_route_packet_hash(routes)
        with tempfile.TemporaryDirectory() as temporary:
            run_dir = Path(temporary) / "hierarchical"
            run_dir.mkdir()
            prompts = bandit.make_prompt_deck(
                run_dir,
                "TASK",
                1,
                2,
                routes=routes,
                experiment_id="ab-01",
                target_fingerprint="same-target",
                route_packet_hash=route_hash,
            )
            context = (run_dir / "00_context.md").read_text(encoding="utf-8")
            lower_a = (run_dir / "31_lower_1.md").read_text(encoding="utf-8")
            lower_b = (run_dir / "32_lower_2.md").read_text(encoding="utf-8")
            reviewer = (run_dir / "40_reviewer.md").read_text(encoding="utf-8")
            self.assertIn(route_hash, context)
            self.assertIn('"id": "route-a"', lower_a)
            self.assertNotIn('"id": "route-b"', lower_a)
            self.assertIn('"id": "route-b"', lower_b)
            self.assertIn("--role reviewer", reviewer)
            self.assertEqual(len(prompts), 5)

            master_dir = Path(temporary) / "master-worker"
            master_dir.mkdir()
            bandit.make_master_worker_prompt_deck(
                master_dir,
                "TASK",
                1,
                routes,
                "ab-01",
                "same-target",
            )
            master_context = (master_dir / "00_context.md").read_text(
                encoding="utf-8"
            )
            master_contract = (master_dir / "harness.json").read_text(
                encoding="utf-8"
            )
            self.assertIn(route_hash, master_context)
            self.assertIn(route_hash, master_contract)

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
                    route_packet_hash="same-routes",
                    stop_on_error=True,
                )
            finally:
                bandit.execute_prompt = original
            self.assertEqual(code, 0)
            self.assertEqual(len(set(worker_threads)), 2)


if __name__ == "__main__":
    unittest.main()
