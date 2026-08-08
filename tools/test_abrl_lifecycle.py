#!/usr/bin/env python3
"""Deterministic and faux-provider tests for ABRL lifecycle hardening."""

from __future__ import annotations

import importlib.util
import json
import tempfile
import threading
import time
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "tools" / "abrl_lifecycle.py"


def load_lifecycle_module():
    spec = importlib.util.spec_from_file_location("abrl_lifecycle_under_test", MODULE)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load tools/abrl_lifecycle.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ShadowAnalyzerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.lifecycle = load_lifecycle_module()

    def trial(self, task: str, status: str, index: int) -> dict[str, str]:
        return {
            "time": f"2026-01-01T00:00:{index:02d}+00:00",
            "task": task,
            "role": "lower" if status == "compiled" else "reviewer",
            "kind": "build" if status == "compiled" else "review",
            "status": status,
            "lean": f"Demo.{task}",
            "notes": f"{task} {status}",
            "run_id": "fixture",
        }

    def test_shadow_flags_historical_etc_exp3_digest_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            trials = root / "runs" / "trials.jsonl"
            trials.parent.mkdir(parents=True)
            rows = [
                self.trial("BRL-UCB-PORT-001", "accepted", 0),
                self.trial("BRL-ETC-PORT-001", "accepted", 1),
                self.trial("BRL-EXP3-ALL-HORIZON", "compiled", 2),
                self.trial("BRL-EXP3-ALL-HORIZON", "accepted", 3),
            ]
            trials.write_text(
                "".join(self.lifecycle.canonical_json(row) + "\n" for row in rows),
                encoding="utf-8",
            )
            digest = root / "runs" / "old" / "memory_digest.md"
            digest.parent.mkdir()
            digest.write_text("# Memory Digest\n\nTask: `BRL-ETC-PORT-001`\n", encoding="utf-8")

            report = self.lifecycle.analyze_frontier(
                root,
                trials_path=trials,
                memory_digest_path=digest,
            )

            self.assertEqual(report["mode"], "shadow-read-only")
            self.assertFalse(report["would_mutate"])
            self.assertEqual(report["inferred_frontier"]["selected_task"], "BRL-EXP3-ALL-HORIZON")
            self.assertEqual(report["mismatches"][0]["kind"], "stale_memory_digest")
            self.assertEqual(report["mismatches"][0]["memory_task"], "BRL-ETC-PORT-001")

    def test_replays_three_transitions_with_bounded_prompts(self) -> None:
        rows: list[dict[str, str]] = []
        tasks = [task for task in ["A", "B", "C", "D"] for _ in range(6)]
        for index, task in enumerate(tasks):
            row = self.trial(task, "compiled" if index % 2 == 0 else "accepted", index)
            row["notes"] = f"{task} verifier evidence " + ("x" * 200)
            rows.append(row)

        report = self.lifecycle.replay_transitions(rows, count=3)

        self.assertEqual(report["transition_count"], 3)
        self.assertEqual(
            [row["new_selected_frontier"] for row in report["transitions"]],
            ["B", "C", "D"],
        )
        for transition in report["transitions"]:
            self.assertLess(transition["new_prompt_characters"], transition["old_prompt_characters"])
            self.assertLessEqual(len(transition["selected_memory_ids"]), 5)


class MemoryAndDagTests(unittest.TestCase):
    def setUp(self) -> None:
        self.lifecycle = load_lifecycle_module()

    def record(
        self,
        name: str,
        *,
        record_type: str = "checkpoint",
        status: str = "accepted",
        supersedes: tuple[str, ...] = (),
    ) -> dict:
        return self.lifecycle.make_memory_record(
            record_type=record_type,
            task="TASK",
            provenance={"kind": "test", "reference": name},
            declaration=name,
            status=status,
            verifier_evidence=["fixture"],
            supersedes=supersedes,
            roles=["lower"],
            created_at=f"2026-01-01T00:00:{len(name):02d}+00:00",
        )

    def test_superseded_memory_is_not_injected(self) -> None:
        old = self.record("old")
        new = self.record("new", supersedes=(old["id"],))
        verified = self.record("lemma", record_type="verified_lemma", status="compiled")

        packet = self.lifecycle.select_memory(
            [old, new, verified],
            task="TASK",
            role="lower",
            limit=1,
            explicit_verified_ids=[verified["id"]],
        )

        self.assertEqual([item["id"] for item in packet], [verified["id"], new["id"]])
        self.assertNotIn(old["id"], [item["id"] for item in packet])

    def test_blocked_leaf_waits_for_dependency_change(self) -> None:
        frontier = {
            "current_leaf": {"id": "leaf", "status": "pending"},
            "dag": {"nodes": [{
                "id": "leaf",
                "status": "pending",
                "dependencies": [{
                    "kind": "declaration",
                    "name": "Demo.missing",
                    "status": "missing",
                }],
            }]},
        }

        first = self.lifecycle.dispatch_leaf(frontier, "leaf")
        self.assertFalse(first["dispatched"])
        self.assertEqual(first["missing_dependencies"][0]["name"], "Demo.missing")
        with self.assertRaisesRegex(ValueError, "blocked dependency unchanged"):
            self.lifecycle.dispatch_leaf(frontier, "leaf")

        frontier["dag"]["nodes"][0]["dependencies"][0]["status"] = "compiled"
        dispatched = self.lifecycle.dispatch_leaf(frontier, "leaf")
        self.assertTrue(dispatched["dispatched"])
        with self.assertRaisesRegex(ValueError, "duplicate dispatch"):
            self.lifecycle.dispatch_leaf(frontier, "leaf")

    def test_interrupted_dispatch_recovers_to_ready(self) -> None:
        frontier = {
            "current_leaf": {"id": "leaf", "status": "running"},
            "dag": {"nodes": [{
                "id": "leaf",
                "status": "running",
                "dependencies": [],
                "active_transaction": "dispatch-1",
            }]},
        }

        recovered = self.lifecycle.recover_interrupted_frontier(frontier)

        self.assertEqual(recovered, ["leaf"])
        self.assertEqual(frontier["dag"]["nodes"][0]["status"], "ready")
        self.assertEqual(frontier["current_leaf"]["status"], "ready")

    def test_accepted_leaf_cannot_be_redispatched(self) -> None:
        frontier = {
            "current_leaf": {"id": "leaf", "status": "accepted"},
            "dag": {"nodes": [{"id": "leaf", "status": "accepted", "dependencies": []}]},
        }
        with self.assertRaisesRegex(ValueError, "terminal leaf"):
            self.lifecycle.dispatch_leaf(frontier, "leaf")


class StatementFenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.lifecycle = load_lifecycle_module()

    def test_statement_mutation_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "BanditRLProof" / "Demo.lean"
            source.parent.mkdir(parents=True)
            source.write_text(
                "namespace Demo\n"
                "theorem fixed (n : Nat) (h : 0 < n) : 0 < n := by\n"
                "  exact h\n"
                "end Demo\n",
                encoding="utf-8",
            )
            statement = self.lifecycle.lean_declaration_header(source, "Demo.fixed")
            fence = self.lifecycle.make_statement_fence(
                declaration="Demo.fixed",
                file="BanditRLProof/Demo.lean",
                statement=statement,
                source_assumptions=["(h : 0 < n)"],
            )
            clean = self.lifecycle.safe_verify(root, fence, lean_files=[source])
            self.assertTrue(clean["ok"], clean)

            source.write_text(
                "namespace Demo\n"
                "theorem fixed (n : Nat) : 0 <= n := by\n"
                "  exact Nat.zero_le n\n"
                "end Demo\n",
                encoding="utf-8",
            )
            mutated = self.lifecycle.safe_verify(root, fence, lean_files=[source])

            self.assertFalse(mutated["ok"])
            kinds = {finding["kind"] for finding in mutated["findings"]}
            self.assertIn("statement_mutation", kinds)
            self.assertIn("source_assumption_removed", kinds)

    def test_custom_axiom_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "BanditRLProof" / "Demo.lean"
            source.parent.mkdir(parents=True)
            source.write_text(
                "namespace Demo\n"
                "theorem fixed : True := by trivial\n"
                "axiom shortcut : False\n"
                "end Demo\n",
                encoding="utf-8",
            )
            fence = self.lifecycle.make_statement_fence(
                declaration="Demo.fixed",
                file="BanditRLProof/Demo.lean",
                statement=self.lifecycle.lean_declaration_header(source, "Demo.fixed"),
            )

            report = self.lifecycle.safe_verify(root, fence, lean_files=[source])

            self.assertFalse(report["ok"])
            self.assertEqual(report["findings"][0]["kind"], "forbidden_lean_declaration")

    def test_result_let_assignments_remain_inside_fenced_statement(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "Demo.lean"
            source.write_text(
                "namespace Demo\n"
                "theorem fixed (n : Nat) :\n"
                "    let doubled := n + n\n"
                "    letI : OfNat Nat 0 := inferInstance\n"
                "    doubled = 2 * n := by\n"
                "  omega\n"
                "end Demo\n",
                encoding="utf-8",
            )

            header = self.lifecycle.lean_declaration_header(source, "Demo.fixed")

            self.assertIn("let doubled := n + n", header)
            self.assertIn("letI : OfNat Nat 0 := inferInstance", header)
            self.assertTrue(header.endswith("doubled = 2 * n"), header)
            self.assertNotIn(":= by", header)


class RuntimeContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.lifecycle = load_lifecycle_module()

    def test_concurrent_session_events_are_append_ordered(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = self.lifecycle.SessionStore(root, "session")
            errors: list[BaseException] = []

            def worker(index: int) -> None:
                try:
                    store.append("worker", {"index": index})
                except BaseException as error:  # pragma: no cover - diagnostic path
                    errors.append(error)

            threads = [threading.Thread(target=worker, args=(index,)) for index in range(8)]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()

            self.assertEqual(errors, [])
            events = self.lifecycle.read_jsonl(store.events_path)
            self.assertEqual([event["sequence"] for event in events], list(range(8)))
            self.assertEqual(len({event["entry_id"] for event in events}), 8)
            self.assertEqual(store.state()["next_sequence"], 8)

    def test_same_file_serializes_and_disjoint_files_overlap(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            queue = self.lifecycle.RepositoryMutationQueue(root)
            active = 0
            maximum = 0
            guard = threading.Lock()

            def same_action() -> None:
                nonlocal active, maximum
                with guard:
                    active += 1
                    maximum = max(maximum, active)
                time.sleep(0.03)
                with guard:
                    active -= 1

            threads = [
                threading.Thread(target=lambda: queue.run([Path("same.lean")], same_action))
                for _ in range(3)
            ]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()
            self.assertEqual(maximum, 1)

            barrier = threading.Barrier(2)
            overlapped: list[str] = []

            def disjoint(name: str) -> None:
                def action() -> None:
                    barrier.wait(timeout=2)
                    overlapped.append(name)

                queue.run([Path(name)], action)

            threads = [
                threading.Thread(target=disjoint, args=("a.lean",)),
                threading.Thread(target=disjoint, args=("b.lean",)),
            ]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()
            self.assertCountEqual(overlapped, ["a.lean", "b.lean"])

    def test_branch_follow_up_and_active_tool_restore(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = self.lifecycle.SessionStore(root, "session")
            start = store.append("start", {"current_leaf": "leaf-a"})
            fork = store.fork("route-b", abandoned_reason="missing declaration", summary="try route b")
            store.enqueue_directive("follow_up", "run reviewer after transaction")
            restored = store.restore_branch("route-b")

            with self.assertRaisesRegex(RuntimeError, "interrupt"):
                with store.active_tool("faux-lean"):
                    raise RuntimeError("interrupt")

            state = store.state()
            self.assertEqual(fork["parent_id"], start["entry_id"])
            self.assertEqual(restored["parent_id"], fork["entry_id"])
            self.assertEqual(restored["payload"]["branch_id"], "route-b")
            self.assertEqual(state["branches"]["route-b"]["abandoned_reason"], "missing declaration")
            self.assertEqual(state["directive_queue"][0]["kind"], "follow_up")
            self.assertIsNone(state["active_tool"])

    def test_steering_precedes_follow_up_after_transaction_settles(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            store = self.lifecycle.SessionStore(Path(tmp), "session")
            store.begin_transaction("tx-1", "leaf-a")
            store.enqueue_directive("follow_up", "review result")
            store.enqueue_directive("steering", "stop and replan")

            settled = store.settle_transaction("stopped")

            self.assertEqual(
                [item["kind"] for item in settled["released"]],
                ["steering", "follow_up"],
            )
            state = store.state()
            self.assertIsNone(state["active_transaction"])
            self.assertEqual(state["directive_queue"], [])
            self.assertTrue(state["replan_required"])

    def test_compaction_only_uses_measured_threshold(self) -> None:
        entries = [{"payload": {"declarations": [f"Demo.d{i}"], "errors": [f"e{i}"]}} for i in range(8)]
        untouched = self.lifecycle.compact_context(
            entries,
            measured_provider_usage=None,
            threshold=100,
        )
        self.assertFalse(untouched["compacted"])

        compacted = self.lifecycle.compact_context(
            entries,
            measured_provider_usage=100,
            threshold=100,
            recent_complete_turns=3,
            authoritative={"statement_hash": "abc"},
        )
        self.assertTrue(compacted["compacted"])
        self.assertEqual(len(compacted["recent_complete_tail"]), 3)
        self.assertEqual(len(compacted["preserved_exact"]["declarations"]), 8)
        self.assertEqual(compacted["authoritative"]["statement_hash"], "abc")

    def test_transient_retry_is_bounded_and_math_failure_is_not_retried(self) -> None:
        provider = self.lifecycle.FauxProvider([
            self.lifecycle.TransientProviderError("overload-1"),
            self.lifecycle.TransientProviderError("overload-2"),
            "ok",
        ])
        value, events = self.lifecycle.call_with_bounded_retry(provider, max_retries=2)
        self.assertEqual(value, "ok")
        self.assertEqual(provider.calls, 3)
        self.assertEqual(events[-1]["retry_count"], 2)

        math_provider = self.lifecycle.FauxProvider([
            self.lifecycle.MathematicalFailure("false statement"),
            "must not run",
        ])
        with self.assertRaises(self.lifecycle.MathematicalFailure):
            self.lifecycle.call_with_bounded_retry(math_provider, max_retries=5)
        self.assertEqual(math_provider.calls, 1)

        exhausted = self.lifecycle.FauxProvider([
            self.lifecycle.TransientProviderError("one"),
            self.lifecycle.TransientProviderError("two"),
        ])
        with self.assertRaises(self.lifecycle.TransientProviderError):
            self.lifecycle.call_with_bounded_retry(exhausted, max_retries=1)
        self.assertEqual(exhausted.calls, 2)

    def test_skill_collision_requires_explicit_precedence(self) -> None:
        base = {
            "name": "probability",
            "version": "1",
            "allowed_roles": ["middle", "lower"],
            "model_visible": True,
        }
        manifests = [
            {**base, "provenance": "repo"},
            {**base, "provenance": "user"},
        ]
        with self.assertRaisesRegex(ValueError, "collision"):
            self.lifecycle.discover_skills(manifests)

        selected = self.lifecycle.discover_skills(
            manifests,
            precedence={"probability": "repo"},
        )
        self.assertEqual(selected[0]["provenance"], "repo")


if __name__ == "__main__":
    unittest.main()
