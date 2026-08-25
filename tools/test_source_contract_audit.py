from __future__ import annotations

import json
import hashlib
from pathlib import Path
import shutil
import tempfile
import unittest
from typing import Any

from tools import validate_source_contract_audit as audit


ROOT = Path(__file__).resolve().parents[1]


class SourceContractAuditTests(unittest.TestCase):
    def assert_json_tamper_fails(
        self, relative_path: str, keys: tuple[Any, ...], replacement: Any
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(ROOT / "evaluation", root / "evaluation")
            path = root / relative_path
            payload = json.loads(path.read_text(encoding="utf-8"))
            cursor = payload
            for key in keys[:-1]:
                cursor = cursor[key]
            cursor[keys[-1]] = replacement
            path.write_text(
                json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            with self.assertRaises(audit.AuditError):
                audit.validate(root)

    def test_tracked_package_validates(self) -> None:
        audit.validate(ROOT)

    def test_unknown_claim_like_top_level_keys_fail_closed(self) -> None:
        mutations = (
            (
                "evaluation/source-contract-audit-v1/summary.json",
                ("human_expert_validation_complete",),
                True,
            ),
            (
                "evaluation/source-contract-audit-v1/protocol.json",
                ("evaluation_outcomes_present",),
                True,
            ),
            (
                "evaluation/source-contract-audit-v1/summary.json",
                ("post_amendment_ai_self_check",),
                {"faithful_contract_match": 18},
            ),
            (
                "evaluation/source-contract-audit-v1/adjudication.json",
                ("benchmark_execution_complete",),
                True,
            ),
            (
                "evaluation/source-contract-audit-v1/reviewer-a.json",
                ("workflow_effectiveness_supported",),
                True,
            ),
            (
                "evaluation/source-contract-audit-v1/amendment.json",
                ("evaluation_outcomes_present",),
                True,
            ),
        )
        for relative_path, keys, replacement in mutations:
            with self.subTest(relative_path=relative_path, keys=keys):
                self.assert_json_tamper_fails(
                    relative_path,
                    keys,
                    replacement,
                )

    def test_unknown_nested_keys_fail_closed(self) -> None:
        mutations = (
            (
                "evaluation/source-contract-audit-v1/protocol.json",
                ("claim_boundary", "benchmark_execution_complete"),
                True,
            ),
            (
                "evaluation/source-contract-audit-v1/summary.json",
                ("claim_boundary", "evaluation_outcomes_present"),
                True,
            ),
            (
                "evaluation/source-contract-audit-v1/reviewer-a.json",
                ("cases", 0, "human_expert_validation_complete"),
                True,
            ),
            (
                "evaluation/source-contract-audit-v1/amendment.json",
                ("timing_and_claim_boundary", "benchmark_execution_complete"),
                True,
            ),
        )
        for relative_path, keys, replacement in mutations:
            with self.subTest(relative_path=relative_path, keys=keys):
                self.assert_json_tamper_fails(
                    relative_path,
                    keys,
                    replacement,
                )

    def test_reviewer_tamper_fails_closed(self) -> None:
        self.assert_json_tamper_fails(
            "evaluation/source-contract-audit-v1/reviewer-a.json",
            ("cases", 0, "faithful_contract"),
            "mismatch",
        )

    def test_protocol_reviewer_count_and_ids_fail_closed(self) -> None:
        for keys, replacement in (
            (("review_design", "reviewer_count"), 1),
            (("review_design", "reviewer_ids"), ["ai-reviewer-a"]),
            (("review_design", "reviewers_blind_to_each_other"), False),
            (("review_design", "human_expert_reviewer_count"), 1),
        ):
            with self.subTest(keys=keys):
                self.assert_json_tamper_fails(
                    "evaluation/source-contract-audit-v1/protocol.json",
                    keys,
                    replacement,
                )

    def test_reviewer_identity_hash_and_outcome_flags_fail_closed(self) -> None:
        for keys, replacement in (
            (("reviewer_id",), "ai-reviewer-b"),
            (("human",), True),
            (("viewed_other_review_before_submission",), True),
            (("source_hashes_verified",), False),
            (("evaluated_outcomes_observed",), True),
        ):
            with self.subTest(keys=keys):
                self.assert_json_tamper_fails(
                    "evaluation/source-contract-audit-v1/reviewer-a.json",
                    keys,
                    replacement,
                )

    def test_adjudication_outcome_boundary_fails_closed(self) -> None:
        for keys, replacement in (
            (("human",), True),
            (("independent_human_expert",), True),
            (("source_pdf_reinspection",), False),
            (("evaluated_outcomes_observed",), True),
        ):
            with self.subTest(keys=keys):
                self.assert_json_tamper_fails(
                    "evaluation/source-contract-audit-v1/adjudication.json",
                    keys,
                    replacement,
                )

    def test_derived_disagreement_per_source_and_amendment_counts_fail_closed(
        self,
    ) -> None:
        mutations = (
            (
                ("agreement", "case_level_any_dimension_disagreement_count"),
                5,
            ),
            (
                ("per_source_adjudicated_original", 0, "faithful_match"),
                6,
            ),
            (
                ("pre_execution_amendment", "amended_case_count"),
                6,
            ),
        )
        for keys, replacement in mutations:
            with self.subTest(keys=keys):
                self.assert_json_tamper_fails(
                    "evaluation/source-contract-audit-v1/summary.json",
                    keys,
                    replacement,
                )

    def test_unsupported_post_amendment_aggregate_fails_closed(self) -> None:
        self.assert_json_tamper_fails(
            "evaluation/source-contract-audit-v1/summary.json",
            ("pre_execution_amendment", "post_amendment_ai_self_check"),
            {"faithful_contract_match": 18, "source_locator_correct": 18},
        )

    def test_amendment_timing_flags_fail_closed(self) -> None:
        for key in (
            "primary_model_outcomes_observed",
            "external_comparator_outcomes_observed",
            "provider_calls_for_evaluation_observed",
            "human_expert_validation_complete",
            "amendment_is_evaluation_result",
        ):
            with self.subTest(key=key):
                self.assert_json_tamper_fails(
                    "evaluation/source-contract-audit-v1/amendment.json",
                    ("timing_and_claim_boundary", key),
                    True,
                )

    def test_before_hash_is_bound_to_versioned_snapshot(self) -> None:
        self.assert_json_tamper_fails(
            "evaluation/source-contract-audit-v1/amendment.json",
            ("primary_inputs", "challenge_manifest", "before_sha256"),
            "0" * 64,
        )

    def test_pre_amendment_snapshot_tamper_fails_closed(self) -> None:
        self.assert_json_tamper_fails(
            "evaluation/source-contract-audit-v1/pre-amendment/"
            "target-drift-v1-challenges.json",
            ("suite_id",),
            "TAMPERED",
        )

    def test_base_commit_cannot_be_rebound_with_manifest_hash(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(ROOT / "evaluation", root / "evaluation")
            base_path = (
                root
                / "evaluation/source-contract-audit-v1/pre-amendment/base.json"
            )
            base = json.loads(base_path.read_text(encoding="utf-8"))
            base["base_git_commit"] = "0" * 40
            base_path.write_text(
                json.dumps(base, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            amendment_path = (
                root / "evaluation/source-contract-audit-v1/amendment.json"
            )
            amendment = json.loads(amendment_path.read_text(encoding="utf-8"))
            amendment["pre_amendment_base"]["manifest_sha256"] = hashlib.sha256(
                base_path.read_bytes()
            ).hexdigest()
            amendment["pre_amendment_base"]["base_git_commit"] = "0" * 40
            amendment_path.write_text(
                json.dumps(amendment, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            with self.assertRaises(audit.AuditError):
                audit.validate(root)

    def test_claim_boundary_is_explicit(self) -> None:
        protocol = json.loads(
            (ROOT / "evaluation/source-contract-audit-v1/protocol.json").read_text(
                encoding="utf-8"
            )
        )
        boundary = protocol["claim_boundary"]
        self.assertFalse(boundary["independent_human_expert_validation_complete"])
        self.assertFalse(boundary["evaluation_outcomes_present"])
        self.assertIn("human validation", boundary["must_not_be_described_as"])


if __name__ == "__main__":
    unittest.main()
