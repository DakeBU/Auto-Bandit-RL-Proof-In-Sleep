from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from tools import prepare_target_drift_human_contract_review as prepare
from tools import validate_target_drift_human_contract_review as validate


def dump(path: Path, value: dict) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


class HumanContractReviewTest(unittest.TestCase):
    def completed_reviewer(self, template: dict, reviewer_id: str) -> dict:
        value = json.loads(json.dumps(template))
        value.update({
            "reviewer_id": reviewer_id,
            "self_attested_human": True,
            "self_attested_independent_bandit_or_formalization_expert": True,
            "viewed_other_review_before_submission": False,
            "evaluation_outcomes_observed": False,
        })
        for case in value["cases"]:
            review = case["review"]
            review.update({
                "faithful_contract": "match",
                "injected_drift": "source_critical_change",
                "source_locator": "exact",
                "source_hash_verified": True,
                "confidence_1_to_3": 3,
                "rationale": "Checked each frozen field against the hash-bound source.",
                "complete_common_target_card": json.loads(json.dumps(
                    case["canonical_frozen_benchmark_card"]
                )),
            })
        return value

    def completed_adjudication(
        self, template: dict, reviewer_a_path: Path, reviewer_b_path: Path,
        reviewer_a: dict, reviewer_b: dict,
    ) -> dict:
        protocol = prepare.load(prepare.PROTOCOL)
        value = json.loads(json.dumps(template))
        value.update({
            "adjudicator_id": "review-adjudicator",
            "self_attested_human": True,
            "self_attested_independent_bandit_or_formalization_expert": True,
            "evaluation_outcomes_observed": False,
            "reviewer_a_sha256": hashlib.sha256(
                reviewer_a_path.read_bytes()
            ).hexdigest(),
            "reviewer_b_sha256": hashlib.sha256(
                reviewer_b_path.read_bytes()
            ).hexdigest(),
        })
        for case, left, right in zip(
            value["cases"], reviewer_a["cases"], reviewer_b["cases"]
        ):
            case["final_decisions"] = dict(validate.PRODUCTION_DECISIONS)
            case["final_common_target_card"] = json.loads(json.dumps(
                case["canonical_frozen_benchmark_card"]
            ))
            dimensions = validate.disagreement_dimensions(left, right, protocol)
            case["reviewer_disagreement_present"] = bool(dimensions)
            case["reviewer_disagreement_dimensions"] = dimensions
            case["reviewer_disagreement_resolved"] = bool(dimensions)
            case["adjudication_rationale"] = (
                "Resolved the listed disagreements against the frozen source."
                if dimensions else "The two self-attested reviews agree."
            )
            reasons = validate.decision_amendment_reasons(left, right, case)
            card_matches = (
                case["final_common_target_card"]
                == case["canonical_frozen_benchmark_card"]
            )
            case["source_contract_valid"] = not reasons and card_matches
        return value

    def make_bundle(self, root: Path) -> dict:
        manifest, template, adjudication_template = prepare.build_packet()
        packet = root / "packet"
        packet.mkdir()
        dump(packet / "packet-manifest.json", manifest)
        dump(packet / "reviewer-template.json", template)
        dump(packet / "adjudication-template.json", adjudication_template)
        reviewer_a_value = self.completed_reviewer(template, "reviewer-a")
        reviewer_b_value = self.completed_reviewer(template, "reviewer-b")
        reviewer_a = root / "reviewer-a.json"
        reviewer_b = root / "reviewer-b.json"
        dump(reviewer_a, reviewer_a_value)
        dump(reviewer_b, reviewer_b_value)
        adjudication = root / "adjudication.json"
        adjudication_value = self.completed_adjudication(
            adjudication_template, reviewer_a, reviewer_b,
            reviewer_a_value, reviewer_b_value,
        )
        dump(adjudication, adjudication_value)
        return {
            "packet": packet,
            "template": template,
            "adjudication_template": adjudication_template,
            "reviewer_a": reviewer_a,
            "reviewer_b": reviewer_b,
            "reviewer_a_value": reviewer_a_value,
            "reviewer_b_value": reviewer_b_value,
            "adjudication": adjudication,
            "adjudication_value": adjudication_value,
        }

    def validate_bundle(self, bundle: dict) -> dict:
        return validate.validate(
            bundle["packet"], bundle["reviewer_a"], bundle["reviewer_b"],
            bundle["adjudication"],
        )

    def rewrite_adjudication(self, bundle: dict) -> None:
        bundle["adjudication_value"] = self.completed_adjudication(
            bundle["adjudication_template"], bundle["reviewer_a"],
            bundle["reviewer_b"], bundle["reviewer_a_value"],
            bundle["reviewer_b_value"],
        )
        dump(bundle["adjudication"], bundle["adjudication_value"])

    def test_templates_do_not_prefill_human_or_expert_claims(self) -> None:
        _, reviewer, adjudication = prepare.build_packet()
        self.assertEqual(reviewer["self_attested_human"], "UNSET")
        self.assertEqual(
            reviewer["self_attested_independent_bandit_or_formalization_expert"],
            "UNSET",
        )
        self.assertEqual(adjudication["self_attested_human"], "UNSET")
        self.assertEqual(
            adjudication["self_attested_independent_bandit_or_formalization_expert"],
            "UNSET",
        )

    def test_canonical_bundle_remains_self_attested_and_not_production_eligible(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            result = self.validate_bundle(bundle)
        self.assertEqual(result["status"], validate.SELF_ATTESTED_STATUS)
        self.assertTrue(result["self_attested_review_bundle_complete"])
        self.assertFalse(result["independent_human_expert_validation_complete"])
        self.assertTrue(result["external_identity_qualification_verification_required"])
        self.assertFalse(result["production_execution_eligible"])
        self.assertFalse(result["benchmark_amendment_required"])
        self.assertTrue(result["benchmark_contract_ready_after_external_verification"])

    def test_all_not_auditable_requires_amendment_and_cannot_be_overridden(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            for reviewer_key, path_key in (
                ("reviewer_a_value", "reviewer_a"),
                ("reviewer_b_value", "reviewer_b"),
            ):
                reviewer = bundle[reviewer_key]
                for case in reviewer["cases"]:
                    case["review"].update({
                        "faithful_contract": "not_auditable",
                        "injected_drift": "not_auditable",
                        "source_locator": "not_auditable",
                    })
                dump(bundle[path_key], reviewer)
            self.rewrite_adjudication(bundle)
            for case in bundle["adjudication_value"]["cases"]:
                case["final_decisions"].update({
                    "faithful_contract": "not_auditable",
                    "injected_drift": "not_auditable",
                    "source_locator": "not_auditable",
                })
                case["source_contract_valid"] = False
            dump(bundle["adjudication"], bundle["adjudication_value"])
            result = self.validate_bundle(bundle)
            self.assertEqual(result["status"], "benchmark_amendment_required")
            self.assertEqual(len(result["benchmark_amendment_cases"]), 30)
            self.assertFalse(result["benchmark_contract_ready_after_external_verification"])

            bundle["adjudication_value"]["cases"][0]["source_contract_valid"] = True
            dump(bundle["adjudication"], bundle["adjudication_value"])
            with self.assertRaises(validate.HumanReviewError):
                self.validate_bundle(bundle)

    def test_false_disagreement_flag_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            bundle["reviewer_b_value"]["cases"][0]["review"][
                "complete_common_target_card"
            ]["source_locator_exact"] = "A different reviewed locator"
            dump(bundle["reviewer_b"], bundle["reviewer_b_value"])
            self.rewrite_adjudication(bundle)
            first = bundle["adjudication_value"]["cases"][0]
            self.assertTrue(first["reviewer_disagreement_present"])
            first["reviewer_disagreement_present"] = False
            dump(bundle["adjudication"], bundle["adjudication_value"])
            with self.assertRaises(validate.HumanReviewError):
                self.validate_bundle(bundle)

    def test_changed_final_card_requires_amendment(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            first = bundle["adjudication_value"]["cases"][0]
            first["final_common_target_card"]["source_locator_exact"] = (
                "A corrected locator requiring a new frozen benchmark"
            )
            first["source_contract_valid"] = False
            dump(bundle["adjudication"], bundle["adjudication_value"])
            result = self.validate_bundle(bundle)
        self.assertEqual(result["status"], "benchmark_amendment_required")
        self.assertIn(
            "final_common_target_card_differs_from_frozen_benchmark",
            result["benchmark_amendment_cases"][0]["reasons"],
        )

    def test_changed_frozen_pair_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            bundle["reviewer_a_value"]["cases"][0]["paired_changed_field"] = (
                "silently changed field"
            )
            dump(bundle["reviewer_a"], bundle["reviewer_a_value"])
            with self.assertRaises(validate.HumanReviewError):
                self.validate_bundle(bundle)

    def test_normalized_duplicate_reviewer_identity_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            bundle["reviewer_a_value"]["reviewer_id"] = "Reviewer-A"
            bundle["reviewer_b_value"]["reviewer_id"] = "reviewer-a"
            dump(bundle["reviewer_a"], bundle["reviewer_a_value"])
            dump(bundle["reviewer_b"], bundle["reviewer_b_value"])
            self.rewrite_adjudication(bundle)
            with self.assertRaises(validate.HumanReviewError):
                self.validate_bundle(bundle)

    def test_false_self_attested_human_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            bundle["reviewer_a_value"]["self_attested_human"] = False
            dump(bundle["reviewer_a"], bundle["reviewer_a_value"])
            self.rewrite_adjudication(bundle)
            with self.assertRaises(validate.HumanReviewError):
                self.validate_bundle(bundle)

    def test_duplicate_json_key_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            text = bundle["reviewer_a"].read_text(encoding="utf-8")
            text = text.replace(
                '  "schema_version": 1,',
                '  "schema_version": 1,\n  "schema_version": 1,',
                1,
            )
            bundle["reviewer_a"].write_text(text, encoding="utf-8")
            with self.assertRaises(validate.HumanReviewError):
                self.validate_bundle(bundle)

    def test_dispatch_kit_is_deterministic_role_separated_and_result_free(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = root / "dispatch-first"
            second = root / "dispatch-second"
            first_manifest = prepare.materialize_dispatch(first)
            second_manifest = prepare.materialize_dispatch(second)

            self.assertEqual(first_manifest, second_manifest)
            self.assertEqual(
                first_manifest["status"],
                "result_free_role_separated_dispatch_ready",
            )
            self.assertFalse(first_manifest["evaluation_outcomes_observed"])
            self.assertEqual(prepare.verify_dispatch(first), first_manifest)
            self.assertEqual(prepare.verify_dispatch(second), second_manifest)

            first_files = {
                path.relative_to(first).as_posix(): path.read_bytes()
                for path in first.rglob("*")
                if path.is_file()
            }
            second_files = {
                path.relative_to(second).as_posix(): path.read_bytes()
                for path in second.rglob("*")
                if path.is_file()
            }
            self.assertEqual(first_files, second_files)

            for slot, other in (
                ("reviewer-a", "reviewer-b"),
                ("reviewer-b", "reviewer-a"),
            ):
                role_paths = set(first_manifest["role_allowlists"][slot])
                self.assertEqual(
                    role_paths,
                    {
                        f"{slot}/README.md",
                        f"{slot}/review-protocol.json",
                        f"{slot}/reviewer-response.json",
                        f"{slot}/source-index.json",
                    },
                )
                role_text = "\n".join(
                    first_files[path].decode("utf-8") for path in sorted(role_paths)
                ).casefold()
                self.assertNotIn(f"{other}/", role_text)
                self.assertNotIn("operator/", role_text)
                self.assertNotIn("adjudication-response.json", role_text)

                response = json.loads(
                    first_files[f"{slot}/reviewer-response.json"]
                )
                self.assertEqual(response["reviewer_id"], "UNSET")
                self.assertEqual(len(response["cases"]), 30)
                self.assertTrue(
                    all(
                        case["review"]["faithful_contract"] == "UNSET"
                        and case["review"]["injected_drift"] == "UNSET"
                        for case in response["cases"]
                    )
                )

            source_index = json.loads(
                first_files["reviewer-a/source-index.json"]
            )
            self.assertEqual(source_index["source_count"], 4)
            self.assertEqual(source_index["case_count"], 30)
            self.assertTrue(
                all(
                    source["public_url"].startswith("https://")
                    and source["sha256"] != "UNSET"
                    and "local_path" not in source
                    for source in source_index["sources"]
                )
            )

    def test_dispatch_verifier_rejects_tampering_and_added_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tampered = root / "tampered"
            prepare.materialize_dispatch(tampered)
            response = tampered / "reviewer-a/reviewer-response.json"
            response.write_bytes(response.read_bytes() + b" ")
            with self.assertRaises(prepare.ReviewPacketError):
                prepare.verify_dispatch(tampered)

            added = root / "added"
            prepare.materialize_dispatch(added)
            (added / "reviewer-a/unexpected.txt").write_text(
                "untracked disclosure", encoding="utf-8"
            )
            with self.assertRaises(prepare.ReviewPacketError):
                prepare.verify_dispatch(added)


if __name__ == "__main__":
    unittest.main()
