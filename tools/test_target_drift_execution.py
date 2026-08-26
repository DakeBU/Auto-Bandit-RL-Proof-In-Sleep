#!/usr/bin/env python3
"""Tests for the result-free target-drift execution preparation layer."""

from __future__ import annotations

import json
import io
import shutil
import subprocess
import sys
import unittest
import tempfile
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import finalize_target_drift_config as finalize  # noqa: E402
import launch_target_drift_checker_container as checker_launcher  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402
import test_target_drift_human_contract_external_verification as human_external_test  # noqa: E402
import validate_target_drift_human_contract_review as human_self_review  # noqa: E402


class TargetDriftExecutionTest(unittest.TestCase):
    def make_signed_human_execution_fixture(
        self, root: Path,
    ) -> tuple[dict, dict, dict[str, bytes], Path]:
        fixture = human_external_test.ExternalVerificationSignatureTest(
            "test_ephemeral_ed25519_positive_path_is_conservatively_scoped"
        )
        bundle = fixture.make_bundle(root)
        attestation = fixture.validate_bundle(bundle)
        attestation_path = root / "external-attestation.json"
        human_external_test.dump(attestation_path, attestation)
        verifier = next(
            item for item in bundle["registry_value"]["signers"]
            if item["slot"] == "external_verifier"
        )
        anchor = {
            "schema_version": 1,
            "contract_id": prepare.TRUST_ANCHOR_CONTRACT_ID,
            "anchor_id": "excluded-ephemeral-four-key-fixture",
            "status": prepare.TRUST_ANCHOR_EXCLUDED_STATUS,
            "anchor_git_commit": "UNSET",
            "anchor_repository_path": "UNSET",
            "anchor_public_repository_url": "UNSET",
            "anchor_public_ref": "UNSET",
            "anchor_public_commit_locator": "UNSET",
            "anchor_registered_at_utc": bundle["registry_value"]["registered_at_utc"],
            "review_started_before_anchor": False,
            "evaluation_outcomes_observed_before_anchor": False,
            "benchmark_execution_complete_before_anchor": False,
            "role_registry_bytes_sha256": prepare.sha256_file(bundle["registry"]),
            "role_registry_canonical_sha256": prepare.sha256_bytes(
                prepare.external_contract_review.canonical_bytes(
                    bundle["registry_value"]
                )
            ),
            "allowed_signers_bytes_sha256": prepare.sha256_file(
                bundle["allowed_signers"]
            ),
            "external_verifier_principal": verifier["principal"],
            "external_verifier_public_key_fingerprint": verifier[
                "public_key_fingerprint"
            ],
            "public_escrow_receipt_locator": bundle["receipt_value"][
                "public_escrow_reference"
            ],
            "public_escrow_receipt_sha256": bundle["receipt_value"][
                "public_escrow_receipt_sha256"
            ],
            "claim_boundary": prepare.TRUST_ANCHOR_CLAIM_BOUNDARY,
        }
        anchor_path = root / "excluded-external-trust-anchor.json"
        human_external_test.dump(anchor_path, anchor)
        proof_path = root / "excluded-external-trust-anchor-proof.pack"
        proof_path.write_bytes(prepare.TRUST_ANCHOR_EXCLUDED_PROOF)
        config = json.loads((
            ROOT / "evaluation" / "target-drift-v2" / "execution-template.json"
        ).read_text(encoding="utf-8"))
        human = config["human_source_contract_validation"]
        human.update({
            "review_packet": str(bundle["packet"]),
            "reviewer_a": str(bundle["reviewer_a"]),
            "reviewer_a_signature": str(bundle["reviewer_a_signature"]),
            "reviewer_b": str(bundle["reviewer_b"]),
            "reviewer_b_signature": str(bundle["reviewer_b_signature"]),
            "adjudication": str(bundle["adjudication"]),
            "adjudication_signature": str(bundle["adjudicator_signature"]),
            "completion_attestation": str(bundle["completion"]),
            "external_trust_anchor": str(anchor_path),
            "external_trust_anchor_git_object_proof": str(proof_path),
            "role_registry": str(bundle["registry"]),
            "allowed_signers": str(bundle["allowed_signers"]),
            "external_receipt": str(bundle["receipt"]),
            "external_receipt_signature": str(bundle["verifier_signature"]),
            "external_attestation": str(attestation_path),
            "combined_prerequisite_satisfied": False,
        })
        human["review_packet_manifest_sha256"] = prepare.sha256_file(
            bundle["packet"] / "packet-manifest.json"
        )
        for path_field, hash_field, _ in prepare.HUMAN_REVIEW_FILE_BINDINGS:
            human[hash_field] = prepare.sha256_file(
                prepare.resolve_repo_path(human[path_field])
            )
        evidence = prepare.validate_human_source_contract_review(
            config, require_completion=True, require_combined_record=False,
            allow_excluded_unanchored_fixture=True,
        )
        pack = root / "packed-human-review"
        review_root = pack / "human_source_contract_review"
        review_root.mkdir(parents=True)
        for name, payload in evidence.items():
            (review_root / name).write_bytes(payload)
        (pack / "operator_challenges.json").write_bytes((
            ROOT / config["challenge_manifest"]
        ).read_bytes())
        (pack / "paired_requirements.json").write_bytes((
            ROOT / config["paired_requirements"]
        ).read_bytes())
        packed_config = prepare.sealed_config_for_pack(config)
        self.assertEqual(
            prepare.validate_packed_human_source_contract_review(
                pack, packed_config, require_combined_record=False,
                allow_excluded_unanchored_fixture=True,
            ),
            evidence,
        )
        return config, packed_config, evidence, pack

    def test_codex_configuration_probe_rejects_an_invalid_tier(self) -> None:
        provider = {
            "executable": str(Path(sys.executable).resolve()),
            "process_environment": {},
        }
        model = {"reasoning_effort": "high", "service_tier": "invalid"}
        completed = subprocess.CompletedProcess([], 2, stdout=b"invalid tier")
        with mock.patch.object(prepare.subprocess, "run", return_value=completed):
            with self.assertRaises(SystemExit):
                prepare.validate_codex_cli_configuration(provider, model)

    def test_codex_provider_runtime_requires_an_auth_only_source_and_frozen_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            auth_source = Path(directory).resolve()
            (auth_source / "auth.json").write_text("{}\n", encoding="utf-8")
            runtime = Path(sys.executable).resolve()
            output = prepare.provider_runtime_version_output(runtime)
            provider = {
                "kind": "codex_cli", "executable": str(runtime),
                "executable_sha256": prepare.sha256_file(runtime),
                "version": output.decode("utf-8").strip(),
                "version_output_sha256": prepare.sha256_bytes(output),
                "auth_source_path": str(auth_source),
                "fresh_codex_home_attestation": (
                    "One auth file is copied into a new disposable home per invocation."
                ),
                "process_environment": {},
                "shell_environment": {"PATH": "frozen-path"},
            }
            self.assertEqual(
                prepare.validate_provider_runtime(provider, require_hash=True), runtime
            )
            (auth_source / "config.toml").write_text("[features]\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                prepare.validate_provider_runtime(provider, require_hash=True)

    def test_template_and_prompts_validate_while_unfrozen(self) -> None:
        prepare.check_template(
            ROOT / "evaluation" / "target-drift-v1" / "execution-template.json"
        )

    def test_v1_and_v2_readiness_reports_cannot_be_conflated(self) -> None:
        expected = {
            "target-drift-v1": ("ABRL-TARGET-DRIFT-V1", 26),
            "target-drift-v2": ("ABRL-TARGET-DRIFT-V2", 161),
        }
        for directory, (suite_id, unresolved_count) in expected.items():
            config_path = ROOT / "evaluation" / directory / "execution-template.json"
            config = json.loads(config_path.read_text(encoding="utf-8"))
            self.assertEqual(config["suite_id"], suite_id)
            self.assertEqual(len(prepare.unset_paths(config)), unresolved_count)
            output = io.StringIO()
            with redirect_stdout(output):
                prepare.check_template(config_path)
            report = output.getvalue()
            self.assertIn(suite_id, report)
            self.assertIn(
                f"{unresolved_count} unresolved placeholders across machine, human, "
                "and provenance fields",
                report,
            )
        v2_human = json.loads((
            ROOT / "evaluation" / "target-drift-v2" / "execution-template.json"
        ).read_text(encoding="utf-8"))["human_source_contract_validation"]
        self.assertEqual(v2_human["external_trust_anchor"], "UNSET")
        self.assertEqual(
            v2_human["external_trust_anchor_git_object_proof"], "UNSET"
        )
        self.assertEqual(v2_human["combined_prerequisite_satisfied"], "UNSET")

    @unittest.skipUnless(shutil.which("ssh-keygen"), "OpenSSH ssh-keygen is unavailable")
    def test_combined_human_gate_uses_both_layers_and_seals_operator_paths(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config, packed, evidence, pack = self.make_signed_human_execution_fixture(root)
            self.assertFalse(
                config["human_source_contract_validation"][
                    "combined_prerequisite_satisfied"
                ]
            )
            with self.assertRaises(SystemExit):
                prepare.validate_human_source_contract_review(
                    config, require_completion=True, require_combined_record=False
                )
            self.assertTrue(
                config["human_source_contract_validation"]["reviewer_a"].startswith(
                    str(root)
                )
            )
            packed_text = json.dumps(packed)
            self.assertNotIn(str(root).replace("\\", "\\\\"), packed_text)
            self.assertEqual(
                prepare.normalized_config_for_digest(config),
                prepare.normalized_config_for_digest(packed),
            )
            self_completion = json.loads(
                evidence["self-attested-completion.json"].decode("utf-8")
            )
            external_attestation = json.loads(
                evidence["external-attestation.json"].decode("utf-8")
            )
            self.assertFalse(self_completion["production_execution_eligible"])
            self.assertFalse(
                external_attestation["production_execution_eligible"]
            )
            self.assertFalse(
                external_attestation["production_execution_eligible_from_this_layer_alone"]
            )
            combined_true = json.loads(json.dumps(packed))
            combined_true["human_source_contract_validation"][
                "combined_prerequisite_satisfied"
            ] = True
            with self.assertRaises(SystemExit):
                prepare.validate_packed_human_source_contract_review(
                    pack, combined_true, require_combined_record=False,
                    allow_excluded_unanchored_fixture=True,
                )
            with self.assertRaises(SystemExit):
                prepare.validate_packed_human_source_contract_review(pack, packed)
            overclaimed = json.loads(json.dumps(packed))
            overclaimed["human_source_contract_validation"][
                "independent_human_expert_validation_complete"
            ] = True
            with self.assertRaises(SystemExit):
                prepare.validate_packed_human_source_contract_review(
                    pack, overclaimed, require_combined_record=False,
                    allow_excluded_unanchored_fixture=True,
                )

    @unittest.skipUnless(shutil.which("ssh-keygen"), "OpenSSH ssh-keygen is unavailable")
    def test_packed_human_gate_rejects_forged_attestation_and_tampered_bytes(self) -> None:
        failures = (
            SystemExit,
            prepare.human_contract_review.HumanReviewError,
            prepare.external_contract_review.ExternalVerificationError,
        )
        with tempfile.TemporaryDirectory() as directory:
            _, packed, evidence, pack = self.make_signed_human_execution_fixture(
                Path(directory)
            )
            review_root = pack / "human_source_contract_review"
            human = packed["human_source_contract_validation"]
            filename_hash_fields = {
                filename: hash_field
                for _, hash_field, filename in prepare.HUMAN_REVIEW_FILE_BINDINGS
            }

            forged = json.loads(evidence["external-attestation.json"].decode("utf-8"))
            forged["status"] = "fabricated_external_attestation"
            forged_bytes = prepare.canonical_json_bytes(forged)
            (review_root / "external-attestation.json").write_bytes(forged_bytes)
            forged_config = json.loads(json.dumps(packed))
            forged_config["human_source_contract_validation"][
                "external_attestation_sha256"
            ] = prepare.sha256_bytes(forged_bytes)
            with self.assertRaises(failures):
                prepare.validate_packed_human_source_contract_review(
                    pack, forged_config, require_combined_record=False,
                    allow_excluded_unanchored_fixture=True,
                )
            (review_root / "external-attestation.json").write_bytes(
                evidence["external-attestation.json"]
            )

            for filename, mutate in (
                (
                    "reviewer-a.json",
                    lambda payload: {
                        **payload,
                        "cases": [
                            {
                                **payload["cases"][0],
                                "review": {
                                    **payload["cases"][0]["review"],
                                    "rationale": "Semantically tampered after signing.",
                                },
                            },
                            *payload["cases"][1:],
                        ],
                    },
                ),
                ("reviewer-a.sig", lambda payload: payload + b"tamper"),
                (
                    "external-receipt.json",
                    lambda payload: {
                        **payload,
                        "public_escrow_reference":
                        "https://example.invalid/tampered-after-signing",
                    },
                ),
                (
                    "external-trust-anchor.json",
                    lambda payload: {
                        **payload,
                        "public_escrow_receipt_sha256": "0" * 64,
                    },
                ),
                (
                    "external-trust-anchor-contract.json",
                    lambda payload: {
                        **payload,
                        "status": "weakened-contract",
                    },
                ),
                (
                    "external-trust-anchor-git-object-proof.pack",
                    lambda payload: payload + b"tamper",
                ),
            ):
                with self.subTest(filename=filename):
                    original = evidence[filename]
                    if filename.endswith(".json"):
                        changed_value = mutate(json.loads(original.decode("utf-8")))
                        changed = prepare.canonical_json_bytes(changed_value)
                    else:
                        changed = mutate(original)
                    (review_root / filename).write_bytes(changed)
                    changed_config = json.loads(json.dumps(packed))
                    changed_config["human_source_contract_validation"][
                        filename_hash_fields[filename]
                    ] = prepare.sha256_bytes(changed)
                    with self.assertRaises(failures):
                        prepare.validate_packed_human_source_contract_review(
                            pack, changed_config, require_combined_record=False,
                            allow_excluded_unanchored_fixture=True,
                        )
                    (review_root / filename).write_bytes(original)

    @unittest.skipUnless(shutil.which("ssh-keygen"), "OpenSSH ssh-keygen is unavailable")
    def test_amendment_required_review_cannot_reach_combined_gate(self) -> None:
        failures = (
            SystemExit,
            prepare.human_contract_review.HumanReviewError,
            prepare.external_contract_review.ExternalVerificationError,
        )
        with tempfile.TemporaryDirectory() as directory:
            _, packed, _, pack = self.make_signed_human_execution_fixture(Path(directory))
            review_root = pack / "human_source_contract_review"
            reviewer_path = review_root / "reviewer-a.json"
            reviewer = json.loads(reviewer_path.read_text(encoding="utf-8"))
            reviewer["cases"][0]["review"]["faithful_contract"] = "needs_correction"
            reviewer["cases"][0]["review"]["rationale"] = (
                "The frozen faithful contract requires a benchmark amendment."
            )
            reviewer_path.write_bytes(prepare.canonical_json_bytes(reviewer))
            adjudication_path = review_root / "adjudication.json"
            adjudication = json.loads(adjudication_path.read_text(encoding="utf-8"))
            adjudication["reviewer_a_sha256"] = prepare.sha256_file(reviewer_path)
            adjudication_case = adjudication["cases"][0]
            adjudication_case.update({
                "source_contract_valid": False,
                "reviewer_disagreement_present": True,
                "reviewer_disagreement_dimensions": ["decision.faithful_contract"],
                "reviewer_disagreement_resolved": True,
                "adjudication_rationale":
                    "Machine-derived reviewer mismatch requires amendment.",
            })
            adjudication_path.write_bytes(prepare.canonical_json_bytes(adjudication))
            completion = human_self_review.validate(
                review_root, reviewer_path, review_root / "reviewer-b.json",
                adjudication_path,
                protocol_path=review_root / "self-review-protocol.json",
                challenge_path=pack / "operator_challenges.json",
                paired_path=pack / "paired_requirements.json",
            )
            self.assertEqual(completion["status"], "benchmark_amendment_required")
            completion_path = review_root / "self-attested-completion.json"
            completion_path.write_bytes(prepare.canonical_json_bytes(completion))
            changed = json.loads(json.dumps(packed))
            human = changed["human_source_contract_validation"]
            human["reviewer_a_sha256"] = prepare.sha256_file(reviewer_path)
            human["adjudication_sha256"] = prepare.sha256_file(adjudication_path)
            human["completion_attestation_sha256"] = prepare.sha256_file(completion_path)
            with self.assertRaises(failures):
                prepare.validate_packed_human_source_contract_review(
                    pack, changed, require_combined_record=False,
                    allow_excluded_unanchored_fixture=True,
                )

    def test_unqualified_cli_readiness_check_still_targets_v1(self) -> None:
        completed = subprocess.run(
            [
                sys.executable,
                str(TOOLS / "prepare_target_drift_execution.py"),
                "--check-template",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        report = completed.stdout + completed.stderr
        self.assertEqual(completed.returncode, 0)
        self.assertIn("ABRL-TARGET-DRIFT-V1", report)
        self.assertIn(
            "26 unresolved placeholders across machine, human, and provenance fields",
            report,
        )
        self.assertNotIn("ABRL-TARGET-DRIFT-V2", report)

    def test_live_pack_verifier_must_equal_pack_bound_source_bytes(self) -> None:
        live = {
            "prepare_target_drift_execution.py":
                Path(prepare.__file__).resolve().read_bytes(),
            "prepare_target_drift_human_contract_review.py": Path(
                prepare.human_contract_review.prepare.__file__
            ).resolve().read_bytes(),
            "validate_target_drift_human_contract_review.py": Path(
                prepare.human_contract_review.__file__
            ).resolve().read_bytes(),
            "validate_target_drift_human_contract_external_verification.py": Path(
                prepare.external_contract_review.__file__
            ).resolve().read_bytes(),
        }
        prepare.validate_live_pack_verifier_trust_anchor(live)
        changed = dict(live)
        changed["validate_target_drift_human_contract_review.py"] += b"tamper"
        with self.assertRaises(SystemExit):
            prepare.validate_live_pack_verifier_trust_anchor(changed)

    def test_sorted_json_roundtrip_does_not_change_condition_semantics(self) -> None:
        config = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        sorted_roundtrip = json.loads(json.dumps(config, sort_keys=True))
        prepare.validate_prompt_templates(sorted_roundtrip, require_hashes=False)
        prepare.validate_resource_policy(sorted_roundtrip, require_hash=False)

    def test_unset_paths_excludes_human_readable_ledger(self) -> None:
        value = {
            "model": {"id": "UNSET"},
            "sealed_agent_view": {"aggregate_sha256": "UNSET"},
            "unresolved_fields": ["UNSET is descriptive here"],
        }
        self.assertEqual(
            prepare.unset_paths(value),
            ["model.id", "sealed_agent_view.aggregate_sha256"],
        )

    def test_adapter_contract_binds_runtime_and_sealed_entrypoint(self) -> None:
        config = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        adapter = config["execution_adapter"]
        contract = ROOT / adapter["contract"]
        entrypoint = ROOT / "tools" / "fake_target_drift_adapter.py"
        runtime = Path(sys.executable).resolve()
        image_digest = "sha256:" + "a" * 64
        adapter.update({
            "contract_sha256": prepare.sha256_file(contract),
            "entrypoint_path": "tools/fake_target_drift_adapter.py",
            "entrypoint_sha256": prepare.sha256_file(entrypoint),
            "runtime_executable": str(runtime),
            "runtime_executable_sha256": prepare.sha256_file(runtime),
            "provider_runtime": {
                "kind": "excluded_fixture",
                "executable": str(runtime),
                "executable_sha256": prepare.sha256_file(runtime),
                "version": prepare.provider_runtime_version_output(runtime).decode(
                    "utf-8"
                ).strip(),
                "version_output_sha256": prepare.sha256_bytes(
                    prepare.provider_runtime_version_output(runtime)
                ),
            },
            "container_or_sandbox_image_digest": image_digest,
            "command_argv": [
                str(runtime), "{{ADAPTER_ENTRYPOINT_PATH}}",
                "{{REQUEST_PATH}}", "{{RESPONSE_PATH}}", "{{TRACE_PATH}}",
                "{{AGENT_MOUNT}}", image_digest,
            ],
        })
        prepare.validate_adapter_contract(config, require_hash=True)
        self.assertEqual(
            prepare.execution_code_paths(config)["execution_adapter_entrypoint"],
            entrypoint.resolve(),
        )
        rendered = runner.render_adapter_command(adapter["command_argv"], {
            "{{ADAPTER_ENTRYPOINT_PATH}}": "C:/sealed/adapter",
            "{{REQUEST_PATH}}": "C:/run/request.json",
            "{{RESPONSE_PATH}}": "C:/run/response.json",
            "{{TRACE_PATH}}": "C:/run/trace.jsonl",
            "{{AGENT_MOUNT}}": "C:/run/agent",
        })
        self.assertEqual(rendered[1], "C:/sealed/adapter")
        adapter["entrypoint_sha256"] = "b" * 64
        with self.assertRaises(SystemExit):
            prepare.validate_adapter_contract(config, require_hash=True)
        adapter["entrypoint_sha256"] = prepare.sha256_file(entrypoint)
        adapter["runtime_executable_sha256"] = "c" * 64
        with self.assertRaises(SystemExit):
            prepare.validate_adapter_contract(config, require_hash=True)

    def test_agent_case_strips_adjudication_keys(self) -> None:
        challenges = json.loads(
            (ROOT / "evaluation" / "target-drift-v1" / "challenges.json")
            .read_text(encoding="utf-8")
        )["cases"]
        case = challenges[0]
        source = {
            "sha256": case["source_sha256"],
            "resolved_path": "C:/sealed/source.pdf",
        }
        paired_payload = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "paired-requirements.json")
            .read_text(encoding="utf-8")
        )
        paired = paired_payload["cases"][0]
        agent_case = prepare.sanitized_case(
            case, source, paired, paired_payload["common_template"]
        )
        forbidden = {
            "faithful_contract",
            "expected_affected_fields",
            "drift_class",
            "stratum",
        }
        self.assertFalse(forbidden & agent_case.keys())
        self.assertIn(paired["injected_drift_value"], agent_case["injected_drift_requirement"])
        self.assertIn(paired["source_faithful_value"], agent_case["source_faithful_requirement"])
        prefix = "The proposed Lean target assigns the source-critical field"
        self.assertTrue(agent_case["source_faithful_requirement"].startswith(prefix))
        self.assertTrue(agent_case["injected_drift_requirement"].startswith(prefix))

    def test_v2_requirement_assignment_is_balanced_and_condition_paired(self) -> None:
        variants = [
            prepare.requirement_variant(case_index, replicate_index)
            for case_index in range(30)
            for replicate_index in range(5)
        ]
        self.assertEqual(variants.count("source_faithful"), 75)
        self.assertEqual(variants.count("injected_drift"), 75)

    def test_v2_replicate_schedule_must_be_exactly_zero_through_four(self) -> None:
        template = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        self.assertEqual(prepare.validate_paired_replicates(template), [0, 1, 2, 3, 4])
        for invalid in (
            [4, 3, 2, 1, 0],
            [0, 1, 2, 3, 5],
            [False, 1, 2, 3, 4],
            [0, 1, 2, 3],
        ):
            with self.subTest(invalid=invalid):
                config = json.loads(json.dumps(template))
                config["randomization"]["paired_replicates"] = invalid
                with self.assertRaises(SystemExit):
                    prepare.validate_paired_replicates(config)

    def test_pack_verify_and_freeze_reject_noncanonical_replicates_first(self) -> None:
        config = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        config["execution_status"] = "preseal_ready"
        config["randomization"]["paired_replicates"] = [0, 1, 2, 3, 5]
        with tempfile.TemporaryDirectory() as directory:
            pack = Path(directory)
            config_path = pack / "execution_config.json"
            config_path.write_text(json.dumps(config) + "\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                prepare.verify_pack(pack)
            with self.assertRaises(SystemExit):
                finalize.freeze_config(config_path, pack, pack / "frozen.json")

    def test_sealed_pack_loader_rejects_duplicate_json_keys(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            pack = Path(directory)
            (pack / "execution_config.json").write_text(
                '{"execution_status":"preseal_ready",'
                '"execution_status":"frozen_ready"}\n',
                encoding="utf-8",
            )
            with self.assertRaises(SystemExit):
                prepare.verify_pack(pack)
            duplicate = pack / "duplicate.json"
            duplicate.write_text('{"a":1,"a":2}\n', encoding="utf-8")
            with self.assertRaises(SystemExit):
                finalize.load(duplicate)

    def test_packed_config_rewrites_all_operator_local_paths_portably(self) -> None:
        config = json.loads((
            ROOT / "evaluation" / "target-drift-v2" / "execution-template.json"
        ).read_text(encoding="utf-8"))
        operator_root = r"C:\operator-private\target-drift"
        operator_root_forward = "C:/operator-private/target-drift"
        config["source_files_manifest"] = operator_root + r"\sources.json"
        human = config["human_source_contract_validation"]
        human["review_packet"] = operator_root + r"\review"
        for path_field, _, filename in prepare.HUMAN_REVIEW_FILE_BINDINGS:
            if path_field not in {
                "protocol", "external_protocol", "external_trust_anchor_contract",
            }:
                human[path_field] = operator_root + "\\review\\" + filename
        adapter = config["execution_adapter"]
        adapter.update({
            "entrypoint_path": operator_root + r"\adapter.py",
            "runtime_executable": operator_root + r"\python.exe",
            "runtime_executable_sha256": "1" * 64,
            "budget_enforcement_attestation": {"log": operator_root + r"\budget.log"},
            "filesystem_network_process_attestation": operator_root + r"\sandbox.txt",
            "command_argv": [operator_root + r"\python.exe", operator_root + r"\adapter.py"],
        })
        adapter["provider_runtime"].update({
            "executable": operator_root + r"\codex.exe",
            "executable_sha256": "2" * 64,
            "auth_source_path": operator_root + r"\auth",
            "fresh_codex_home_attestation": operator_root + r"\fresh-home.txt",
            "process_environment": {"TRACE": operator_root + r"\trace"},
            "shell_environment": {"PATH": operator_root + r"\bin"},
        })
        checker = config["posthoc_checker"]
        checker.update({
            "driver_path": operator_root + r"\check.py",
            "inner_checker_path": operator_root + r"\inner.py",
            "isolation_probe_runner_path": operator_root + r"\probe.py",
            "host_launcher_path": operator_root + r"\launch.py",
            "host_python_executable": operator_root + r"\python.exe",
            "host_python_executable_sha256": "3" * 64,
            "container_runtime_executable": operator_root + r"\docker.exe",
            "container_runtime_executable_sha256": "4" * 64,
            "checker_image_recipe": operator_root + r"\Containerfile",
            "checker_image_sbom": operator_root + r"\sbom.json",
            "checker_image_build_input_manifest": operator_root + r"\build.json",
            "checker_cache_manifest_artifact": operator_root + r"\cache.json",
            "checker_image_build_log": operator_root + r"\build.log",
            "controller_entrypoint_source": operator_root + r"\controller.py",
            "isolation_probe_report": operator_root + r"\probe.json",
            "isolation_probe_artifacts_dir": operator_root + r"\probe-artifacts",
            "sandbox_command_argv": [
                operator_root + r"\docker.exe", operator_root_forward,
            ],
            "sandbox_cleanup_argv": [operator_root_forward + "/cleanup"],
            "filesystem_network_process_attestation": operator_root + r"\isolation.txt",
            "controller_worker_separation_attestation": {
                "receipt": operator_root + r"\separation.json"
            },
        })
        packed = prepare.sealed_config_for_pack(config)
        packed_text = json.dumps(packed, sort_keys=True)
        self.assertNotIn("operator-private", packed_text)
        self.assertEqual(
            prepare.sealed_config_for_pack(packed), packed,
            "portable config normalization must be idempotent",
        )
        self.assertEqual(packed["source_files_manifest"], "SEALED/source_manifest.json")
        self.assertTrue(
            packed["execution_adapter"]["runtime_executable"].startswith("HOST-BOUND/")
        )
        self.assertEqual(
            packed["execution_adapter"]["provider_runtime"]["auth_source_path"],
            "OPERATOR-SECRET/provider-auth-source",
        )

    @unittest.skipUnless(shutil.which("git"), "Git is unavailable")
    def test_git_object_proof_is_pack_only_and_tamper_evident(self) -> None:
        def git(repository: Path, *args: str, input_bytes: bytes | None = None) -> bytes:
            process = subprocess.run(
                [shutil.which("git"), *args], cwd=repository, input=input_bytes,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            )
            self.assertEqual(
                process.returncode, 0, process.stderr.decode(errors="replace")
            )
            return process.stdout

        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "source"
            repository.mkdir()
            git(repository, "init", "-q")
            git(repository, "config", "user.name", "Excluded Fixture")
            git(repository, "config", "user.email", "excluded-fixture.invalid")
            anchor_rel = "evaluation/target-drift-v2/public-anchor.json"
            anchor_path = repository / Path(anchor_rel)
            anchor_path.parent.mkdir(parents=True)
            anchor_bytes = b'{"fixture":"git-object-membership-only"}\n'
            anchor_path.write_bytes(anchor_bytes)
            git(repository, "add", anchor_rel)
            git(repository, "commit", "-q", "-m", "fixture anchor")
            anchor_commit = git(repository, "rev-parse", "HEAD").decode().strip()
            (repository / "later.txt").write_text("later\n", encoding="utf-8")
            git(repository, "add", "later.txt")
            git(repository, "commit", "-q", "-m", "fixture later commit")
            current_commit = git(repository, "rev-parse", "HEAD").decode().strip()

            object_ids = git(repository, "rev-list", current_commit).decode().splitlines()
            object_ids.append(git(
                repository, "rev-parse", f"{anchor_commit}^{{tree}}"
            ).decode().strip())
            for prefix in (
                "evaluation", "evaluation/target-drift-v2",
                "evaluation/target-drift-v2/public-anchor.json",
            ):
                object_ids.append(git(
                    repository, "rev-parse", f"{anchor_commit}:{prefix}"
                ).decode().strip())
            proof = git(
                repository, "pack-objects", "--stdout",
                input_bytes=("\n".join(object_ids) + "\n").encode("ascii"),
            )
            anchor = {
                "anchor_git_commit": anchor_commit,
                "anchor_repository_path": anchor_rel,
            }
            prepare.validate_git_object_proof(
                proof, anchor, anchor_bytes, current_commit
            )
            with self.assertRaises(SystemExit):
                prepare.validate_git_object_proof(
                    proof, anchor, anchor_bytes + b"tamper", current_commit
                )

    def test_run_manifest_requires_exact_cartesian_schedule_and_variant_parity(self) -> None:
        config = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        cases = [
            {
                "case_id": f"case-{case_index}",
                "source_faithful_requirement": f"faithful-{case_index}",
                "injected_drift_requirement": f"drift-{case_index}",
            }
            for case_index in range(30)
        ]
        runs = []
        for case_index, case in enumerate(cases):
            for replicate in range(5):
                variant = prepare.requirement_variant(case_index, replicate)
                for condition in prepare.CONDITIONS:
                    runs.append({
                        "run_id": (
                            f"{case['case_id']}--{condition}--replicate-{replicate}"
                        ),
                        "case_id": case["case_id"],
                        "condition": condition,
                        "replicate": replicate,
                        "prompt_template": config["conditions"][condition][
                            "prompt_template"
                        ],
                        "requirement_variant": variant,
                        "proposed_requirement": case[f"{variant}_requirement"],
                        "status": "sealed_unrun",
                        "presentation_order": len(runs),
                    })
        agent_cases = {"cases": cases}
        run_manifest = {"runs": runs}
        prepare.validate_run_manifest_schedule(config, agent_cases, run_manifest)

        duplicated = json.loads(json.dumps(run_manifest))
        duplicated["runs"][-1] = dict(duplicated["runs"][0])
        duplicated["runs"][-1]["presentation_order"] = 449
        with self.assertRaises(SystemExit):
            prepare.validate_run_manifest_schedule(config, agent_cases, duplicated)

        wrong_variant = json.loads(json.dumps(run_manifest))
        first = wrong_variant["runs"][0]
        first["requirement_variant"] = "source_faithful"
        first["proposed_requirement"] = cases[0]["source_faithful_requirement"]
        with self.assertRaises(SystemExit):
            prepare.validate_run_manifest_schedule(config, agent_cases, wrong_variant)

    def test_agent_case_order_is_bound_to_frozen_challenge_order(self) -> None:
        source_sha256 = "a" * 64
        challenges = {
            "cases": [
                {
                    "id": f"case-{index}",
                    "source_id": "source-a",
                    "source_sha256": source_sha256,
                    "source_locator": f"page {index + 1}",
                }
                for index in range(30)
            ]
        }
        paired = {
            "common_template": (
                "The proposed Lean target assigns '{{FIELD}}' '{{VALUE}}'."
            ),
            "cases": [
                {
                    "case_id": f"case-{index}",
                    "field": "contract",
                    "source_faithful_value": f"faithful-{index}",
                    "injected_drift_value": f"drift-{index}",
                }
                for index in range(30)
            ],
        }
        sources = {
            "sources": [{"source_id": "source-a", "sha256": source_sha256}]
        }
        paired_by_id = {entry["case_id"]: entry for entry in paired["cases"]}
        agent_cases = {
            "cases": [
                prepare.sanitized_case(
                    case, sources["sources"][0], paired_by_id[case["id"]],
                    paired["common_template"],
                )
                for case in challenges["cases"]
            ]
        }
        prepare.validate_agent_case_projection(
            challenges, paired, sources, agent_cases
        )
        reordered = json.loads(json.dumps(agent_cases))
        reordered["cases"][0], reordered["cases"][1] = (
            reordered["cases"][1], reordered["cases"][0]
        )
        with self.assertRaises(SystemExit):
            prepare.validate_agent_case_projection(
                challenges, paired, sources, reordered
            )

    def test_method_amendment_is_config_bound_and_pack_tamper_evident(self) -> None:
        config = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        amendment_path = ROOT / config["method_amendment"]
        amendment_bytes = amendment_path.read_bytes()
        protocol_bytes = (ROOT / config["protocol"]).read_bytes()
        script_path = ROOT / config["analysis"]["script"]
        script_bytes = script_path.read_bytes()
        test_script_path = ROOT / config["analysis"]["test_script"]
        test_script_bytes = test_script_path.read_bytes()
        config["analysis"]["script_sha256"] = prepare.sha256_bytes(script_bytes)
        self.assertEqual(
            prepare.validate_method_amendment(
                config,
                require_hashes=True,
                amendment_bytes=amendment_bytes,
                protocol_bytes=protocol_bytes,
                analysis_script_bytes=script_bytes,
                analysis_test_bytes=test_script_bytes,
            ),
            amendment_bytes,
        )
        changed_config = json.loads(json.dumps(config))
        changed_config["method_amendment_sha256"] = "0" * 64
        self.assertNotEqual(
            prepare.normalized_config_for_digest(config),
            prepare.normalized_config_for_digest(changed_config),
        )
        with self.assertRaises(SystemExit):
            prepare.validate_method_amendment(
                changed_config,
                require_hashes=True,
                amendment_bytes=amendment_bytes,
                protocol_bytes=protocol_bytes,
                analysis_script_bytes=script_bytes,
                analysis_test_bytes=test_script_bytes,
            )
        wrong_path_config = json.loads(json.dumps(config))
        wrong_path_config["method_amendment"] = "evaluation/target-drift-v2/protocol.json"
        with self.assertRaises(SystemExit):
            prepare.validate_method_amendment(
                wrong_path_config,
                require_hashes=False,
                amendment_bytes=amendment_bytes,
                protocol_bytes=protocol_bytes,
                analysis_script_bytes=script_bytes,
                analysis_test_bytes=test_script_bytes,
            )
        changed_analysis = json.loads(json.dumps(config))
        changed_analysis["analysis"]["primary_interval"] = "population bootstrap"
        with self.assertRaises(SystemExit):
            prepare.validate_method_amendment(
                changed_analysis,
                require_hashes=False,
                amendment_bytes=amendment_bytes,
                protocol_bytes=protocol_bytes,
                analysis_script_bytes=script_bytes,
                analysis_test_bytes=test_script_bytes,
            )
        outcome_tamper = json.loads(amendment_bytes.decode("utf-8"))
        outcome_tamper["timing_and_claim_boundary"][
            "primary_model_outcomes_observed"
        ] = True
        with self.assertRaises(SystemExit):
            prepare.validate_method_amendment(
                config,
                require_hashes=False,
                amendment_bytes=prepare.canonical_json_bytes(outcome_tamper),
                protocol_bytes=protocol_bytes,
                analysis_script_bytes=script_bytes,
                analysis_test_bytes=test_script_bytes,
            )
        binding_tamper = json.loads(amendment_bytes.decode("utf-8"))
        binding_tamper["bindings"]["analysis_script_after_amendment"][
            "sha256"
        ] = "0" * 64
        with self.assertRaises(SystemExit):
            prepare.validate_method_amendment(
                config,
                require_hashes=False,
                amendment_bytes=prepare.canonical_json_bytes(binding_tamper),
                protocol_bytes=protocol_bytes,
                analysis_script_bytes=script_bytes,
                analysis_test_bytes=test_script_bytes,
            )
        with self.assertRaises(SystemExit):
            prepare.validate_method_amendment(
                config,
                require_hashes=True,
                amendment_bytes=amendment_bytes,
                protocol_bytes=protocol_bytes + b" ",
                analysis_script_bytes=script_bytes,
                analysis_test_bytes=test_script_bytes,
            )
        with self.assertRaises(SystemExit):
            prepare.validate_method_amendment(
                config,
                require_hashes=True,
                amendment_bytes=amendment_bytes,
                protocol_bytes=protocol_bytes,
                analysis_script_bytes=script_bytes + b" ",
                analysis_test_bytes=test_script_bytes,
            )
        with self.assertRaises(SystemExit):
            prepare.validate_method_amendment(
                config,
                require_hashes=True,
                amendment_bytes=amendment_bytes,
                protocol_bytes=protocol_bytes,
                analysis_script_bytes=script_bytes,
                analysis_test_bytes=test_script_bytes + b" ",
            )
        with tempfile.TemporaryDirectory() as directory:
            pack = Path(directory)
            (pack / "protocol.json").write_bytes(protocol_bytes)
            code = pack / "execution_code"
            code.mkdir()
            (code / "analyze_target_drift_execution.py").write_bytes(script_bytes)
            (code / "test_target_drift_analysis.py").write_bytes(test_script_bytes)
            execution_code = {
                "analyze_target_drift_execution.py": script_bytes,
                "test_target_drift_analysis.py": test_script_bytes,
            }
            with self.assertRaises(SystemExit):
                prepare.packed_method_amendment_bytes(pack, config, execution_code)
            packed_amendment = pack / "method-amendment.json"
            packed_amendment.write_bytes(amendment_bytes)
            self.assertEqual(
                prepare.packed_method_amendment_bytes(pack, config, execution_code),
                amendment_bytes,
            )
            packed_amendment.write_bytes(amendment_bytes + b" ")
            with self.assertRaises(SystemExit):
                prepare.packed_method_amendment_bytes(pack, config, execution_code)

    def test_excluded_checker_fixture_contract_is_schema_valid_but_not_production(self) -> None:
        config = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        checker = config["posthoc_checker"]
        contract = ROOT / checker["contract"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            artifacts = root / "artifacts"
            artifacts.mkdir()
            (artifacts / "excluded-fixture-record.txt").write_text(
                "nonexperimental fixture\n", encoding="utf-8"
            )
            probe = root / "probe.json"
            checker.update({
                "contract_sha256": prepare.sha256_file(contract),
                "mode": "excluded_fixture",
                "checker_id": "excluded-local-checker-fixture",
                "checker_version": "1",
                "runtime_id": "host-python-fixture",
                "runtime_version": "1",
                "container_image_digest": "sha256:" + "f" * 64,
                "isolation_probe_artifacts_dir": str(artifacts),
                "isolation_probe_report": str(probe),
                "isolation_probe_runner_sha256": prepare.sha256_file(
                    ROOT / checker["isolation_probe_runner_path"]
                ),
                "sandbox_command_argv": [
                    "fixture", "{{CHECKER_REQUEST_PATH}}", "{{BASE_SNAPSHOT_PATH}}",
                    "{{PATCH_PATH}}", "{{CHECKER_OUTPUT_DIR}}", "{{CHECKER_RESPONSE_PATH}}",
                    "{{CIDFILE}}", "{{CHECKER_ATTEMPT_LABEL}}", "{{CHECKER_IMAGE_DIGEST}}",
                ],
                "sandbox_cleanup_argv": ["fixture-cleanup", "{{CIDFILE}}"],
                "sandbox_inspect_argv": ["fixture-inspect", "{{CIDFILE}}"],
                "sandbox_cleanup_by_label_argv": [
                    "fixture-cleanup-label", "{{CHECKER_ATTEMPT_LABEL}}"
                ],
                "sandbox_inspect_by_label_argv": [
                    "fixture-inspect-label", "{{CHECKER_ATTEMPT_LABEL}}"
                ],
                "inspect_absent_exit_code": 3,
                "budgets": {
                    "wall_clock_seconds": 10, "memory_mb": 128, "pids_limit": 32,
                    "cpus": 1, "maximum_output_bytes": 4096,
                    "maximum_response_bytes": 4096,
                },
            })
            checker["runtime_config_sha256"] = prepare.checker_runtime_config_sha256(config)
            probe.write_text(json.dumps({
                "schema_version": 1,
                "suite_id": config["suite_id"],
                "status": "excluded_fixture_nonexperimental",
                "checker_id": checker["checker_id"],
                "checker_version": checker["checker_version"],
                "container_image_digest": checker["container_image_digest"],
                "checker_runtime_config_sha256": checker["runtime_config_sha256"],
                "runtime_command_template_sha256": prepare.sha256_bytes(
                    prepare.canonical_json_bytes(checker["sandbox_command_argv"])
                ),
                "probe_runner_sha256": checker["isolation_probe_runner_sha256"],
                "probes": {},
                "artifact_manifest": prepare.probe_artifact_manifest(
                    prepare.probe_artifact_bytes(artifacts)
                ),
            }), encoding="utf-8")
            checker["isolation_probe_report_sha256"] = prepare.sha256_file(probe)
            prepare.validate_checker_contract(config, require_hashes=True)
            checker["sandbox_command_argv"].insert(1, "--detach=true")
            with self.assertRaises(SystemExit):
                prepare.validate_checker_contract(config, require_hashes=True)
            checker["sandbox_command_argv"].remove("--detach=true")
            checker["mode"] = "production"
            with self.assertRaises(SystemExit):
                prepare.validate_checker_contract(config, require_hashes=True)

    def test_checker_runtime_digest_binds_command_budget_and_code(self) -> None:
        config = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        checker = config["posthoc_checker"]
        checker.update({
            "checker_id": "checker", "checker_version": "1",
            "mode": "excluded_fixture", "runtime_id": "runtime", "runtime_version": "1",
            "sandbox_command_argv": ["run", "{{CIDFILE}}"],
            "sandbox_cleanup_argv": ["clean", "{{CIDFILE}}"],
            "sandbox_inspect_argv": ["inspect", "{{CIDFILE}}"],
            "sandbox_cleanup_by_label_argv": ["clean-label", "{{CHECKER_ATTEMPT_LABEL}}"],
            "sandbox_inspect_by_label_argv": ["inspect-label", "{{CHECKER_ATTEMPT_LABEL}}"],
            "inspect_absent_exit_code": 3,
            "container_image_digest": "sha256:" + "f" * 64,
            "filesystem_network_process_attestation": "x" * 20,
            "controller_worker_separation_attestation": "y" * 20,
            "budgets": {"wall_clock_seconds": 1, "memory_mb": 1, "pids_limit": 1,
                        "cpus": 1, "maximum_output_bytes": 1,
                        "maximum_response_bytes": 1},
            "worker_command_prefix": [], "cache_prelude_argv": [],
        })
        baseline = prepare.checker_runtime_config_sha256(config)
        checker["budgets"]["memory_mb"] = 2
        self.assertNotEqual(baseline, prepare.checker_runtime_config_sha256(config))

    def test_rendered_checker_argv_must_preserve_frozen_template(self) -> None:
        template = ["docker", "run", "--label", "{{CHECKER_ATTEMPT_LABEL}}", "image"]
        self.assertTrue(prepare.rendered_argv_matches_template(
            template, ["docker", "run", "--label", "ABRL-PROBE-123", "image"]
        ))
        self.assertFalse(prepare.rendered_argv_matches_template(
            template, ["docker", "run", "--privileged", "ABRL-PROBE-123", "image"]
        ))

    def test_production_preflight_rejects_noncanonical_launcher_argv_first(self) -> None:
        config = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        checker = config["posthoc_checker"]
        checker.update({
            "mode": "production", "checker_id": "checker", "checker_version": "1",
            "runtime_id": "docker", "runtime_version": "client=x;server=x;os=linux",
            "host_launcher_sha256": prepare.sha256_file(
                ROOT / checker["host_launcher_path"]
            ),
            "host_python_executable": sys.executable,
            "host_python_executable_sha256": "a" * 64,
            "container_runtime_executable": "C:/not-docker/fabricated-runtime.exe",
            "container_runtime_executable_sha256": "b" * 64,
            "runtime_version_output_sha256": "c" * 64,
            "runtime_signature_output_sha256": "f" * 64,
            "daemon_identity_output_sha256": "d" * 64,
            "checker_cache_manifest_sha256": "9" * 64,
            "container_image_digest": "sha256:" + "e" * 64,
            "controller_uid": "0:0", "worker_uid": "10002:10002",
            "budgets": {
                "wall_clock_seconds": 10, "memory_mb": 256, "pids_limit": 32,
                "cpus": 1, "maximum_output_bytes": 4096,
                "maximum_response_bytes": 4096,
            },
        })
        launcher = ROOT / checker["host_launcher_path"]
        checker["worker_command_prefix"] = checker_launcher.worker_command_prefix(checker)
        checker.update(checker_launcher.command_templates(checker, launcher))
        checker["sandbox_command_argv"].insert(-1, "--privileged")
        with self.assertRaises(SystemExit):
            prepare.validate_checker_runtime_preflight(config)

    def test_aggregate_digest_changes_for_every_sealed_component(self) -> None:
        config = {
            "sealed_agent_view": {"aggregate_sha256": "UNSET"},
            "model": {"immutable_version": "v1"},
        }
        components = prepare.digest_components(
            config,
            {"cases": []},
            {"runs": []},
            b"challenges",
            b"paired requirements",
            b"protocol",
            b"method amendment",
            b"missing-run policy",
            b"sources",
            {"source.pdf": b"pdf"},
            b"rubric",
            b"policy",
            b"adapter contract",
            b"checker contract",
            b"checker probe",
            {"probe.json": b"probe artifact"},
            {"checker-image.Containerfile": b"recipe"},
            b"grader prompt",
            b"text-only prompt",
            {condition: condition.encode() for condition in prepare.CONDITIONS},
            {"runner.py": b"runner"},
            {"self-attested-completion.json": b"human review"},
        )
        self.assertIn("method-amendment.json", components)
        baseline, _ = prepare.aggregate_digest(components)
        for name in components:
            changed = dict(components)
            changed[name] += b"x"
            digest, _ = prepare.aggregate_digest(changed)
            self.assertNotEqual(digest, baseline, name)

    def test_preseal_and_frozen_status_have_the_same_normalized_config(self) -> None:
        preseal = {
            "execution_status": "preseal_ready",
            "sealed_agent_view": {"aggregate_sha256": "UNSET"},
            "unresolved_fields": ["sealed_agent_view.aggregate_sha256"],
        }
        frozen = {
            "execution_status": "frozen_ready",
            "sealed_agent_view": {"aggregate_sha256": "a" * 64},
            "unresolved_fields": [],
        }
        self.assertEqual(
            prepare.normalized_config_for_digest(preseal),
            prepare.normalized_config_for_digest(frozen),
        )

    def test_every_source_revision_has_a_frozen_hash(self) -> None:
        source_manifest = json.loads(
            (ROOT / "evaluation" / "target-drift-v1" / "source-files.template.json")
            .read_text(encoding="utf-8")
        )
        for source in source_manifest["sources"]:
            digest = source["sha256"]
            self.assertEqual(len(digest), 64)
            self.assertTrue(all(character in "0123456789abcdef" for character in digest))


if __name__ == "__main__":
    unittest.main()
