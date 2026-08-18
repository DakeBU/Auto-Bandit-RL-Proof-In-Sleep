#!/usr/bin/env python3
"""Tests for the result-free target-drift execution preparation layer."""

from __future__ import annotations

import json
import sys
import unittest
import tempfile
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import launch_target_drift_checker_container as checker_launcher  # noqa: E402


class TargetDriftExecutionTest(unittest.TestCase):
    def test_template_and_prompts_validate_while_unfrozen(self) -> None:
        prepare.check_template(
            ROOT / "evaluation" / "target-drift-v1" / "execution-template.json"
        )

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
        )
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
