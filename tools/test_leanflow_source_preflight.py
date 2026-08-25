#!/usr/bin/env python3
"""Tests for the LeanFlow pinned-source preflight workflow and validator."""

from __future__ import annotations

import ast
import copy
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
CONTRACT = ROOT / "evaluation" / "target-drift-v2" / "leanflow-real-adapter-contract.json"
WORKFLOW = ROOT / ".github" / "workflows" / "leanflow-source-preflight.yml"

import sys

sys.path.insert(0, str(TOOLS))
import validate_leanflow_source_preflight as validator  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class LeanFlowSourcePreflightValidatorTests(unittest.TestCase):
    def load_contract(self) -> dict:
        return json.loads(CONTRACT.read_text(encoding="utf-8"))

    def build_artifacts(self, root: Path) -> tuple[Path, Path, dict, list[dict]]:
        contract = self.load_contract()
        source = contract["source_identity"]
        response = {
            "schema_version": 1,
            "suite_id": contract["suite_id"],
            "comparator_id": contract["comparator_id"],
            "adapter_id": validator.EXPECTED_ADAPTER_ID,
            "adapter_version": validator.EXPECTED_ADAPTER_VERSION,
            "status": validator.EXPECTED_STATUS,
            "result_eligible": False,
            "production_eligible": False,
            "adapter_provider_client_called": False,
            "adapter_started_leanflow": False,
            "adapter_credential_read_path_present": False,
            "adapter_network_client_path_present": False,
            "local_git_executable_pre_frozen": False,
            "os_network_isolation_attested": False,
            "formalization_outcome_reported": False,
            "production_gate_passed": False,
            "contract_sha256": sha256(CONTRACT),
            "source_identity": {
                "repository_commit": source["repository_commit"],
                "repository_tree_sha1": source["repository_tree_sha1"],
                "project_version": source["project_version"],
                "python_requires": source["python_requires"],
                "lock_sha256": source["lock_sha256"],
                "pinned_file_count": len(source["pinned_files"]),
            },
            "local_preflight": {
                "git_executable_sha256": "9" * 64,
                "git_identity_probe_count": 2,
                "model_invocations": 0,
                "git_executable_pre_frozen": False,
                "git_os_level_behavior_attested": False,
            },
            "gates": copy.deepcopy(validator.EXPECTED_GATE_VALUES),
            "unmet_production_gates": copy.deepcopy(
                contract["unmet_production_gates"],
            ),
        }
        trace = [
            {"sequence": 0, "kind": "preflight_started"},
            {
                "sequence": 1,
                "kind": "contract_validated",
                "contract_sha256": sha256(CONTRACT),
            },
            {
                "sequence": 2,
                "kind": "local_git_identity_validated",
                "repository_commit": source["repository_commit"],
                "repository_tree_sha1": source["repository_tree_sha1"],
                "git_identity_probe_count": 2,
            },
            {
                "sequence": 3,
                "kind": "pinned_source_files_validated",
                "pinned_file_count": len(source["pinned_files"]),
                "lock_sha256": source["lock_sha256"],
            },
            {
                "sequence": 4,
                "kind": "pinned_cli_policy_audited",
                "clean_room_status": contract["clean_room_audit"]["status"],
                "no_web_overlay_frozen": False,
                "provider_only_network_containment_frozen": False,
            },
            {
                "sequence": 5,
                "kind": "preflight_summary",
                "result_eligible": False,
                "adapter_provider_client_called": False,
                "adapter_started_leanflow": False,
                "adapter_credential_read_path_present": False,
                "adapter_network_client_path_present": False,
                "local_git_executable_pre_frozen": False,
                "os_network_isolation_attested": False,
                "formalization_outcome_reported": False,
                "production_gate_passed": False,
            },
        ]
        response_path = root / "source-preflight-response.json"
        trace_path = root / "source-preflight-trace.jsonl"
        response_path.write_text(
            json.dumps(response, indent=2, sort_keys=True) + "\n", encoding="utf-8",
        )
        trace_path.write_text(
            "".join(json.dumps(event, sort_keys=True) + "\n" for event in trace),
            encoding="utf-8",
        )
        return response_path, trace_path, response, trace

    def test_tracked_workflow_has_exact_result_free_source_boundary(self) -> None:
        observed = validator.validate_workflow(WORKFLOW)
        self.assertEqual(
            observed["path"], ".github/workflows/leanflow-source-preflight.yml",
        )
        self.assertEqual(observed["sha256"], sha256(WORKFLOW))
        text = WORKFLOW.read_text(encoding="utf-8")
        self.assertIn("0 model calls; not results", text)
        self.assertIn("remote remove origin", text)
        self.assertNotIn("${{ secrets.", text)
        self.assertEqual(
            sha256(WORKFLOW), validator.EXPECTED_WORKFLOW_SHA256,
        )
        self.assertIn(
            f"actions/checkout@{validator.CHECKOUT_ACTION_SHA} # v6", text,
        )
        self.assertIn(
            f"actions/upload-artifact@{validator.UPLOAD_ACTION_SHA} # v4", text,
        )
        trusted_main_condition = (
            "if: github.repository == 'DakeBU/Auto-Bandit-RL-Proof-In-Sleep' && "
            "github.event_name == 'push' && github.ref == 'refs/heads/main'"
        )
        self.assertEqual(text.count(trusted_main_condition), 2)

    def test_workflow_is_git_normalized_to_lf_and_crlf_bytes_fail(self) -> None:
        attribute_line = (
            ".github/workflows/leanflow-source-preflight.yml text eol=lf"
        )
        self.assertIn(
            attribute_line,
            (ROOT / ".gitattributes").read_text(encoding="utf-8").splitlines(),
        )
        if (ROOT / ".git").exists():
            attributes = subprocess.run(
                [
                    "git", "check-attr", "text", "eol", "--",
                    ".github/workflows/leanflow-source-preflight.yml",
                ],
                cwd=ROOT,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding="utf-8",
            ).stdout
            self.assertIn("text: set", attributes)
            self.assertIn("eol: lf", attributes)
        canonical = WORKFLOW.read_bytes()
        self.assertNotIn(b"\r\n", canonical)
        self.assertEqual(
            hashlib.sha256(canonical).hexdigest(),
            validator.EXPECTED_WORKFLOW_SHA256,
        )
        with tempfile.TemporaryDirectory() as tmp:
            crlf_path = Path(tmp) / "workflow.yml"
            crlf_path.write_bytes(canonical.replace(b"\n", b"\r\n"))
            with self.assertRaisesRegex(
                validator.ValidationError, "exact trusted-main snapshot",
            ):
                validator.validate_workflow(crlf_path)

    def test_independent_validator_freezes_commit_tree_lock_and_file_bytes(self) -> None:
        contract = self.load_contract()
        validator.validate_contract_boundary(contract)
        mutations = (
            ("repository_commit", "0" * 40),
            ("repository_tree_sha1", "1" * 40),
            ("lock_sha256", "2" * 64),
        )
        for field, value in mutations:
            mutated = copy.deepcopy(contract)
            mutated["source_identity"][field] = value
            with self.subTest(field=field), self.assertRaises(
                validator.ValidationError,
            ):
                validator.validate_contract_boundary(mutated)
        mutated = copy.deepcopy(contract)
        mutated["source_identity"]["pinned_files"][0]["bytes"] += 1
        with self.assertRaises(validator.ValidationError):
            validator.validate_contract_boundary(mutated)

    def test_valid_nonresult_response_and_trace_emit_nonresult_attestation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            response_path, trace_path, unused_response, unused_trace = (
                self.build_artifacts(root)
            )
            attestation = validator.validate_artifacts(
                CONTRACT, response_path, trace_path, WORKFLOW,
            )
            self.assertEqual(
                attestation["artifact_kind"],
                "leanflow_pinned_source_preflight_not_evaluation_results",
            )
            self.assertFalse(attestation["result_eligible"])
            self.assertFalse(attestation["production_eligible"])
            self.assertFalse(attestation["leanflow_started"])
            self.assertFalse(attestation["provider_client_called"])
            self.assertFalse(attestation["formalization_outcome_reported"])
            self.assertEqual(attestation["model_invocations"], 0)
            self.assertEqual(attestation["provenance"]["mode"], "local")
            self.assertEqual(
                attestation["provenance"]["status"], "local_non_evidence",
            )
            self.assertFalse(attestation["provenance"]["ci_evidence_eligible"])
            self.assertFalse(
                attestation["provenance"]["main_push_artifact_upload_permitted"],
            )
            self.assertEqual(
                attestation["artifact_sha256"]["adapter"],
                sha256(TOOLS / "leanflow_target_drift_adapter.py"),
            )
            self.assertEqual(
                attestation["artifact_sha256"]["validator"],
                sha256(TOOLS / "validate_leanflow_source_preflight.py"),
            )
            self.assertEqual(
                attestation["source_identity"]["repository_commit"],
                validator.EXPECTED_COMMIT,
            )

    def test_result_field_or_positive_result_flag_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            response_path, trace_path, response, unused_trace = self.build_artifacts(root)
            for field, value in (("result_eligible", True), ("score", 1.0)):
                mutated = copy.deepcopy(response)
                mutated[field] = value
                response_path.write_text(
                    json.dumps(mutated, sort_keys=True) + "\n", encoding="utf-8",
                )
                with self.subTest(field=field), self.assertRaises(
                    validator.ValidationError,
                ):
                    validator.validate_artifacts(
                        CONTRACT, response_path, trace_path, WORKFLOW,
                    )

    def test_trace_order_fields_and_cross_hash_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            response_path, trace_path, unused_response, trace = self.build_artifacts(root)
            mutations = []
            wrong_order = copy.deepcopy(trace)
            wrong_order[2]["sequence"] = 99
            mutations.append(wrong_order)
            extra_field = copy.deepcopy(trace)
            extra_field[-1]["proof"] = "invented"
            mutations.append(extra_field)
            wrong_hash = copy.deepcopy(trace)
            wrong_hash[1]["contract_sha256"] = "0" * 64
            mutations.append(wrong_hash)
            for index, mutated in enumerate(mutations):
                trace_path.write_text(
                    "".join(json.dumps(event, sort_keys=True) + "\n"
                            for event in mutated),
                    encoding="utf-8",
                )
                with self.subTest(index=index), self.assertRaises(
                    validator.ValidationError,
                ):
                    validator.validate_artifacts(
                        CONTRACT, response_path, trace_path, WORKFLOW,
                    )

    def test_workflow_exact_bytes_reject_every_requested_bypass(self) -> None:
        original = WORKFLOW.read_text(encoding="utf-8")
        mutations = (
            original + "\n# leanflow doctor\n",
            original + "\n# curl https://example.invalid\n",
            original.replace(validator.EXPECTED_COMMIT, "0" * 40),
            original.replace("persist-credentials: false", "persist-credentials: true"),
            original + "\n# ${{ secrets.PROVIDER_KEY }}\n",
            original + "\n# ${{ secrets['X'] }}\n",
            original + "\n# ${{ github.token }}\n",
            original + "\n# python -c \"import urllib.request\"\n",
            original + "\n# urllib.request.urlopen('https://example.invalid')\n",
            original + "\nextra-job:\n  runs-on: ubuntu-latest\n",
            original + "\n      - name: Extra step\n        run: true\n",
            original.replace("jobs:\n", "env:\n  EXTRA_ENV: bypass\njobs:\n", 1),
            original + "\nrun: echo bypass\n",
            original.replace(
                validator.CHECKOUT_ACTION_SHA, "1" * 40,
            ),
            original.replace(
                validator.UPLOAD_ACTION_SHA, "2" * 40,
            ),
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "workflow.yml"
            for index, text in enumerate(mutations):
                path.write_text(text, encoding="utf-8")
                with self.subTest(index=index), self.assertRaises(
                    validator.ValidationError,
                ):
                    validator.validate_workflow(path)

    def test_github_provenance_binds_context_but_is_not_self_authenticating(self) -> None:
        common = {
            "github_sha": "a" * 40,
            "github_run_id": "123456",
            "github_run_attempt": "2",
            "github_event_name": "push",
            "github_ref": "refs/heads/main",
            "github_workflow": validator.EXPECTED_WORKFLOW_NAME,
            "github_workflow_ref": (
                f"{validator.EXPECTED_ABRL_GITHUB_REPOSITORY}/.github/workflows/"
                "leanflow-source-preflight.yml@"
                "refs/heads/main"
            ),
            "github_repository": validator.EXPECTED_ABRL_GITHUB_REPOSITORY,
            "github_server_url": "https://github.com",
        }
        provenance = validator.build_provenance("github-actions", **common)
        self.assertEqual(provenance["abrl_github_sha"], "a" * 40)
        self.assertEqual(provenance["github_run_id"], "123456")
        self.assertEqual(provenance["github_run_attempt"], "2")
        self.assertEqual(provenance["github_event_name"], "push")
        self.assertEqual(provenance["github_ref"], "refs/heads/main")
        self.assertEqual(
            provenance["github_workflow"], validator.EXPECTED_WORKFLOW_NAME,
        )
        self.assertEqual(
            provenance["github_run_url"],
            (
                "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
                "actions/runs/123456"
            ),
        )
        self.assertTrue(provenance["main_push_artifact_upload_permitted"])
        self.assertFalse(provenance["ci_evidence_eligible"])
        self.assertIsNone(provenance["artifact_digest"])
        self.assertEqual(len(provenance["required_external_verification"]), 3)
        with tempfile.TemporaryDirectory() as tmp:
            response_path, trace_path, unused_response, unused_trace = (
                self.build_artifacts(Path(tmp))
            )
            attestation = validator.validate_artifacts(
                CONTRACT, response_path, trace_path, WORKFLOW, provenance,
            )
            self.assertEqual(attestation["provenance"], provenance)
            self.assertEqual(
                attestation["provenance"]["abrl_github_sha"], "a" * 40,
            )

        for event, ref in (
            ("pull_request", "refs/pull/7/merge"),
            ("workflow_dispatch", "refs/heads/main"),
        ):
            check_only = validator.build_provenance(
                "github-actions",
                **{**common, "github_event_name": event, "github_ref": ref},
            )
            self.assertEqual(check_only["status"], "check_only_non_evidence")
            self.assertFalse(check_only["main_push_artifact_upload_permitted"])
            self.assertFalse(check_only["ci_evidence_eligible"])
            self.assertEqual(check_only["required_external_verification"], [])

        fork = {**common, "github_repository": "fork-owner/Auto-Bandit-RL-Proof-In-Sleep"}
        fork["github_workflow_ref"] = (
            "fork-owner/Auto-Bandit-RL-Proof-In-Sleep/.github/workflows/"
            "leanflow-source-preflight.yml@refs/heads/main"
        )
        with self.assertRaisesRegex(
            validator.ValidationError, "trusted ABRL repository",
        ):
            validator.build_provenance("github-actions", **fork)

    def test_local_provenance_rejects_injected_github_context(self) -> None:
        local = validator.build_provenance()
        self.assertEqual(local["status"], "local_non_evidence")
        self.assertFalse(local["ci_evidence_eligible"])
        self.assertEqual(validator.validate_provenance(local), local)
        with self.assertRaises(validator.ValidationError):
            validator.build_provenance("local", github_sha="a" * 40)

    def test_provenance_exact_schema_and_semantics_fail_closed(self) -> None:
        local = validator.build_provenance()
        github = validator.build_provenance(
            "github-actions",
            github_sha="a" * 40,
            github_run_id="123456",
            github_run_attempt="2",
            github_event_name="push",
            github_ref="refs/heads/main",
            github_workflow=validator.EXPECTED_WORKFLOW_NAME,
            github_workflow_ref=(
                f"{validator.EXPECTED_ABRL_GITHUB_REPOSITORY}/.github/workflows/"
                "leanflow-source-preflight.yml@refs/heads/main"
            ),
            github_repository=validator.EXPECTED_ABRL_GITHUB_REPOSITORY,
            github_server_url="https://github.com",
        )
        self.assertEqual(validator.validate_provenance(github), github)

        mutations = []
        extra = copy.deepcopy(github)
        extra["unexpected"] = "forged"
        mutations.append(extra)
        missing = copy.deepcopy(github)
        missing.pop("nonclaim")
        mutations.append(missing)
        for field, value in (
            ("ci_evidence_eligible", True),
            ("artifact_digest", "0" * 64),
            ("status", "ci_evidence_verified"),
            ("github_repository", "fork-owner/abrl"),
            ("github_ref", "refs/heads/feature"),
            ("main_push_artifact_upload_permitted", False),
            ("required_external_verification", []),
            ("github_run_url", "https://example.invalid/forged"),
        ):
            mutated = copy.deepcopy(github)
            mutated[field] = value
            mutations.append(mutated)
        bad_mode = copy.deepcopy(github)
        bad_mode["mode"] = "forged"
        mutations.append(bad_mode)
        local_digest = copy.deepcopy(local)
        local_digest["artifact_digest"] = "1" * 64
        mutations.append(local_digest)
        local_eligible = copy.deepcopy(local)
        local_eligible["ci_evidence_eligible"] = True
        mutations.append(local_eligible)

        for index, mutated in enumerate(mutations):
            with self.subTest(index=index), self.assertRaises(
                validator.ValidationError,
            ):
                validator.validate_provenance(mutated)

        with tempfile.TemporaryDirectory() as tmp:
            response_path, trace_path, unused_response, unused_trace = (
                self.build_artifacts(Path(tmp))
            )
            forged = copy.deepcopy(github)
            forged["ci_evidence_eligible"] = True
            with self.assertRaises(validator.ValidationError):
                validator.validate_artifacts(
                    CONTRACT, response_path, trace_path, WORKFLOW, forged,
                )

    def test_validator_has_no_subprocess_provider_or_network_import(self) -> None:
        source = (TOOLS / "validate_leanflow_source_preflight.py").read_text(
            encoding="utf-8",
        )
        tree = ast.parse(source)
        imports = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imports.update(alias.name.split(".", 1)[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imports.add(node.module.split(".", 1)[0])
        self.assertFalse(imports & {
            "anthropic", "httpx", "openai", "requests", "socket", "subprocess",
            "urllib",
        })

    def test_attestation_write_is_no_clobber(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            response_path, trace_path, unused_response, unused_trace = (
                self.build_artifacts(root)
            )
            attestation = validator.validate_artifacts(
                CONTRACT, response_path, trace_path, WORKFLOW,
            )
            output = root / "validation.json"
            validator.write_new_object(output, attestation)
            sentinel = output.read_bytes()
            with self.assertRaisesRegex(
                validator.ValidationError, "refusing to overwrite",
            ):
                validator.write_new_object(output, attestation)
            self.assertEqual(output.read_bytes(), sentinel)


if __name__ == "__main__":
    unittest.main()
