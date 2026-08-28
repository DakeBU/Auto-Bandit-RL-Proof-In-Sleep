import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).resolve().with_name("build_anonymous_iclr_supplement.py")
SPEC = importlib.util.spec_from_file_location("anonymous_supplement_builder", str(SCRIPT))
BUILDER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILDER)


class AnonymousSupplementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temp.name)
        cls.first = cls.root / "first.zip"
        cls.second = cls.root / "second.zip"
        cls.first_result = BUILDER.build_archive(
            cls.first, allow_missing_graph=True
        )
        cls.second_result = BUILDER.build_archive(
            cls.second, allow_missing_graph=True
        )

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_archive_is_reproducible(self):
        self.assertEqual(self.first.read_bytes(), self.second.read_bytes())
        self.assertEqual(self.first_result["sha256"], self.second_result["sha256"])

    def test_payload_is_stable_under_crlf_checkout_presentation(self):
        expected = BUILDER.build_payload(allow_missing_graph=True)
        original_read = BUILDER.read_regular

        def crlf_read(rel):
            data = original_read(rel)
            if not BUILDER.is_text_payload_path(rel):
                return data
            normalized = data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
            return normalized.replace(b"\n", b"\r\n")

        with mock.patch.object(BUILDER, "read_regular", side_effect=crlf_read):
            crlf_payload = BUILDER.build_payload(allow_missing_graph=True)
        self.assertEqual(expected, crlf_payload)
        self.assertTrue(all(
            b"\r" not in data
            for rel, data in expected.items()
            if BUILDER.is_text_payload_path(rel)
        ))

    def test_crlf_proof_graph_report_is_rebound_to_packaged_bytes(self):
        source_report = json.loads((
            BUILDER.REPO_ROOT / "research-wiki" / "proof-graph"
            / "benchmark_report.json"
        ).read_text(encoding="utf-8"))
        graph = {
            "schema_version": 1,
            "extraction": {
                "source": "compiled-environment",
                "dependency_semantics": "direct-constant-occurrence",
                "deterministic": True,
            },
            "status_vocabulary": [
                "compiled", "prototype", "partial", "planned", "blocked",
            ],
            "nodes": [],
            "edges": [],
            "module_imports": [],
            "counts": {
                "project_nodes": 0,
                "external_boundary_nodes": 0,
                "edges": 0,
                "module_imports": 0,
            },
        }
        graph_bytes = (
            json.dumps(graph, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8").replace(b"\n", b"\r\n")
        graph_path = self.root / "crlf-proof-graph.json"
        report_path = self.root / "crlf-proof-report.json"
        graph_path.write_bytes(graph_bytes)
        source_report["graph"]["counts"] = graph["counts"]
        source_report["graph"]["sha256"] = hashlib.sha256(graph_bytes).hexdigest()
        report_path.write_bytes((
            json.dumps(source_report, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8").replace(b"\n", b"\r\n"))

        payload = BUILDER.build_payload(graph_path, report_path)
        packaged_graph = payload[
            "evidence/proof-graph/current-proof-graph.json"
        ]
        packaged_report = json.loads(payload[
            "evidence/proof-graph/current-benchmark-report.json"
        ].decode("utf-8"))
        self.assertNotIn(b"\r", packaged_graph)
        self.assertEqual(
            packaged_report["graph"]["sha256"],
            hashlib.sha256(packaged_graph).hexdigest(),
        )

        first_archive = self.root / "graph-included-first.zip"
        second_archive = self.root / "graph-included-second.zip"
        first_result = BUILDER.build_archive(
            first_archive, graph_path, report_path
        )
        second_result = BUILDER.build_archive(
            second_archive, graph_path, report_path
        )
        self.assertEqual(first_archive.read_bytes(), second_archive.read_bytes())
        self.assertEqual(first_result["sha256"], second_result["sha256"])
        with zipfile.ZipFile(str(first_archive)) as archive:
            manifest = json.loads(archive.read(
                BUILDER.ARCHIVE_ROOT + "/ARTIFACT_MANIFEST.json"
            ))
        self.assertTrue(manifest["proof_graph"]["included"])
        destination = self.root / "graph-included-extracted"
        with zipfile.ZipFile(str(first_archive)) as archive:
            archive.extractall(str(destination))
        artifact = destination / BUILDER.ARCHIVE_ROOT
        verification = subprocess.run(
            [sys.executable, "artifact/verify_artifact.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertEqual(
            verification.returncode, 0,
            msg=verification.stdout + verification.stderr,
        )
        self.assertTrue(json.loads(verification.stdout)["proof_graph_included"])

    def test_archive_has_expected_positive_allowlist(self):
        with zipfile.ZipFile(str(self.first)) as archive:
            names = set(archive.namelist())
        prefix = BUILDER.ARCHIVE_ROOT + "/"
        self.assertIn(prefix + "BanditRLProof.lean", names)
        self.assertIn(prefix + "Tests.lean", names)
        self.assertIn(prefix + "Tests/DelayedFeedbackPaperAuditCanary.lean", names)
        self.assertIn(
            prefix + "BanditRLProof/Algorithms/"
            "StochasticGradientBanditTheoremFourContractAudit.lean",
            names,
        )
        self.assertIn(
            prefix + "Tests/StochasticGradientBanditTheoremFourContractAuditCanary.lean",
            names,
        )
        self.assertIn(
            prefix + "BanditRLProof/Algorithms/"
            "StochasticGradientBanditTheoremTwoNthPull.lean",
            names,
        )
        self.assertIn(
            prefix + "Tests/StochasticGradientBanditTheoremTwoNthPullCanary.lean",
            names,
        )
        self.assertIn(
            prefix + "BanditRLProof/Algorithms/"
            "StochasticGradientBanditTheoremTwoLatentReward.lean",
            names,
        )
        self.assertIn(
            prefix + "Tests/StochasticGradientBanditTheoremTwoLatentRewardCanary.lean",
            names,
        )
        self.assertIn(
            prefix + "BanditRLProof/Algorithms/"
            "StochasticGradientBanditTheoremTwoNativeTrajectory.lean",
            names,
        )
        self.assertIn(
            prefix + "Tests/"
            "StochasticGradientBanditTheoremTwoNativeTrajectoryCanary.lean",
            names,
        )
        self.assertIn(prefix + "evidence/claim-ledger.json", names)
        self.assertIn(prefix + "evidence/theorem-audit-comparison.json", names)
        self.assertIn(prefix + "evidence/delayed-feedback-proof-obligations.md", names)
        self.assertIn(prefix + "evidence/succinct-lower-bound-proof-obligations.md", names)
        self.assertIn(
            prefix + "evidence/stochastic-gradient-bandit-proof-obligations.md",
            names,
        )
        self.assertIn(
            prefix + "evidence/stochastic-gradient-bandit-follow-on-proof-obligations.md",
            names,
        )
        self.assertIn(prefix + "artifact/verify_artifact.py", names)
        self.assertIn(prefix + "tools/prepare_target_drift_checker_image.py", names)
        self.assertIn(
            prefix + "tools/prepare_target_drift_checker_probe_config.py", names
        )
        self.assertIn(prefix + "tools/target_drift_checker_cache_manifest.py", names)
        self.assertIn(prefix + "tools/export_target_drift_grader_pack.py", names)
        self.assertIn(prefix + "tools/test_target_drift_grader_export.py", names)
        self.assertIn(prefix + "tools/test_target_drift_grading.py", names)
        self.assertIn(
            prefix + "evaluation/target-drift-v2/checker-image-candidate-record.json",
            names,
        )
        self.assertIn(
            prefix + "evaluation/target-drift-v2/checker-image-isolation-candidate-record.json",
            names,
        )
        self.assertIn(
            prefix + "evaluation/target-drift-v2/agent-outer-boundary-candidate-record.json",
            names,
        )
        self.assertFalse(any("32137509103" in name for name in names))
        self.assertFalse(any("32419343467" in name for name in names))
        self.assertFalse(any("32735680163" in name for name in names))
        self.assertIn(
            prefix + "research-wiki/proof-graph/benchmark_report.json", names
        )
        self.assertIn(
            prefix + "research-wiki/proof-graph/benchmark_replication.json", names
        )
        self.assertIn(
            prefix + "evidence/proof-graph/benchmark_replication.json", names
        )
        self.assertIn(
            prefix + "research-wiki/proof-graph/proof_cost.schema.json", names
        )
        for rel in BUILDER.SOURCE_CONTRACT_AUDIT_FILES:
            self.assertIn(prefix + rel, names)
        for rel in BUILDER.SOURCE_CONTRACT_AUDIT_TOOLS:
            self.assertIn(prefix + rel, names)
        self.assertIn(prefix + BUILDER.EXTERNAL_COMPARATOR_PLAN, names)
        self.assertIn(prefix + BUILDER.EXTERNAL_COMPARATOR_SEAL, names)
        self.assertIn(prefix + BUILDER.LEANFLOW_ADAPTER_CONTRACT, names)
        self.assertIn(prefix + BUILDER.LEANFLOW_EXTERNAL_SCHEDULE, names)
        self.assertIn(prefix + BUILDER.LEANFLOW_FIXTURE_REQUEST, names)
        self.assertIn(prefix + BUILDER.LEANFLOW_LEDGER_CONTRACT, names)
        self.assertIn(prefix + BUILDER.LEANFLOW_PLUMBING_SEAL, names)
        self.assertIn(prefix + BUILDER.LEANFLOW_FAKE_ADAPTER, names)
        self.assertIn(prefix + BUILDER.LEANFLOW_SCHEDULE_BUILDER, names)
        self.assertIn(prefix + BUILDER.LEANFLOW_LEDGER_BUILDER, names)
        self.assertNotIn(
            prefix + "evaluation/target-drift-v2/external-comparator-results.json",
            names,
        )
        self.assertNotIn(
            prefix
            + "evaluation/target-drift-v2/leanflow-external-completion-ledger.json",
            names,
        )
        self.assertFalse(any("website/_site" in name for name in names))
        self.assertFalse(any("contributors.json" in name for name in names))
        self.assertFalse(any(name.endswith(".pdf") for name in names))
        self.assertFalse(any(".git/" in name for name in names))

    def test_extracted_verifier_passes(self):
        destination = self.root / "extracted"
        with zipfile.ZipFile(str(self.first)) as archive:
            archive.extractall(str(destination))
        artifact = destination / BUILDER.ARCHIVE_ROOT
        result = subprocess.run(
            [sys.executable, "artifact/verify_artifact.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertTrue(report["artifact_verified"])
        self.assertTrue(report["theorem_audit_comparison_verified"])
        self.assertFalse(report["target_drift_results_present"])
        source_audit = subprocess.run(
            [sys.executable, "tools/validate_source_contract_audit.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertEqual(
            source_audit.returncode, 0,
            msg=source_audit.stdout + source_audit.stderr,
        )

    def test_source_contract_audit_removes_authoring_git_fingerprints(self):
        payload = BUILDER.build_payload(allow_missing_graph=True)
        forbidden = (
            BUILDER.SOURCE_AUDIT_PUBLIC_BASE_COMMIT.encode("ascii"),
            *(item.encode("ascii") for item in BUILDER.SOURCE_AUDIT_PUBLIC_BLOB_IDS),
        )
        for rel in BUILDER.SOURCE_CONTRACT_AUDIT_FILES + BUILDER.SOURCE_CONTRACT_AUDIT_TOOLS:
            with self.subTest(path=rel):
                self.assertFalse(any(item in payload[rel] for item in forbidden))
        base = json.loads(
            payload[BUILDER.SOURCE_AUDIT_BASE_MANIFEST].decode("utf-8")
        )
        anonymous_base = json.loads(
            payload["evidence/anonymous-base-manifest.json"].decode("utf-8")
        )
        self.assertEqual(
            base["base_git_commit"],
            anonymous_base["schema_compatibility_reference"],
        )
        for row in base["snapshots"].values():
            self.assertNotIn("git_blob_sha1", row)
            self.assertRegex(row["snapshot_binding_sha1"], r"^[0-9a-f]{40}$")

    def test_extracted_external_comparator_validator_passes(self):
        destination = self.root / "external-comparator"
        with zipfile.ZipFile(str(self.first)) as archive:
            archive.extractall(str(destination))
        artifact = destination / BUILDER.ARCHIVE_ROOT
        result = subprocess.run(
            [sys.executable, "tools/validate_target_drift_external_comparator.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)
        self.assertIn("external comparator plan valid and unrun", result.stdout)

    def test_anonymous_external_comparator_rebinds_primary_bytes(self):
        payload = BUILDER.build_payload(allow_missing_graph=True)
        protocol_sha = hashlib.sha256(
            payload[BUILDER.TARGET_DRIFT_V2_PROTOCOL]
        ).hexdigest()
        plan_data = payload[BUILDER.EXTERNAL_COMPARATOR_PLAN]
        plan = json.loads(plan_data.decode("utf-8"))
        seal = json.loads(
            payload[BUILDER.EXTERNAL_COMPARATOR_SEAL].decode("utf-8")
        )
        self.assertEqual(plan["primary_protocol_sha256"], protocol_sha)
        self.assertEqual(seal["primary_protocol_sha256"], protocol_sha)
        self.assertEqual(
            seal["plan_sha256"], hashlib.sha256(plan_data).hexdigest()
        )

    def test_extracted_verifier_rejects_unmanifested_file(self):
        # Keep the path short enough for the longest Lean module on Windows.
        destination = self.root / "extra"
        with zipfile.ZipFile(str(self.first)) as archive:
            archive.extractall(str(destination))
        artifact = destination / BUILDER.ARCHIVE_ROOT
        (artifact / "unexpected-output.json").write_text("{}\n", encoding="utf-8")
        result = subprocess.run(
            [sys.executable, "artifact/verify_artifact.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unmanifested extracted file", result.stdout + result.stderr)

    def test_extracted_verifier_rejects_delayed_record_id_drift(self):
        destination = self.root / "delayed-record-id-drift"
        with zipfile.ZipFile(str(self.first)) as archive:
            archive.extractall(str(destination))
        artifact = destination / BUILDER.ARCHIVE_ROOT
        ledger_path = artifact / "evidence" / "claim-ledger.json"
        ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
        fake_id = "FAKE-DIAGNOSTIC-RECORD"
        source = dict(ledger["source_records"][BUILDER.DELAYED_DIAGNOSTIC_ID])
        source["id"] = fake_id
        ledger["source_records"][fake_id] = source
        ledger["delayed_feedback"]["diagnostic_id"] = fake_id
        ledger_path.write_text(
            json.dumps(ledger, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        manifest_path = artifact / "ARTIFACT_MANIFEST.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        tree_digest = hashlib.sha256()
        for entry in manifest["files"]:
            path = artifact / entry["path"]
            data = path.read_bytes()
            entry["bytes"] = len(data)
            entry["sha256"] = hashlib.sha256(data).hexdigest()
            tree_digest.update(entry["path"].encode("utf-8") + b"\0")
            tree_digest.update(entry["sha256"].encode("ascii") + b"\0")
            tree_digest.update(str(entry["bytes"]).encode("ascii") + b"\n")
        manifest["source_tree_digest"] = tree_digest.hexdigest()
        manifest_path.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        result = subprocess.run(
            [sys.executable, "artifact/verify_artifact.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "record binding drift for diagnostic_id",
            result.stdout + result.stderr,
        )

    def test_extracted_verifier_rejects_sgb_theorem_four_endpoint_drift(self):
        destination = self.root / "sgb-theorem-four-endpoint-drift"
        with zipfile.ZipFile(str(self.first)) as archive:
            archive.extractall(str(destination))
        artifact = destination / BUILDER.ARCHIVE_ROOT
        ledger_path = artifact / "evidence" / "claim-ledger.json"
        ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
        ledger["stochastic_gradient_bandit"][
            "theorem_four_endpoint_verified"
        ] = True
        ledger_path.write_text(
            json.dumps(ledger, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        manifest_path = artifact / "ARTIFACT_MANIFEST.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        tree_digest = hashlib.sha256()
        for entry in manifest["files"]:
            path = artifact / entry["path"]
            data = path.read_bytes()
            entry["bytes"] = len(data)
            entry["sha256"] = hashlib.sha256(data).hexdigest()
            tree_digest.update(entry["path"].encode("utf-8") + b"\0")
            tree_digest.update(entry["sha256"].encode("ascii") + b"\0")
            tree_digest.update(str(entry["bytes"]).encode("ascii") + b"\n")
        manifest["source_tree_digest"] = tree_digest.hexdigest()
        manifest_path.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        result = subprocess.run(
            [sys.executable, "artifact/verify_artifact.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "SGB Theorem-4 endpoint verification flag drift",
            result.stdout + result.stderr,
        )

    def test_claim_ledger_has_conservative_counts(self):
        payload = BUILDER.build_payload(allow_missing_graph=True)
        ledger = json.loads(payload["evidence/claim-ledger.json"].decode("utf-8"))
        self.assertEqual(ledger["delayed_feedback"]["implementation_facing_declaration_count"], 89)
        self.assertEqual(
            ledger["delayed_feedback"]["diagnostic_conditional_repair_declaration_count"],
            19,
        )
        self.assertEqual(ledger["delayed_feedback"]["processed_prefix_declaration_count"], 16)
        self.assertEqual(
            ledger["delayed_feedback"]["processed_trace_summary_declaration_count"],
            9,
        )
        self.assertEqual(
            ledger["delayed_feedback"]["ordered_no_switch_transition_declaration_count"],
            15,
        )
        self.assertEqual(
            ledger["delayed_feedback"]["ordered_no_switch_trace_declaration_count"],
            12,
        )
        self.assertEqual(ledger["delayed_feedback"]["d11_domain_declaration_count"], 6)
        self.assertEqual(
            ledger["delayed_feedback"]["line10_initialization_declaration_count"],
            31,
        )
        self.assertEqual(ledger["delayed_feedback"]["source_audit_declaration_count"], 197)
        self.assertEqual(
            ledger["delayed_feedback"]["generic_multiregime_contract_declaration_count"],
            5,
        )
        self.assertEqual(ledger["delayed_feedback"]["directory_declaration_count"], 202)
        self.assertFalse(ledger["delayed_feedback"]["paper_endpoint_verified"])
        self.assertEqual(ledger["source_records"][BUILDER.DELAYED_DIAGNOSTIC_ID]["status"], "partial")
        self.assertEqual(
            ledger["source_records"][BUILDER.DELAYED_TRACE_SUMMARY_ID]["status"],
            "compiled",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.DELAYED_ORDERED_TRANSITION_ID]["status"],
            "compiled",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.DELAYED_ORDERED_TRACE_ID]["status"],
            "compiled",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.DELAYED_D11_DOMAIN_ID]["status"],
            "compiled",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.DELAYED_LINE10_INITIALIZATION_ID]["status"],
            "compiled",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.DELAYED_CENTRAL_ENDPOINT_ID]["status"],
            "partial",
        )
        self.assertEqual(
            ledger["source_records"]["TARGET-DRIFT-V2-CONTROLLED-EVALUATION"]["status"],
            "planned",
        )
        direct_textbook_records = {
            "TEXTBOOK-PART-IV-THEOREM-13-1-GAUSSIAN-MINIMAX",
            "TEXTBOOK-PART-IV-CH15-SAME-POLICY-HISTORY-KL-DECOMPOSITION",
            "TEXTBOOK-PART-IV-CH15-GAUSSIAN-MINIMAX-LOWER-BOUND",
        }
        textbook_row = next(
            row for row in ledger["table_rows"]
            if row["artifact"] == "Textbook Chapters 13--17"
        )
        self.assertTrue(
            direct_textbook_records.issubset(set(textbook_row["source_record_ids"]))
        )
        for record_id in direct_textbook_records:
            self.assertEqual(ledger["source_records"][record_id]["status"], "compiled")
        self.assertEqual(
            ledger["textbook_chapter_16"]["dependency_declaration_count"],
            20,
        )
        self.assertEqual(
            ledger["textbook_chapter_16"]["event_regret_declaration_count"],
            15,
        )
        self.assertFalse(
            ledger["textbook_chapter_16"]["finite_mean_gap_bridge_verified"]
        )
        self.assertFalse(
            ledger["textbook_chapter_16"]["source_terminals_verified"]
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.CH16_COMPILED_ID]["status"],
            "compiled",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.CH16_EVENT_REGRET_ID]["status"],
            "compiled",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.CH16_TERMINAL_ID]["status"],
            "blocked",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.CH16_TERMINAL_ID]["declarations"],
            [],
        )
        succinct_row = next(
            row for row in ledger["table_rows"]
            if row["artifact"] == "Succinct geometry audit"
        )
        self.assertEqual(succinct_row["status"], "partial")
        self.assertEqual(succinct_row["source_record_ids"], [BUILDER.SUCCINCT_AUDIT_ID])
        self.assertEqual(ledger["succinct_geometry"]["declaration_count"], 54)
        self.assertFalse(ledger["succinct_geometry"]["paper_endpoint_verified"])
        self.assertEqual(
            ledger["source_records"][BUILDER.SUCCINCT_AUDIT_ID]["status"],
            "partial",
        )
        sgb_row = next(
            row for row in ledger["table_rows"]
            if row["artifact"] ==
                "Stochastic-gradient-bandit Theorem 1, Corollary 1, and blocked Theorem-2 follow-on"
        )
        self.assertEqual(sgb_row["status"], "partial")
        self.assertEqual(
            sgb_row["source_record_ids"],
            [BUILDER.SGB_AUDIT_ID, BUILDER.SGB_FOLLOW_ON_ID],
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["declaration_count"], 316
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "historical_declaration_count"
            ],
            223,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "theorem_one_stack_declaration_count"
            ],
            215,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "theorem_four_contract_audit_declaration_count"
            ],
            8,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "corollary_one_declaration_count"
            ],
            23,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "theorem_two_deterministic_starvation_consumer_declaration_count"
            ],
            18,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "theorem_two_nth_pull_bridge_declaration_count"
            ],
            24,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "theorem_two_latent_reward_product_readout_declaration_count"
            ],
            7,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "theorem_two_prefix_factorization_declaration_count"
            ],
            8,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "theorem_two_action_readout_branch_locality_interface_and_count_cap_scaffold_declaration_count"
            ],
            13,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["finite_algebra_declaration_count"],
            26,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["generated_history_declaration_count"],
            18,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["two_arm_rate_declaration_count"],
            18,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["exponential_audit_declaration_count"],
            14,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["generated_equation_8_declaration_count"],
            4,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["successor_recurrence_declaration_count"],
            10,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["initial_recurrence_declaration_count"],
            3,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["measurable_recurrence_declaration_count"],
            25,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["path_integrability_declaration_count"],
            19,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["fixed_iid_declaration_count"],
            9,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "unconditional_recurrence_declaration_count"
            ],
            37,
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["theorem_one_declaration_count"],
            32,
        )
        self.assertTrue(
            ledger["stochastic_gradient_bandit"]["generated_trajectory_compiled"]
        )
        self.assertTrue(
            ledger["stochastic_gradient_bandit"]["conditional_law_bridge_compiled"]
        )
        self.assertTrue(
            ledger["stochastic_gradient_bandit"]["two_arm_equation_11_compiled"]
        )
        self.assertTrue(
            ledger["stochastic_gradient_bandit"]["source_equation_8_compiled"]
        )
        for flag in (
            "generated_equation_8_kernel_bridge_compiled",
            "two_arm_initial_recurrence_compiled",
            "fixed_history_successor_recurrence_compiled",
            "trajectory_cond_distrib_recurrence_compiled",
            "path_integrability_compiled",
            "conditional_expectation_one_step_recurrence_compiled",
            "fixed_iid_contract_compiled",
            "unconditional_recurrence_iteration_compiled",
            "generic_expected_failure_mass_bound_compiled",
            "source_theorem_one_compiled",
            "source_theorem_four_contract_audit_compiled",
            "source_corollary_one_compiled",
            "source_theorem_two_deterministic_starvation_consumer_compiled",
            "source_theorem_two_nth_pull_bridge_compiled",
            "source_theorem_two_latent_product_readout_compiled",
            "source_theorem_two_prefix_factorization_compiled",
            "source_theorem_two_action_factorization_compiled",
            "source_theorem_two_pathwise_coordinate_support_compiled",
            "source_theorem_two_branch_product_consumer_compiled",
            "source_theorem_two_branch_locality_contract_typed",
            "source_theorem_two_count_cap_scaffold_compiled",
        ):
            self.assertTrue(ledger["stochastic_gradient_bandit"][flag])
        for missing_bridge in (
            "visible-marginal/native-prefix identification",
            "prefix-plus-next-pair freshness",
            "full native visible law",
            "stopped-prefix future-cylinder",
            "conditional no-return probability >= 1/2",
            "Rademacher/binomial ballot phase",
            "asymptotic terminal",
            "does not make totalized or occurrence-conditioned stopped rewards IID",
            "branch-locality contract is typed but unproved",
            "no branch-locality producer is compiled",
        ):
            self.assertIn(missing_bridge, sgb_row["boundary"])
        self.assertTrue(
            ledger["stochastic_gradient_bandit"][
                "source_corollary_one_is_direct_theorem_one_consumer"
            ]
        )
        self.assertEqual(
            ledger["stochastic_gradient_bandit"]["source_theorem_two_status"],
            "blocked",
        )
        self.assertFalse(
            ledger["stochastic_gradient_bandit"][
                "source_theorem_two_endpoint_verified"
            ]
        )
        self.assertFalse(
            ledger["stochastic_gradient_bandit"][
                "source_theorem_two_branch_locality_producer_compiled"
            ]
        )
        self.assertTrue(
            ledger["stochastic_gradient_bandit"][
                "coordinate_update_integrability_verified"
            ]
        )
        self.assertFalse(
            ledger["stochastic_gradient_bandit"]["uniform_reward_regularities_verified"]
        )
        self.assertFalse(
            ledger["stochastic_gradient_bandit"]["learning_rate_regime_verified"]
        )
        self.assertTrue(
            ledger["stochastic_gradient_bandit"]["global_tower_iteration_verified"]
        )
        self.assertTrue(
            ledger["stochastic_gradient_bandit"]["expected_failure_mass_verified"]
        )
        self.assertTrue(ledger["stochastic_gradient_bandit"]["paper_endpoint_verified"])
        self.assertEqual(
            ledger["stochastic_gradient_bandit"][
                "paper_endpoint_verified_scope"
            ],
            "Theorem 1 only",
        )
        self.assertFalse(
            ledger["stochastic_gradient_bandit"]["theorem_four_endpoint_verified"]
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.SGB_AUDIT_ID]["status"],
            "partial",
        )
        self.assertEqual(
            ledger["source_records"][BUILDER.SGB_FOLLOW_ON_ID]["status"],
            "partial",
        )

    def test_theorem_audit_comparison_is_claim_ledger_backed(self):
        payload = BUILDER.build_payload(allow_missing_graph=True)
        comparison = json.loads(payload[
            BUILDER.THEOREM_AUDIT_COMPARISON_DESTINATION
        ].decode("utf-8"))
        ledger = json.loads(payload["evidence/claim-ledger.json"].decode("utf-8"))
        self.assertEqual(comparison, ledger["theorem_audit_comparison"])
        self.assertEqual(
            [row["id"] for row in comparison["rows"]],
            list(BUILDER.THEOREM_AUDIT_ROW_IDS),
        )
        rows = {row["id"]: row for row in comparison["rows"]}
        chapter15 = rows["textbook-chapter-15-scoped-positive-control"]
        self.assertEqual(chapter15["promotion_status"], "compiled")
        self.assertEqual(chapter15["compiled_declaration_count"], 12)
        self.assertTrue(chapter15["scoped_endpoint_verified"])
        self.assertNotIn("paper_endpoint_verified", chapter15)

        delayed = rows["delayed-bobw-source-frozen-audit"]
        self.assertEqual(delayed["compiled_declaration_count"], 197)
        self.assertEqual(
            delayed["declaration_count_breakdown"],
            {
                "implementation_facing": 89,
                "diagnostic_conditional_repair": 19,
                "processed_prefix": 16,
                "processed_trace_summary_adapter": 9,
                "ordered_no_switch_transition": 15,
                "ordered_no_switch_trace_ordering": 12,
                "nonnegative_gap_d11_domain": 6,
                "line10_eliminated_arm_initialization": 31,
            },
        )
        self.assertIn(
            "simultaneous D.4 2/T probability bound and full good-event projection",
            delayed["blocking_obligations"],
        )
        succinct = rows["succinct-lower-bound-source-frozen-audit"]
        self.assertEqual(succinct["compiled_declaration_count"], 54)
        sgb = rows["stochastic-gradient-bandit-source-frozen-audit"]
        self.assertEqual(sgb["compiled_declaration_count"], 316)
        self.assertEqual(
            sgb["evidence_record_ids"],
            [BUILDER.SGB_AUDIT_ID, BUILDER.SGB_FOLLOW_ON_ID],
        )
        self.assertEqual(
            sgb["declaration_count_breakdown"],
            {
                "finite_action_algebra": 26,
                "generated_history_and_kernel_bridge": 18,
                "two_arm_zero_sum_and_equation_11": 18,
                "source_c_and_equation_8": 14,
                "generated_equation_8_kernel_bridge": 4,
                "fixed_history_successor_recurrence": 10,
                "two_arm_initial_recurrence": 3,
                "measurable_contract_and_cond_distrib_transport": 25,
                "path_integrability_and_conditional_recurrence": 19,
                "fixed_iid_source_contract_bridge": 9,
                "unconditional_recurrence_and_failure_mass": 37,
                "source_theorem_one_terminal": 32,
                "source_theorem_four_contract_audit": 8,
                "source_corollary_one_companion": 23,
                "source_theorem_two_deterministic_starvation_consumer": 18,
                "source_theorem_two_nth_pull_bridge": 24,
                "source_theorem_two_latent_reward_product_readout": 7,
                "source_theorem_two_deferred_decisions_prefix_factorization": 8,
                "source_theorem_two_action_readout_branch_locality_interface_and_count_cap_scaffold": 13,
            },
        )
        for row in (delayed, succinct, sgb):
            self.assertEqual(row["promotion_status"], "partial")
            self.assertTrue(row["blocking_obligations"])
        self.assertFalse(delayed["paper_endpoint_verified"])
        self.assertFalse(succinct["paper_endpoint_verified"])
        self.assertTrue(sgb["paper_endpoint_verified"])
        self.assertTrue(sgb["theorem_one_endpoint_verified"])
        self.assertTrue(sgb["corollary_one_endpoint_verified"])
        self.assertFalse(sgb["theorem_two_endpoint_verified"])
        self.assertFalse(sgb["theorem_four_endpoint_verified"])
        self.assertTrue(sgb["theorem_two_nth_pull_bridge_compiled"])
        self.assertTrue(sgb["theorem_two_latent_product_readout_compiled"])
        self.assertTrue(sgb["theorem_two_prefix_factorization_compiled"])
        self.assertTrue(sgb["theorem_two_action_factorization_compiled"])
        self.assertTrue(sgb["theorem_two_pathwise_coordinate_support_compiled"])
        self.assertTrue(sgb["theorem_two_branch_product_consumer_compiled"])
        self.assertTrue(sgb["theorem_two_branch_locality_contract_typed"])
        self.assertTrue(sgb["theorem_two_count_cap_scaffold_compiled"])
        self.assertFalse(sgb["theorem_two_branch_locality_producer_compiled"])

    def test_theorem_audit_comparison_rejects_status_and_count_drift(self):
        records = BUILDER.selected_source_records()
        index = BUILDER.load_json(
            BUILDER.REPO_ROOT / "research-wiki" / "retrieval-index" /
            "local_lean_declarations.json"
        )
        source = BUILDER.load_json(
            BUILDER.REPO_ROOT / BUILDER.THEOREM_AUDIT_COMPARISON_SOURCE
        )
        status_drift = json.loads(json.dumps(source))
        status_drift["rows"][1]["promotion_status"] = "compiled"
        with self.assertRaisesRegex(ValueError, "promotion_status drift"):
            BUILDER.validate_theorem_audit_comparison(
                records, index, comparison=status_drift
            )

        count_drift = json.loads(json.dumps(source))
        count_drift["rows"][1]["compiled_declaration_count"] = 147
        with self.assertRaisesRegex(ValueError, "compiled_declaration_count drift"):
            BUILDER.validate_theorem_audit_comparison(
                records, index, comparison=count_drift
            )

        theorem_four_endpoint_drift = json.loads(json.dumps(source))
        theorem_four_endpoint_drift["rows"][3][
            "theorem_four_endpoint_verified"
        ] = True
        with self.assertRaisesRegex(
            ValueError, "theorem_four_endpoint_verified drift"
        ):
            BUILDER.validate_theorem_audit_comparison(
                records, index, comparison=theorem_four_endpoint_drift
            )

        theorem_two_endpoint_drift = json.loads(json.dumps(source))
        theorem_two_endpoint_drift["rows"][3][
            "theorem_two_endpoint_verified"
        ] = True
        with self.assertRaisesRegex(
            ValueError, "theorem_two_endpoint_verified drift"
        ):
            BUILDER.validate_theorem_audit_comparison(
                records, index, comparison=theorem_two_endpoint_drift
            )

        declaration_drift_records = json.loads(json.dumps(records))
        declaration_drift_records[BUILDER.DELAYED_D11_DOMAIN_ID]["declarations"][0] = (
            "BanditRLProof.ETC.Spec"
        )
        with self.assertRaisesRegex(
            ValueError, "exact non-generic DelayedFeedback declaration set"
        ):
            BUILDER.validate_theorem_audit_comparison(
                declaration_drift_records, index, comparison=source
            )

        source_freeze = BUILDER.load_json(
            BUILDER.REPO_ROOT / "research-wiki" / "papers" /
            "prospective-audit-2025-freeze.json"
        )
        timing_drift = json.loads(json.dumps(source_freeze))
        timing_drift["selection_status"] = "frozen_before_lean_proof_search"
        with self.assertRaisesRegex(
            ValueError, "source-lock portfolio timing status drifted"
        ):
            BUILDER.validate_theorem_audit_comparison(
                records, index, comparison=source, source_freeze=timing_drift
            )

        case_timing_drift = json.loads(json.dumps(source_freeze))
        case_timing_drift["papers"][0]["selection_timing"] = (
            "locked_before_case_specific_lean_slice"
        )
        with self.assertRaisesRegex(
            ValueError, "source-lock case-specific timing drifted"
        ):
            BUILDER.validate_theorem_audit_comparison(
                records, index, comparison=source,
                source_freeze=case_timing_drift
            )

    def test_sgb_required_bridge_names_are_frozen(self):
        required_sets = (
            BUILDER.SGB_CONDITIONAL_LAW_BRIDGE_DECLARATIONS,
            BUILDER.SGB_TWO_ARM_RATE_DECLARATIONS,
            BUILDER.SGB_EXPONENTIAL_AUDIT_DECLARATIONS,
            BUILDER.SGB_GENERATED_EQUATION_8_DECLARATIONS,
            BUILDER.SGB_INITIAL_RECURRENCE_DECLARATIONS,
            BUILDER.SGB_SUCCESSOR_RECURRENCE_DECLARATIONS,
            BUILDER.SGB_TRAJECTORY_COND_DISTRIB_RECURRENCE_DECLARATIONS,
            BUILDER.SGB_PATH_INTEGRABILITY_DECLARATIONS,
            BUILDER.SGB_CONDITIONAL_RECURRENCE_DECLARATIONS,
            BUILDER.SGB_FIXED_IID_DECLARATIONS,
            BUILDER.SGB_UNCONDITIONAL_RECURRENCE_DECLARATIONS,
            BUILDER.SGB_THEOREM_ONE_DECLARATIONS,
            BUILDER.SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATIONS,
            BUILDER.SGB_COROLLARY_ONE_REPRESENTATIVE_DECLARATIONS,
            BUILDER.SGB_THEOREM_TWO_STARVATION_REPRESENTATIVE_DECLARATIONS,
            BUILDER.SGB_THEOREM_TWO_NTH_PULL_REPRESENTATIVE_DECLARATIONS,
            BUILDER.SGB_THEOREM_TWO_LATENT_REWARD_DECLARATIONS,
            BUILDER.SGB_THEOREM_TWO_PREFIX_FACTORIZATION_DECLARATIONS,
            BUILDER.SGB_THEOREM_TWO_ACTION_READOUT_BRANCH_LOCALITY_INTERFACE_AND_COUNT_CAP_SCAFFOLD_DECLARATIONS,
        )
        for required in required_sets:
            with self.subTest(victim_set=sorted(required)):
                records = json.loads(json.dumps(BUILDER.selected_source_records()))
                index = BUILDER.load_json(
                    BUILDER.REPO_ROOT / "research-wiki" / "retrieval-index" /
                    "local_lean_declarations.json"
                )
                victim = next(iter(required))
                replacement = victim + "_drifted"
                record_id = (
                    BUILDER.SGB_AUDIT_ID
                    if victim in records[BUILDER.SGB_AUDIT_ID]["declarations"]
                    else BUILDER.SGB_FOLLOW_ON_ID
                )
                declarations = records[record_id]["declarations"]
                declarations[declarations.index(victim)] = replacement
                row = next(
                    row for row in index["declarations"]
                    if row["full_name"] == victim
                )
                row["full_name"] = replacement
                with self.assertRaisesRegex(
                    ValueError,
                    "316 declarations: historical 223",
                ):
                    BUILDER.validate_sgb_count(records, index)

    def test_ch16_dependency_names_and_blocked_terminals_are_frozen(self):
        records = json.loads(json.dumps(BUILDER.selected_source_records()))
        declarations = records[BUILDER.CH16_COMPILED_ID]["declarations"]
        declarations[-1] = declarations[-1] + "_drifted"
        with self.assertRaisesRegex(ValueError, "frozen 20 unique declarations"):
            BUILDER.validate_ch16_boundary(records)

        records = json.loads(json.dumps(BUILDER.selected_source_records()))
        declarations = records[BUILDER.CH16_EVENT_REGRET_ID]["declarations"]
        declarations[-1] = declarations[-1] + "_drifted"
        with self.assertRaisesRegex(ValueError, "frozen 15 unique declarations"):
            BUILDER.validate_ch16_boundary(records)

        records = json.loads(json.dumps(BUILDER.selected_source_records()))
        records[BUILDER.CH16_TERMINAL_ID]["declarations"] = [
            "BanditRLProof.LowerBounds.uncompiledChapter16Terminal"
        ]
        with self.assertRaisesRegex(ValueError, "blocked and declaration-free"):
            BUILDER.validate_ch16_boundary(records)

    def test_public_base_is_replaced_by_anonymous_tree_binding(self):
        payload = BUILDER.build_payload(allow_missing_graph=True)
        joined = b"\n".join(payload.values()).lower()
        self.assertNotIn(BUILDER.PUBLIC_WORKSPACE_BASE_COMMIT.encode("ascii"), joined)
        self.assertNotIn(
            b"cb5d50be148c691cc595ed9fd2f535c42506fada", joined
        )
        base = json.loads(
            payload["evidence/anonymous-base-manifest.json"].decode("utf-8")
        )
        self.assertFalse(base["git_object_database_included"])
        self.assertFalse(base["materializable_by_target_drift_runner"])
        readme = payload["evaluation/target-drift-v2/README.md"].decode("utf-8")
        self.assertIn("tools/target_drift_agent_pid1.py", payload)
        self.assertIn("tools/record_target_drift_agent_lifecycle_probe.py", payload)
        self.assertIn("tools/test_target_drift_agent_lifecycle.py", payload)
        self.assertIn("tools/prepare_target_drift_agent_image.py", payload)
        self.assertIn("tools/record_target_drift_agent_image_probe.py", payload)
        self.assertIn("tools/test_target_drift_agent_image.py", payload)
        self.assertIn(
            ".github/workflows/target-drift-agent-lifecycle.yml", payload
        )
        self.assertIn(
            ".github/workflows/target-drift-agent-image.yml", payload
        )
        self.assertIn(
            ".github/workflows/leanflow-source-preflight.yml", payload
        )
        self.assertIn(".gitattributes", payload)
        self.assertIn("evaluation/target-drift-v2/agent-sandbox-contract.json", payload)
        self.assertIn("evaluation/target-drift-v2/agent-lifecycle.Containerfile", payload)
        self.assertIn("evaluation/target-drift-v2/agent-image.Containerfile", payload)
        self.assertIn("evaluation/target-drift-v2/agent-image-sources.json", payload)
        self.assertIn("evaluation/target-drift-v2/agent-codex-native.apparmor", payload)
        self.assertIn(
            "evaluation/target-drift-v2/wording-negative-control-record.json",
            payload,
        )
        self.assertIn(
            "evaluation/target-drift-v2/leanflow-real-adapter-contract.json",
            payload,
        )
        self.assertIn("tools/leanflow_target_drift_adapter.py", payload)
        self.assertIn("tools/test_leanflow_target_drift_adapter.py", payload)
        self.assertIn("tools/validate_leanflow_source_preflight.py", payload)
        self.assertIn("tools/test_leanflow_source_preflight.py", payload)
        anonymous_workflow = payload[
            ".github/workflows/leanflow-source-preflight.yml"
        ]
        anonymous_workflow_sha256 = hashlib.sha256(anonymous_workflow).hexdigest()
        anonymous_validator = payload[
            "tools/validate_leanflow_source_preflight.py"
        ]
        self.assertIn(
            (
                'EXPECTED_WORKFLOW_SHA256 = "{}"'.format(
                    anonymous_workflow_sha256
                )
            ).encode("ascii"),
            anonymous_validator,
        )
        self.assertIn(b"anonymous/abrl-artifact", anonymous_workflow)
        self.assertIn(b"anonymous/abrl-artifact", anonymous_validator)
        self.assertNotIn(b"dakebu", anonymous_workflow.lower())
        self.assertNotIn(b"dakebu", anonymous_validator.lower())
        self.assertIn("tools/fetch_target_drift_sources.py", payload)
        self.assertIn("tools/test_fetch_target_drift_sources.py", payload)
        self.assertIn("tools/test_target_drift_wording_record.py", payload)
        self.assertIn("non-Git", readme)
        self.assertNotIn("the public base immediately", readme)
        self.assertNotIn(BUILDER.PUBLIC_CANDIDATE_RUN_ID, readme)
        self.assertNotIn(BUILDER.PUBLIC_ISOLATION_CANDIDATE_RUN_ID, readme)
        self.assertNotIn(BUILDER.PUBLIC_AGENT_LIFECYCLE_RUN_ID, readme)
        self.assertNotIn(BUILDER.PUBLIC_AGENT_IMAGE_RUN_ID, readme)
        self.assertNotIn(BUILDER.PUBLIC_AGENT_OUTER_BOUNDARY_RUN_ID, readme)
        candidate = json.loads(payload[
            "evaluation/target-drift-v2/checker-image-candidate-record.json"
        ].decode("utf-8"))
        self.assertEqual(
            candidate["workflow_run"]["id"], "<redacted-public-run-id>"
        )
        self.assertEqual(
            candidate["workflow_run"]["head_commit"],
            "<anonymous-builder-snapshot>",
        )
        isolation_candidate = json.loads(payload[
            "evaluation/target-drift-v2/checker-image-isolation-candidate-record.json"
        ].decode("utf-8"))
        lifecycle_candidate = json.loads(payload[
            "evaluation/target-drift-v2/agent-lifecycle-candidate-record.json"
        ].decode("utf-8"))
        agent_image_candidate = json.loads(payload[
            "evaluation/target-drift-v2/agent-image-candidate-record.json"
        ].decode("utf-8"))
        outer_candidate = json.loads(payload[
            "evaluation/target-drift-v2/agent-outer-boundary-candidate-record.json"
        ].decode("utf-8"))
        self.assertEqual(
            lifecycle_candidate["workflow_run"]["id"],
            "<redacted-public-run-id>",
        )
        self.assertEqual(
            lifecycle_candidate["workflow_run"]["head_commit"],
            "<anonymous-builder-snapshot>",
        )
        self.assertEqual(
            agent_image_candidate["workflow_run"]["id"],
            "<redacted-public-run-id>",
        )
        self.assertEqual(
            agent_image_candidate["workflow_run"]["url"],
            "<redacted-public-run-url>",
        )
        self.assertEqual(
            agent_image_candidate["workflow_run"]["head_commit"],
            "<anonymous-builder-snapshot>",
        )
        self.assertEqual(
            agent_image_candidate["recorded_at_utc"],
            "<redacted-public-run-time>",
        )
        self.assertEqual(
            agent_image_candidate["workflow_run"]["job_duration"],
            "<redacted-public-run-duration>",
        )
        self.assertNotIn("artifacts", agent_image_candidate)
        self.assertNotIn(
            "container_image_digest", agent_image_candidate["candidate"]
        )
        self.assertNotIn(
            "command_sha256", agent_image_candidate["lifecycle_probe"]
        )
        self.assertEqual(
            outer_candidate["workflow_run"]["id"],
            "<redacted-public-run-id>",
        )
        self.assertEqual(
            outer_candidate["workflow_run"]["head_commit"],
            "<anonymous-builder-snapshot>",
        )
        self.assertTrue(outer_candidate["probe_checkout"]["trees_identical"])
        self.assertEqual(
            outer_candidate["candidate"]["workspace_base_commit"],
            json.loads(payload["evidence/anonymous-base-manifest.json"])[
                "schema_compatibility_reference"
            ],
        )
        self.assertNotIn("artifacts", outer_candidate)
        self.assertNotIn("source_bindings", outer_candidate)
        self.assertNotIn("container_image_digest", outer_candidate["candidate"])
        self.assertNotIn(
            "container_image_digest", outer_candidate["cross_probe_bindings"]
        )
        outer_component = outer_candidate["outer_boundary_component"]
        self.assertEqual(
            [item["path"] for item in outer_component["control_evidence"]["files"]],
            [
                "controller-report.json",
                "pid1-exit.json",
                "pid1-ready.json",
                "root-only-sentinel",
            ],
        )
        self.assertEqual(
            outer_component["worker_boundary"]["effective_capabilities_hex"],
            "0000000000000000",
        )
        nested = outer_component["nested_codex_sandbox_observation"]
        self.assertEqual(nested["outer_auth_mount_read_error_name"], "EACCES")
        self.assertEqual(nested["root_control_output_read_error_name"], "EACCES")
        self.assertTrue(nested["trusted_auth_fd_env_absent"])
        self.assertTrue(nested["trusted_auth_fd_target_absent"])
        self.assertEqual(nested["effective_capabilities_hex"], "0000000000000000")
        self.assertEqual(outer_component["pid1_observation"]["controller_pid"], 1)
        self.assertEqual(outer_component["pid1_observation"]["child_return_code"], 0)
        self.assertTrue(
            outer_component["pid1_observation"][
                "interpreter_shutdown_fatal_absent_from_captured_log"
            ]
        )
        public_outer_record = json.loads(
            (BUILDER.REPO_ROOT / BUILDER.PUBLIC_AGENT_OUTER_BOUNDARY_RECORD).read_text(
                encoding="utf-8"
            )
        )
        anonymous_outer_bytes = payload[
            "evaluation/target-drift-v2/agent-outer-boundary-candidate-record.json"
        ]
        public_outer_fingerprints = {
            public_outer_record["recorded_at_utc"],
            public_outer_record["workflow_run"]["job_duration"],
            public_outer_record["workflow_run"]["head_commit"],
            public_outer_record["probe_checkout"]["pull_request_merge_commit"],
            public_outer_record["probe_checkout"]["pull_request_merge_tree"],
            public_outer_record["candidate"]["container_image_digest"],
            public_outer_record["candidate"]["checker_base_image_digest"],
            public_outer_record["outer_boundary_component"][
                "trusted_client_fake_auth_handoff"
            ]["sha256"],
        }
        public_outer_fingerprints.update(
            item["sha256"] for item in public_outer_record["artifacts"]
            if item["sha256"] != hashlib.sha256(b"").hexdigest()
        )
        public_outer_fingerprints.update(
            item["sha256"] for item in public_outer_record["source_bindings"]
        )
        for fingerprint in public_outer_fingerprints:
            self.assertNotIn(fingerprint.encode("utf-8"), anonymous_outer_bytes)
        public_agent_record = json.loads(
            (BUILDER.REPO_ROOT / BUILDER.PUBLIC_AGENT_IMAGE_RECORD).read_text(
                encoding="utf-8"
            )
        )
        anonymous_agent_bytes = payload[
            "evaluation/target-drift-v2/agent-image-candidate-record.json"
        ]
        public_fingerprints = (
            public_agent_record["recorded_at_utc"],
            public_agent_record["workflow_run"]["job_duration"],
            public_agent_record["candidate"]["container_image_digest"],
            public_agent_record["candidate"]["checker_base_image_digest"],
            public_agent_record["sandbox_probe"]["sandbox_command_sha256"],
            public_agent_record["lifecycle_probe"]["command_sha256"],
            public_agent_record["artifacts"][0]["sha256"],
        )
        for fingerprint in public_fingerprints:
            self.assertNotIn(fingerprint.encode("utf-8"), anonymous_agent_bytes)
        anonymous_records = {
            BUILDER.PUBLIC_CANDIDATE_RECORD:
                "evaluation/target-drift-v2/checker-image-candidate-record.json",
            BUILDER.PUBLIC_ISOLATION_CANDIDATE_RECORD:
                "evaluation/target-drift-v2/checker-image-isolation-candidate-record.json",
            BUILDER.PUBLIC_AGENT_LIFECYCLE_RECORD:
                "evaluation/target-drift-v2/agent-lifecycle-candidate-record.json",
            BUILDER.PUBLIC_AGENT_IMAGE_RECORD:
                "evaluation/target-drift-v2/agent-image-candidate-record.json",
            BUILDER.PUBLIC_AGENT_OUTER_BOUNDARY_RECORD:
                "evaluation/target-drift-v2/agent-outer-boundary-candidate-record.json",
        }
        anonymous_payload = b"\n".join(payload.values()).lower()
        for public_rel, anonymous_rel in anonymous_records.items():
            public_record = json.loads(
                (BUILDER.REPO_ROOT / public_rel).read_text(encoding="utf-8")
            )
            anonymous_record = json.loads(payload[anonymous_rel].decode("utf-8"))
            self.assertEqual(
                anonymous_record["recorded_at_utc"],
                "<redacted-public-run-time>",
            )
            self.assertEqual(
                anonymous_record["workflow_run"]["job_duration"],
                "<redacted-public-run-duration>",
            )
            self.assertNotIn("artifacts", anonymous_record)
            anonymous_record_bytes = payload[anonymous_rel].lower()
            low_entropy_run_values = [
                public_record["recorded_at_utc"],
                public_record["workflow_run"]["job_duration"],
            ]
            for value in low_entropy_run_values:
                self.assertFalse(
                    value.lower().encode("utf-8") in anonymous_record_bytes,
                    "public run timing remained in " + anonymous_rel,
                )
            unique_values = []
            container_digest = public_record.get("candidate", {}).get(
                "container_image_digest"
            )
            if container_digest:
                unique_values.append(container_digest)
            unique_values.extend(
                item["sha256"] for item in public_record.get("artifacts", [])
                if item.get("sha256") != hashlib.sha256(b"").hexdigest()
            )
            for value in unique_values:
                self.assertFalse(
                    value.lower().encode("utf-8") in anonymous_payload,
                    "public run fingerprint remained in anonymous payload",
                )
        self.assertEqual(
            isolation_candidate["workflow_run"]["id"],
            "<redacted-public-run-id>",
        )
        self.assertEqual(
            isolation_candidate["workflow_run"]["url"],
            "<redacted-public-run-url>",
        )
        self.assertEqual(
            isolation_candidate["workflow_run"]["head_commit"],
            "<anonymous-builder-snapshot>",
        )

    def test_result_free_evaluation_allowlist_is_closed(self):
        tracked = BUILDER.git_tracked_files()
        tracked.add("evaluation/target-drift-v2/run-result.json")
        with self.assertRaisesRegex(ValueError, "unreviewed evaluation file"):
            BUILDER.evaluation_files(tracked)

    def test_outer_candidate_fail_closed_evidence_gates(self):
        source = json.loads((
            BUILDER.REPO_ROOT / BUILDER.PUBLIC_AGENT_OUTER_BOUNDARY_RECORD
        ).read_text(encoding="utf-8"))
        mutations = {
            "failed hash check": (
                lambda record: record["hash_chain_checks"].update({
                    next(iter(record["hash_chain_checks"])): False
                }),
                "hash checks must all pass",
            ),
            "missing source binding": (
                lambda record: record["source_bindings"].pop(),
                "source bindings must match 14 reviewed files",
            ),
            "changed source binding": (
                lambda record: record["source_bindings"][0].update({
                    "path": "tools/unreviewed.py"
                }),
                "source bindings must match 14 reviewed files",
            ),
            "failed workflow": (
                lambda record: record["workflow_run"].update({
                    "conclusion": "failure"
                }),
                "workflow must have succeeded",
            ),
            "provider invocation": (
                lambda record: record["candidate"].update({
                    "provider_request_or_model_invocation_occurred": True
                }),
                "must remain unpublished, unsealed, and provider-free",
            ),
            "provider credential": (
                lambda record: record["candidate"].update({
                    "provider_credential_used": True
                }),
                "must remain unpublished, unsealed, and provider-free",
            ),
            "production seal": (
                lambda record: record["candidate"].update({
                    "production_sealed": True
                }),
                "must remain unpublished, unsealed, and provider-free",
            ),
            "published record": (
                lambda record: record["candidate"].update({
                    "published": True
                }),
                "must remain unpublished, unsealed, and provider-free",
            ),
        }
        for label, (mutate, error) in mutations.items():
            with self.subTest(label=label):
                candidate = json.loads(json.dumps(source))
                mutate(candidate)
                with self.assertRaisesRegex(ValueError, error):
                    BUILDER.anonymous_agent_outer_boundary_candidate(
                        candidate, "0" * 40
                    )

    def test_identity_and_host_path_markers_are_rejected(self):
        with self.assertRaises(ValueError):
            BUILDER.require_anonymous_bytes("bad.txt", b"github.com/DakeBU/project")
        with self.assertRaises(ValueError):
            BUILDER.require_anonymous_bytes("bad.txt", b"C:/Users/example/file")
        with self.assertRaises(ValueError):
            BUILDER.require_anonymous_bytes("bad.txt", b"person@example.edu")
        BUILDER.require_anonymous_bytes("good.txt", b"https://example.org/paper.pdf")

    def test_packaged_verifier_does_not_embed_identity_membership_oracle(self):
        verifier_path = (
            BUILDER.REPO_ROOT / "artifact" / "anonymous-supplement"
            / "verify_artifact.py"
        )
        source = verifier_path.read_bytes().lower()
        for exposed_fragment in (
            b"dake" + b"bu", b"ji" + b" cheng",
            b"city university" + b" of hong kong",
            b"git." + b"overleaf.com",
            b"6a3f743d1f1f53f9" + b"6990c557",
        ):
            self.assertNotIn(exposed_fragment, source)
        self.assertNotIn(b"blocked_identity_digests", source)
        self.assertNotIn(b"contains_blocked_identity", source)
        self.assertIn(b"windows_path", source)
        self.assertIn(b"email", source)

    def test_authoring_workflow_binds_and_runs_the_seven_probe_candidate(self):
        workflow = (
            BUILDER.REPO_ROOT / ".github" / "workflows"
            / "target-drift-checker-image.yml"
        ).read_text(encoding="utf-8")
        self.assertIn("prepare_target_drift_checker_probe_config.py", workflow)
        self.assertIn("finalize_target_drift_config.py bind-runtime", workflow)
        self.assertIn("record_target_drift_checker_isolation_probe.py", workflow)
        self.assertIn('--probe-commit "${GITHUB_SHA}"', workflow)
        self.assertIn('--host-platform "$(uname -srmo)"', workflow)
        self.assertIn("set -o pipefail", workflow)
        self.assertIn("checker-isolation-probe-attempt.log", workflow)
        self.assertIn("Upload the result-free build and isolation evidence", workflow)
        self.assertIn("if: always()", workflow)

    def test_cli_requires_a_bound_graph_and_report(self):
        with self.assertRaises(ValueError):
            BUILDER.build_payload()


if __name__ == "__main__":
    unittest.main()
