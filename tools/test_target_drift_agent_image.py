from __future__ import annotations

import hashlib
import io
import json
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import prepare_target_drift_agent_image as image
import record_target_drift_agent_image_probe as probe


ROOT = Path(__file__).resolve().parents[1]


class TargetDriftAgentImageTest(unittest.TestCase):
    def test_source_lock_is_exact_and_result_free(self) -> None:
        payload = image.validate_source_lock(json.loads(
            (ROOT / "evaluation/target-drift-v2/agent-image-sources.json").read_text(
                encoding="utf-8"
            )
        ))
        self.assertEqual(payload["codex_cli"]["version"], "0.130.0")
        self.assertEqual(payload["platform"], "x86_64-unknown-linux-musl")
        self.assertIn("No provider credential", payload["boundary"])

    def test_sri_and_hex_digest_must_agree(self) -> None:
        payload = json.loads(
            (ROOT / "evaluation/target-drift-v2/agent-image-sources.json").read_text(
                encoding="utf-8"
            )
        )
        payload["codex_cli"]["sha512_hex"] = "0" * 128
        with self.assertRaisesRegex(SystemExit, "SRI and hexadecimal"):
            image.validate_source_lock(payload)

    def synthetic_package(self, root: Path, linked: bool = False) -> tuple[Path, dict]:
        lock = json.loads(
            (ROOT / "evaluation/target-drift-v2/agent-image-sources.json").read_text(
                encoding="utf-8"
            )
        )
        package = root / "codex.tgz"
        members = lock["codex_cli"]["required_members"]
        contents = {
            members["codex"]: b"codex-binary",
            members["bwrap"]: b"bwrap-binary",
            members["rg"]: b"rg-binary",
            members["package_json"]: json.dumps({
                "name": "@openai/codex", "version": "0.130.0-linux-x64"
            }).encode("utf-8"),
        }
        with tarfile.open(package, "w:gz") as archive:
            for name, content in contents.items():
                info = tarfile.TarInfo(name)
                info.size = len(content)
                archive.addfile(info, io.BytesIO(content))
            if linked:
                info = tarfile.TarInfo("package/linked")
                info.type = tarfile.SYMTYPE
                info.linkname = "/etc/passwd"
                archive.addfile(info)
        digest = hashlib.sha512(package.read_bytes()).digest()
        lock["codex_cli"]["sha512_hex"] = digest.hex()
        lock["codex_cli"]["sha512_sri"] = (
            "sha512-" + __import__("base64").b64encode(digest).decode("ascii")
        )
        return package, lock

    def test_package_reducer_extracts_only_allowlisted_regular_members(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            package, lock = self.synthetic_package(Path(directory))
            extracted = image.verify_codex_package(package, image.validate_source_lock(lock))
            self.assertEqual(set(extracted), {"codex", "bwrap", "rg", "package_json"})
            self.assertEqual(extracted["codex"], b"codex-binary")

    def test_package_reducer_rejects_any_link(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            package, lock = self.synthetic_package(Path(directory), linked=True)
            with self.assertRaisesRegex(SystemExit, "linked member"):
                image.verify_codex_package(package, image.validate_source_lock(lock))

    def test_containerfile_inherits_cache_and_keeps_pid1(self) -> None:
        recipe = (
            ROOT / "evaluation/target-drift-v2/agent-image.Containerfile"
        ).read_text(encoding="utf-8")
        self.assertIn("FROM ${CHECKER_BASE_IMAGE}", recipe)
        self.assertIn("/opt/abrl-codex/codex", recipe)
        self.assertIn("codex_target_drift_adapter.py", recipe)
        self.assertIn(
            'ENTRYPOINT ["python3", "/usr/local/bin/abrl-agent-pid1"]', recipe
        )
        self.assertNotIn("curl ", recipe)
        self.assertNotIn("npm ", recipe)

    def test_codex_version_observation_allows_daemon_notice(self) -> None:
        payload = (
            b"WARNING: daemon emitted a bounded platform notice\n"
            b"codex-cli 0.130.0\n"
        )
        self.assertEqual(
            image.validate_codex_version_output(payload, "0.130.0"),
            "codex-cli 0.130.0",
        )
        with self.assertRaisesRegex(SystemExit, "differs from the source lock"):
            image.validate_codex_version_output(
                b"codex-cli 0.129.0\n", "0.130.0"
            )
        with self.assertRaisesRegex(SystemExit, "differs from the source lock"):
            image.validate_codex_version_output(
                b"codex-cli 0.130.0\ncodex-cli 0.130.0\n", "0.130.0"
            )
        with self.assertRaisesRegex(SystemExit, "differs from the source lock"):
            image.validate_codex_version_output(
                b"codex-cli 0.129.0\ncodex-cli 0.130.0\n", "0.130.0"
            )
        with self.assertRaisesRegex(SystemExit, "differs from the source lock"):
            image.validate_codex_version_output(
                b" codex-cli 0.130.0 \n", "0.130.0"
            )

    def test_probe_checks_write_network_auth_env_and_pid_boundaries(self) -> None:
        source = probe.probe_source("203.0.113.7").decode("utf-8")
        for marker in (
            "workspace_write_succeeded", "provider_auth_unreadable",
            "persistent_outside_workspace_write_denied", "network_denied",
            "network_error_errno", "openai_api_key_absent", "fresh_pid_namespace",
        ):
            self.assertIn(marker, source)
        self.assertIn("203.0.113.7", source)
        self.assertIn("errno.ENETUNREACH", source)
        self.assertEqual(probe.NETWORK_CONTROL_PORT, 443)

    def test_checker_evidence_cross_binds_raw_sidecars(self) -> None:
        digest = "sha256:" + "1" * 64
        build_payload = {
            "workspace_base_commit": "2" * 40,
            "source_files_aggregate_sha256": "3" * 64,
            "source_files": [{"path": "lean-toolchain", "sha256": "4" * 64}],
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build = root / "build.json"
            cache = root / "cache.json"
            sbom = root / "sbom.json"
            build.write_text("{}\n", encoding="utf-8")
            cache.write_text("{}\n", encoding="utf-8")
            build_sha = image.sha256_file(build)
            cache_sha = image.sha256_file(cache)
            sbom_payload = {
                "schema_version": 1,
                "suite_id": image.SUITE_ID,
                "status": "built_manifest_verified_probe_pending",
                "container_image_digest": digest,
                "build_input_manifest_sha256": build_sha,
                "lake_cache_manifest_sha256": cache_sha,
                "workspace_base_commit": build_payload["workspace_base_commit"],
                "source_snapshot_manifest_sha256": build_payload[
                    "source_files_aggregate_sha256"
                ],
                "checker_image_recipe_sha256": "5" * 64,
                "base_image_digest": "sha256:" + "6" * 64,
            }
            sbom.write_text(json.dumps(sbom_payload) + "\n", encoding="utf-8")
            cache_payload = {"provenance": {
                "workspace_base_commit": build_payload["workspace_base_commit"],
                "source_files_aggregate_sha256": build_payload[
                    "source_files_aggregate_sha256"
                ],
                "build_input_manifest_sha256": build_sha,
                "checker_image_recipe_sha256": "5" * 64,
                "base_image_digest": "6" * 64,
                "lean_toolchain_sha256": "4" * 64,
            }}
            with mock.patch.object(
                image.checker_image, "validate_build_input_payload",
                return_value=build_payload,
            ), mock.patch.object(
                image.checker_image.cache_manifest, "load_manifest",
                return_value=cache_payload,
            ):
                image.validate_checker_evidence(digest, sbom, cache, build)
                sbom_payload["source_snapshot_manifest_sha256"] = "7" * 64
                sbom.write_text(json.dumps(sbom_payload) + "\n", encoding="utf-8")
                with self.assertRaisesRegex(SystemExit, "raw build-input/cache"):
                    image.validate_checker_evidence(digest, sbom, cache, build)

    def test_workflow_builds_and_probes_without_provider_secrets(self) -> None:
        workflow = (
            ROOT / ".github/workflows/target-drift-agent-image.yml"
        ).read_text(encoding="utf-8")
        for marker in (
            "prepare_target_drift_checker_image.py build-image",
            "prepare_target_drift_agent_image.py build-image",
            "record_target_drift_agent_image_probe.py",
            "record_target_drift_agent_lifecycle_probe.py",
            "agent-image-isolation-probe.json",
            "agent-lifecycle-probe.json",
            "--checker-build-input",
            "--containerfile-source evaluation/target-drift-v2/agent-image.Containerfile",
            "--workflow-source .github/workflows/target-drift-agent-image.yml",
        ):
            self.assertIn(marker, workflow)
        self.assertNotIn("secrets.", workflow)
        self.assertIn("if: always()", workflow)


if __name__ == "__main__":
    unittest.main()
