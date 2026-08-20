#!/usr/bin/env python3
"""Unit tests for opaque preparation, neutral checking, and blind packaging."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import check_target_drift_inner as checker_inner  # noqa: E402
import check_target_drift_run as checker_controller  # noqa: E402
import assemble_target_drift_grades as assembler  # noqa: E402
import prepare_target_drift_grading as grading  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402
import record_target_drift_checker_isolation_probe as isolation_probe  # noqa: E402
import launch_target_drift_checker_container as checker_launcher  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402
import prepare_target_drift_checker_image as checker_image  # noqa: E402
import prepare_target_drift_checker_probe_config as checker_probe_config  # noqa: E402
import target_drift_checker_cache_manifest as cache_manifest  # noqa: E402


class TargetDriftRuntimeTest(unittest.TestCase):
    CACHE_PROVENANCE = {
        "workspace_base_commit": "1" * 40,
        "source_files_aggregate_sha256": "2" * 64,
        "build_input_manifest_sha256": "3" * 64,
        "checker_image_recipe_sha256": "4" * 64,
        "base_image_digest": "5" * 64,
        "lean_toolchain_sha256": "6" * 64,
    }

    def test_checker_probe_config_binds_only_result_free_candidate_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            context = root / "context"
            artifacts = root / "artifacts"
            context.mkdir()
            artifacts.mkdir()
            build_input = {"workspace_base_commit": "1" * 40}
            (context / "checker-image-build-input.json").write_text(
                json.dumps(build_input) + "\n", encoding="utf-8"
            )
            for name, payload in (
                ("Containerfile", b"FROM scratch\n"),
                ("check_target_drift_container_controller.py", b"controller\n"),
                ("check_target_drift_inner.py", b"inner\n"),
            ):
                (context / name).write_bytes(payload)
            (artifacts / "checker-cache-manifest.json").write_bytes(b"{}\n")
            (artifacts / "checker-image-build.log").write_bytes(b"build\n")
            sbom = {
                "schema_version": 1,
                "suite_id": "ABRL-TARGET-DRIFT-V2",
                "status": "built_manifest_verified_probe_pending",
                "container_image_digest": "sha256:" + "f" * 64,
                "workspace_base_commit": "1" * 40,
                "build_input_manifest_sha256": prepare.sha256_file(
                    context / "checker-image-build-input.json"
                ),
                "checker_image_recipe_sha256": prepare.sha256_file(
                    context / "Containerfile"
                ),
                "controller_entrypoint_sha256": prepare.sha256_file(
                    context / "check_target_drift_container_controller.py"
                ),
                "inner_checker_sha256": prepare.sha256_file(
                    context / "check_target_drift_inner.py"
                ),
                "lake_cache_manifest_sha256": prepare.sha256_file(
                    artifacts / "checker-cache-manifest.json"
                ),
                "image_build_log_sha256": prepare.sha256_file(
                    artifacts / "checker-image-build.log"
                ),
            }
            (artifacts / "checker-image-sbom.json").write_text(
                json.dumps(sbom) + "\n", encoding="utf-8"
            )
            template = TOOLS.parent / "evaluation" / "target-drift-v2" / "execution-template.json"
            output = root / "probe-draft.json"
            budgets = {
                "wall_clock_seconds": 60,
                "memory_mb": 512,
                "pids_limit": 32,
                "cpus": 1.0,
                "maximum_output_bytes": 4096,
                "maximum_response_bytes": 2048,
            }
            with mock.patch.object(
                checker_probe_config.checker_image, "validate_context",
                return_value=build_input,
            ), mock.patch.object(
                checker_probe_config, "current_commit", return_value="2" * 40
            ):
                config = checker_probe_config.materialize(
                    template, context, artifacts,
                    artifacts / "checker-isolation-probe.json",
                    artifacts / "checker-isolation-probe-artifacts",
                    output, budgets,
                )
            self.assertEqual(config["execution_status"], "template_unfrozen")
            self.assertEqual(config["workspace_base_commit"], "1" * 40)
            checker = config["posthoc_checker"]
            self.assertEqual(checker["mode"], "production")
            self.assertEqual(checker["checker_version"], "candidate-" + "2" * 40)
            self.assertEqual(checker["container_image_digest"], "sha256:" + "f" * 64)
            self.assertEqual(checker["budgets"], budgets)
            self.assertEqual(config["model"]["provider"], "UNSET")
            self.assertIn("model.provider", config["unresolved_fields"])
            self.assertNotIn(b"\r\n", output.read_bytes())
            with self.assertRaises(SystemExit):
                checker_probe_config.materialize(
                    template, context, artifacts,
                    artifacts / "checker-isolation-probe.json",
                    artifacts / "checker-isolation-probe-artifacts",
                    output, budgets,
                )

    def test_checker_probe_config_rejects_noncandidate_sbom(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            context = root / "context"
            artifacts = root / "artifacts"
            context.mkdir()
            artifacts.mkdir()
            build_input = {"workspace_base_commit": "1" * 40}
            for name in (
                "checker-image-build-input.json", "Containerfile",
                "check_target_drift_container_controller.py",
                "check_target_drift_inner.py",
            ):
                (context / name).write_text("{}\n", encoding="utf-8")
            for name in ("checker-cache-manifest.json", "checker-image-build.log"):
                (artifacts / name).write_text("{}\n", encoding="utf-8")
            sbom = {
                "schema_version": 1,
                "suite_id": "ABRL-TARGET-DRIFT-V2",
                "status": "unbuilt_template",
            }
            (artifacts / "checker-image-sbom.json").write_text(
                json.dumps(sbom) + "\n", encoding="utf-8"
            )
            with mock.patch.object(
                checker_probe_config.checker_image, "validate_context",
                return_value=build_input,
            ), self.assertRaises(SystemExit):
                checker_probe_config.materialize(
                    TOOLS.parent / "evaluation" / "target-drift-v2"
                    / "execution-template.json",
                    context, artifacts, artifacts / "probe.json",
                    artifacts / "probe-artifacts", root / "draft.json",
                    {
                        "wall_clock_seconds": 60, "memory_mb": 512,
                        "pids_limit": 32, "cpus": 1.0,
                        "maximum_output_bytes": 4096,
                        "maximum_response_bytes": 2048,
                    },
                )

    def test_checker_cache_manifest_round_trip_and_tamper_rejection(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cache = root / ".lake"
            (cache / "packages" / "mathlib").mkdir(parents=True)
            (cache / "packages" / "mathlib" / "lakefile.lean").write_text(
                "package mathlib\n", encoding="utf-8"
            )
            (cache / "build" / "lib").mkdir(parents=True)
            (cache / "build" / "lib" / "BanditRLProof.olean").write_bytes(b"olean")
            manifest_path = root / "cache-manifest.json"
            payload = cache_manifest.manifest_for(cache, self.CACHE_PROVENANCE)
            cache_manifest.write_new(manifest_path, payload)
            self.assertEqual(cache_manifest.load_manifest(manifest_path), payload)
            self.assertEqual(
                cache_manifest.manifest_for(cache, self.CACHE_PROVENANCE), payload
            )
            (cache / "build" / "lib" / "BanditRLProof.olean").write_bytes(b"tampered")
            self.assertNotEqual(
                cache_manifest.manifest_for(cache, self.CACHE_PROVENANCE), payload
            )

    def test_checker_cache_manifest_rejects_linked_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cache = root / ".lake"
            cache.mkdir()
            source = cache / "source"
            source.write_bytes(b"cache")
            linked = cache / "linked"
            try:
                os.link(source, linked)
            except OSError:
                self.skipTest("hard links are unavailable on this filesystem")
            with self.assertRaises(SystemExit):
                cache_manifest.manifest_for(cache, self.CACHE_PROVENANCE)

    def test_checker_cache_materializes_safe_internal_file_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / ".lake"
            target = cache / "packages" / "batteries" / "README.md"
            target.parent.mkdir(parents=True)
            target.write_bytes(b"trusted documentation\n")
            linked = target.parent / "docs" / "README.md"
            linked.parent.mkdir()
            try:
                linked.symlink_to(Path("..") / "README.md")
            except OSError:
                self.skipTest("symbolic links are unavailable on this filesystem")
            self.assertEqual(
                cache_manifest.materialize_internal_file_symlinks(cache), 1
            )
            self.assertFalse(linked.is_symlink())
            self.assertEqual(linked.read_bytes(), target.read_bytes())
            cache_manifest.manifest_for(cache, self.CACHE_PROVENANCE)

    def test_checker_cache_rejects_external_symlink_materialization(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cache = root / ".lake"
            cache.mkdir()
            outside = root / "outside"
            outside.write_bytes(b"outside")
            linked = cache / "escape"
            try:
                linked.symlink_to(outside)
            except OSError:
                self.skipTest("symbolic links are unavailable on this filesystem")
            with self.assertRaises(SystemExit):
                cache_manifest.materialize_internal_file_symlinks(cache)

    @unittest.skipUnless(os.name == "nt", "Windows junction regression")
    def test_checker_cache_rejects_junction_root(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            outside = root / "outside"
            outside.mkdir()
            (outside / "sentinel").write_bytes(b"outside")
            junction = root / ".lake"
            result = subprocess.run(
                ["cmd", "/c", "mklink", "/J", str(junction), str(outside)],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
            if result.returncode != 0:
                self.skipTest("directory junctions are unavailable")
            with self.assertRaises(SystemExit):
                cache_manifest.materialize_internal_file_symlinks(junction)
            with self.assertRaises(SystemExit):
                cache_manifest.require_plain_tree(junction)
            cli = subprocess.run(
                [
                    sys.executable,
                    str(TOOLS / "target_drift_checker_cache_manifest.py"),
                    "materialize-links",
                    "--root",
                    str(junction),
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
            self.assertNotEqual(cli.returncode, 0)
            self.assertIn("linked, or a reparse point", cli.stdout + cli.stderr)
            self.assertEqual((outside / "sentinel").read_bytes(), b"outside")

    def test_checker_image_context_is_frozen_to_the_base_commit(self) -> None:
        if not (TOOLS.parent / ".git").exists():
            self.skipTest("requires the authoring checkout Git object database")
        # ABRL contains intentionally descriptive Lean filenames.  Keep the
        # Windows build-context root short enough for non-long-path-aware tools.
        temporary_parent = TOOLS.parent.parent if os.name == "nt" else None
        with tempfile.TemporaryDirectory(dir=temporary_parent) as directory:
            output = Path(directory) / "checker-context"
            commit = "d43bfeee56fb0c1c35cf5af9fc1a7fdc3e0c37b9"
            image = "example.invalid/lean@sha256:" + "a" * 64
            checker_image.prepare_context(
                commit, image, output, allow_dirty_test_fixture=True
            )
            payload = checker_image.validate_context(output, allow_test_fixture=True)
            self.assertNotIn(
                b"\r\n", (output / "checker-image-build-input.json").read_bytes()
            )
            self.assertEqual(payload["workspace_base_commit"], commit)
            self.assertEqual(payload["lean_base_image"], image)
            paths = {entry["path"] for entry in payload["source_files"]}
            self.assertIn("BanditRLProof.lean", paths)
            self.assertIn("Tests.lean", paths)
            self.assertFalse(any(path.startswith("evaluation/") for path in paths))
            self.assertFalse(any(".git" in Path(path).parts for path in paths))
            relabeled = json.loads(
                (output / "checker-image-build-input.json").read_text(encoding="utf-8")
            )
            relabeled["workspace_base_commit"] = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=TOOLS.parent, text=True
            ).strip()
            with self.assertRaises(SystemExit):
                checker_image.validate_build_input_payload(relabeled)
            (output / "checker-base" / "lean-toolchain").write_text(
                "tampered\n", encoding="utf-8"
            )
            with self.assertRaises(SystemExit):
                checker_image.validate_context(output)

    def test_checker_containerfile_constructs_cache_from_frozen_context(self) -> None:
        recipe = (TOOLS.parent / "evaluation" / "target-drift-v2"
                  / "checker-image.Containerfile").read_text(encoding="utf-8")
        self.assertIn("FROM ${LEAN_BASE_IMAGE} AS cache-builder", recipe)
        self.assertIn("COPY checker-base/ /build/base/", recipe)
        self.assertIn("lake build BanditRLProof Tests", recipe)
        self.assertIn("target_drift_checker_cache_manifest.py create", recipe)
        self.assertIn("materialize-links --root /build/base/.lake", recipe)
        self.assertIn("--workspace-base-commit", recipe)
        self.assertIn("COPY checker-image-build-input.json", recipe)
        self.assertIn("COPY --from=cache-builder /build/base/.lake", recipe)
        self.assertIn('elan toolchain install "$(cat lean-toolchain)"', recipe)
        self.assertIn("ENV ELAN_HOME=${ABRL_ELAN_HOME}", recipe)
        self.assertIn(
            "COPY --from=cache-builder ${ABRL_ELAN_HOME} ${ABRL_ELAN_HOME}",
            recipe,
        )
        self.assertIn('test -x "${ABRL_ELAN_HOME}/bin/lean"', recipe)
        self.assertGreaterEqual(checker_launcher.MAX_CACHE_MANIFEST_BYTES, 32 * 1024 * 1024)
        self.assertGreater(
            checker_launcher.MAX_CACHE_MANIFEST_BYTES,
            checker_launcher.MAX_RUNTIME_LEDGER_BYTES,
        )
        final_stage = recipe.index("FROM ${LEAN_BASE_IMAGE}\n", recipe.index("AS cache-builder"))
        final_root = recipe.index("USER root", final_stage)
        final_cache_copy = recipe.index("COPY --from=cache-builder", final_stage)
        self.assertLess(final_stage, final_root)
        self.assertLess(final_root, final_cache_copy)

    def test_offline_toolchain_probe_is_networkless_restricted_and_read_only(self) -> None:
        observed: list[list[str]] = []

        def fake_checked(command: list[str], log: Path | None = None) -> bytes:
            self.assertIsNone(log)
            observed.append(command)
            return b""

        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            checker_image, "docker_checked", side_effect=fake_checked
        ), mock.patch.object(checker_image, "docker_cleanup_absent") as cleanup:
            checker_image.offline_image_command(
                Path("docker"), "sha256:" + "f" * 64, Path(directory),
                "lean", ["ToolchainProbe.lean"],
            )
        cleanup.assert_called_once()
        self.assertEqual(len(observed), 1)
        command = observed[0]
        joined = "\0".join(command)
        for required in (
            "--network\0none", "--read-only", "--cap-drop\0ALL",
            "--security-opt\0no-new-privileges=true",
            "--user\0" + "10002:10002", "--workdir\0/probe",
            ",dst=/probe,readonly",
        ):
            self.assertIn(required, joined)
        self.assertIn("--pull\0never", joined)

    def test_offline_toolchain_probe_binds_frozen_release(self) -> None:
        calls: list[tuple[str, tuple[str, ...]]] = []

        def fake_run(
            runtime: Path, image_digest: str, probe_root: Path,
            executable: str, arguments: list[str],
        ) -> bytes:
            self.assertTrue((probe_root / "lean-toolchain").is_file())
            self.assertTrue((probe_root / "ToolchainProbe.lean").is_file())
            if os.name != "nt":
                self.assertEqual(probe_root.stat().st_mode & 0o777, 0o755)
                self.assertEqual(
                    (probe_root / "lean-toolchain").stat().st_mode & 0o777, 0o444
                )
            calls.append((executable, tuple(arguments)))
            versions = {
                "lean": b"Lean (version 4.19.0, x86_64-unknown-linux-gnu)\n",
                "lake": b"Lake version 5.0.0 (Lean version 4.19.0)\n",
                "python3": b"Python 3.11.9\n",
            }
            return b"" if arguments == ["ToolchainProbe.lean"] else versions[executable]

        with mock.patch.object(
            checker_image, "offline_image_command", side_effect=fake_run
        ):
            result = checker_image.offline_toolchain_probe(
                Path("docker"), "sha256:" + "f" * 64,
                b"leanprover/lean4:v4.19.0\n",
            )
        self.assertEqual(result["toolchain_release"], "4.19.0")
        self.assertEqual(result["offline_toolchain_probe"],
                         "passed_network_none_as_worker")
        self.assertEqual(len(calls), 4)
        self.assertEqual(
            checker_image.parse_lean_version_output(result["lean_version"]), "4.19.0"
        )
        self.assertEqual(
            checker_image.parse_lake_lean_version_output(result["lake_version"]),
            "4.19.0",
        )
        with self.assertRaises(SystemExit):
            checker_image.parse_lean_toolchain(b"leanprover/lean4:nightly\n")
        with self.assertRaises(SystemExit):
            checker_image.parse_lean_version_output("NOT LEAN; marker 4.19.0")
        with self.assertRaises(SystemExit):
            checker_image.parse_lake_lean_version_output("NOT LAKE; marker 4.19.0")

    def test_checker_image_helper_output_cap_fails_closed(self) -> None:
        with tempfile.TemporaryFile(mode="w+b") as handle:
            with self.assertRaises(SystemExit):
                checker_image.run_to_capped_file(
                    [sys.executable, "-c", "import sys; sys.stdout.write('x' * 4096)"],
                    handle, timeout_seconds=10, max_bytes=32,
                )

    def test_image_extract_cleans_known_name_after_bad_create_response(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            checker_image, "docker_checked", return_value=b"bad id with spaces\n"
        ), mock.patch.object(checker_image, "docker_cleanup_absent") as cleanup:
            with self.assertRaises(SystemExit):
                checker_image.extract_image_file(
                    Path("docker"), "sha256:" + "f" * 64,
                    "/inside", Path(directory) / "output",
                )
        cleanup.assert_called_once()
        self.assertRegex(cleanup.call_args.args[1], r"^abrl-checker-build-audit-")

    def test_checker_image_cleanup_requires_successful_empty_inventory(self) -> None:
        completed = subprocess.CompletedProcess
        with mock.patch.object(checker_image.subprocess, "run", side_effect=[
            completed(["docker", "rm"], 1, b""),
            completed(["docker", "ps"], 0, b""),
        ]):
            checker_image.docker_cleanup_absent(Path("docker"), "audit-name")
        with mock.patch.object(checker_image.subprocess, "run", side_effect=[
            completed(["docker", "rm"], 1, b""),
            completed(["docker", "ps"], 1, b"daemon unavailable"),
        ]):
            with self.assertRaises(SystemExit):
                checker_image.docker_cleanup_absent(Path("docker"), "audit-name")
        with mock.patch.object(checker_image.subprocess, "run", side_effect=[
            completed(["docker", "rm"], 0, b""),
            completed(["docker", "ps"], 0, b"container-id\n"),
        ]):
            with self.assertRaises(SystemExit):
                checker_image.docker_cleanup_absent(Path("docker"), "audit-name")

    def test_production_launcher_constructs_fixed_hardening_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("request.json", "submission.patch"):
                (root / name).write_text("{}\n", encoding="utf-8")
            (root / "base").mkdir()
            (root / "output").mkdir()
            (root / "response").mkdir()
            args = argparse.Namespace(
                response=root / "response" / "response.json",
                request=root / "request.json", base_snapshot=root / "base",
                patch=root / "submission.patch", output=root / "output",
                cidfile=root / "container.cid", attempt_label="CHK-opaque-01",
                controller_uid="0:0", pids_limit=32, memory_mb=256, cpus=1.0,
                controller_entrypoint="/usr/local/bin/abrl-checker-controller",
                image_digest="sha256:" + "f" * 64,
            )
            command = checker_launcher.docker_run_command(args, Path("docker"))
            joined = "\0".join(command)
            for required in (
                "--read-only", "--network\0none", "--cap-drop\0ALL",
                "--cap-add\0SETUID", "--cap-add\0SETGID",
                "--cap-add\0FOWNER", "--cap-add\0DAC_OVERRIDE",
                "--security-opt\0no-new-privileges=true", "--user\0" + "0:0",
                ",dst=/input/request.json,readonly",
                ",dst=/input/base,readonly", ",dst=/input/submission.patch,readonly",
            ):
                self.assertIn(required, joined)
            self.assertEqual(
                [command[index + 1] for index, token in enumerate(command) if token == "--cap-add"],
                ["SETUID", "SETGID", "FOWNER", "DAC_OVERRIDE"],
            )
            self.assertNotIn("--privileged", command)
            self.assertNotIn("--detach", command)

    def test_worker_prefix_is_exact_irreversible_uid_transition(self) -> None:
        checker = {
            "controller_entrypoint": "/usr/local/bin/abrl-checker-controller",
            "worker_uid": "10002:10002",
        }
        prefix = checker_launcher.worker_command_prefix(checker)
        self.assertEqual(prefix, [
            "/usr/local/bin/abrl-checker-controller", "--worker-exec",
            "--uid", "10002", "--gid", "10002", "--",
        ])

    def test_runtime_executable_bytes_are_rechecked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            runtime = Path(directory) / ("docker.exe" if os.name == "nt" else "docker")
            runtime.write_bytes(b"sealed-runtime")
            if os.name != "nt":
                runtime.chmod(0o755)
            digest = prepare.sha256_file(runtime)
            self.assertEqual(
                checker_launcher.regular_executable(runtime.resolve(), digest, "runtime"),
                runtime.resolve(),
            )
            runtime.write_bytes(b"mutated-runtime")
            if os.name != "nt":
                runtime.chmod(0o755)
            with self.assertRaises(SystemExit):
                checker_launcher.regular_executable(runtime.resolve(), digest, "runtime")

    @unittest.skipIf(os.name == "nt", "POSIX execute bits are not available on Windows")
    def test_interpreted_launcher_is_hash_bound_without_requiring_execute_bit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            launcher = Path(directory) / "launcher.py"
            launcher.write_text("print('sealed')\n", encoding="utf-8")
            launcher.chmod(0o644)
            digest = prepare.sha256_file(launcher)
            self.assertEqual(
                checker_launcher.regular_protected_file(
                    launcher.resolve(), digest, "launcher"
                ),
                launcher.resolve(),
            )
            with self.assertRaises(SystemExit):
                checker_launcher.regular_executable(
                    launcher.resolve(), digest, "launcher"
                )

    def test_temporary_path_fake_docker_is_not_an_allowlisted_runtime(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fake = Path(directory) / ("docker.exe" if os.name == "nt" else "docker")
            fake.write_bytes(b"fabricated-runtime")
            if os.name != "nt":
                fake.chmod(0o755)
            with mock.patch.object(checker_launcher.shutil, "which", return_value=str(fake)):
                with self.assertRaises(SystemExit):
                    checker_launcher.canonical_docker_executable()

    def test_unbuilt_checker_sbom_is_rejected(self) -> None:
        sbom = json.loads(
            (TOOLS.parent / "evaluation" / "target-drift-v2"
             / "checker-image-sbom.template.json").read_text(encoding="utf-8")
        )
        entry = {
            "container_image_digest": "sha256:" + "f" * 64,
            "checker_image_recipe_sha256": "a" * 64,
            "controller_entrypoint_sha256": "b" * 64,
            "controller_uid": "0:0", "worker_uid": "10002:10002",
            "checker_cache_root": checker_launcher.CHECKER_CACHE_ROOT,
            "checker_cache_manifest_path": checker_launcher.CHECKER_CACHE_MANIFEST_PATH,
            "checker_cache_manifest_sha256": "d" * 64,
            "container_runtime_executable_sha256": "7" * 64,
        }
        with self.assertRaises(SystemExit):
            prepare.validate_checker_image_sbom(entry, sbom, "c" * 64)

    def test_built_checker_sbom_rejects_unset_toolchain_or_cache_fields(self) -> None:
        entry = {
            "container_image_digest": "sha256:" + "f" * 64,
            "checker_image_recipe_sha256": "a" * 64,
            "controller_entrypoint_sha256": "b" * 64,
            "controller_uid": "0:0", "worker_uid": "10002:10002",
            "checker_cache_root": checker_launcher.CHECKER_CACHE_ROOT,
            "checker_cache_manifest_path": checker_launcher.CHECKER_CACHE_MANIFEST_PATH,
            "checker_cache_manifest_sha256": "d" * 64,
            "container_runtime_executable_sha256": "7" * 64,
        }
        sbom = {
            "schema_version": 1, "suite_id": "ABRL-TARGET-DRIFT-V2",
            "status": "built_manifest_verified_probe_pending",
            "container_image_digest": entry["container_image_digest"],
            "checker_image_recipe_sha256": entry["checker_image_recipe_sha256"],
            "controller_entrypoint_sha256": entry["controller_entrypoint_sha256"],
            "inner_checker_sha256": "c" * 64,
            "controller_uid": entry["controller_uid"], "worker_uid": entry["worker_uid"],
            "base_image_digest": "sha256:" + "e" * 64,
            "base_image_reference": "example.invalid/lean@sha256:" + "e" * 64,
            "toolchain_release": "4.19.0",
            "offline_toolchain_probe": "passed_network_none_as_worker",
            "toolchain_probe_source_sha256": prepare.sha256_bytes(
                checker_image.TOOLCHAIN_PROBE_SOURCE
            ),
            "workspace_base_commit": "1" * 40,
            "cache_manifest_tool_sha256": prepare.sha256_file(
                TOOLS / "target_drift_checker_cache_manifest.py"
            ),
            "image_context_builder_sha256": prepare.sha256_file(
                TOOLS / "prepare_target_drift_checker_image.py"
            ),
            "build_input_manifest_sha256": "4" * 64,
            "source_snapshot_manifest_sha256": "5" * 64,
            "image_build_log_sha256": "6" * 64,
            "docker_executable_sha256": "7" * 64,
            "docker_runtime_identity": {
                "runtime_id": "docker", "runtime_version": "client=1;server=1;os=linux",
                "runtime_signature_output_sha256": "8" * 64,
                "runtime_version_output_sha256": "9" * 64,
                "daemon_identity_output_sha256": "a" * 64,
            },
            "lean_version": "UNSET", "lake_version": "UNSET", "python_version": "UNSET",
            "lake_cache_manifest_sha256": "d" * 64,
            "checker_cache_root": checker_launcher.CHECKER_CACHE_ROOT,
            "checker_cache_manifest_path": checker_launcher.CHECKER_CACHE_MANIFEST_PATH,
            "nonclaim": (
                "Component-level image record; production probes and model runs remain absent."
            ),
        }
        with self.assertRaises(SystemExit):
            prepare.validate_checker_image_sbom(entry, sbom, "c" * 64)
        sbom.update({
            "lean_version": "Lean (version 4.19.0, x86_64-unknown-linux-gnu)",
            "lake_version": "Lake version 5.0.0 (Lean version 4.19.0)",
            "python_version": "Python 3.11.9",
        })
        prepare.validate_checker_image_sbom(entry, sbom, "c" * 64)
        build_input = {
            "source_files_aggregate_sha256": "5" * 64,
            "lean_base_image": sbom["base_image_reference"],
        }
        cache_payload = {"provenance": {"build_input_manifest_sha256": "4" * 64}}
        prepare.validate_checker_image_sbom(
            entry, sbom, "c" * 64, "1" * 40, build_input, cache_payload,
            "4" * 64, "6" * 64, sbom["docker_runtime_identity"],
        )
        wrong_suite = dict(sbom)
        wrong_suite["suite_id"] = "OTHER-SUITE"
        with self.assertRaises(SystemExit):
            prepare.validate_checker_image_sbom(entry, wrong_suite, "c" * 64)
        with self.assertRaises(SystemExit):
            prepare.validate_checker_image_sbom(
                entry, sbom, "c" * 64, "1" * 40, build_input, cache_payload,
                "0" * 64, "6" * 64, sbom["docker_runtime_identity"],
            )

    def test_complete_lake_cache_manifest_binds_every_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "packages" / "mathlib").mkdir(parents=True)
            target = root / "packages" / "mathlib" / "lake-manifest.json"
            target.write_text("{}\n", encoding="utf-8")
            entries = checker_inner.complete_cache_manifest(root)
            digest = checker_inner.cache_manifest_aggregate(entries)
            target.write_text('{"changed":true}\n', encoding="utf-8")
            changed = checker_inner.complete_cache_manifest(root)
            self.assertNotEqual(entries, changed)
            self.assertNotEqual(digest, checker_inner.cache_manifest_aggregate(changed))

    def test_cache_seed_copy_is_performed_by_the_worker_process(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "image-cache"
            target = root / "replay" / ".lake"
            (source / "packages" / "mathlib").mkdir(parents=True)
            (source / "packages" / "mathlib" / "cache.olean").write_bytes(b"olean")
            target.mkdir(parents=True)
            target.chmod(0o777)
            outcome = subprocess.run(
                [sys.executable, "-c", checker_inner.CACHE_COPY_SCRIPT,
                 str(source), str(target)],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
            )
            self.assertEqual(outcome.returncode, 0, outcome.stdout.decode(errors="replace"))
            self.assertEqual(
                checker_inner.complete_cache_manifest(source),
                checker_inner.complete_cache_manifest(target),
            )

    def test_image_inspection_binds_digest_entrypoint_and_root_controller(self) -> None:
        digest = "sha256:" + "f" * 64
        payload = {
            "Id": digest,
            "Config": {
                "Entrypoint": [checker_launcher.CONTROLLER_PATH],
                "User": "0:0",
            },
        }
        checker_launcher.validate_image_inspect(
            payload, digest, checker_launcher.CONTROLLER_PATH
        )
        payload["Config"]["Entrypoint"] = ["/unsealed/controller"]
        with self.assertRaises(SystemExit):
            checker_launcher.validate_image_inspect(
                payload, digest, checker_launcher.CONTROLLER_PATH
            )

    def test_opaque_ids_are_deterministic_and_do_not_echo_semantics(self) -> None:
        semantic = "DBOBW-01-ALGORITHM-IDENTITY--abrl--replicate-7"
        first = runner.opaque_id("run", "a" * 64, semantic)
        second = runner.opaque_id("run", "a" * 64, semantic)
        self.assertEqual(first, second)
        self.assertNotIn("DBOBW", first)
        self.assertRegex(first, r"^RUN-[0-9a-f]{20}$")

    def test_prompt_rendering_removes_every_placeholder(self) -> None:
        template = " ".join(
            (
                "{{CASE_ID}}",
                "{{SOURCE_ID}}",
                "{{SOURCE_LOCATOR}}",
                "{{SOURCE_PACKET_PATH}}",
                "{{PROPOSED_REQUIREMENT}}",
                "{{WORKSPACE_PATH}}",
            )
        )
        rendered = runner.render_prompt(
            template,
            "CASE-opaque",
            "SOURCE-opaque",
            "Lemma 4.2",
            Path("source.pdf"),
            "preserve the exact target",
            Path("workspace"),
        )
        self.assertNotIn("{{", rendered)
        self.assertIn("CASE-opaque", rendered)
        self.assertIn("preserve the exact target", rendered)
        self.assertIn(runner.BLIND_GRADING_TEXT_RULE, rendered)

    def test_every_workflow_prompt_appends_blind_grading_text_contract(self) -> None:
        prompt_root = TOOLS.parent / "evaluation" / "target-drift-v1" / "prompts"
        for condition in ("compile-only", "source-aware-blueprint", "abrl"):
            with self.subTest(condition=condition):
                template = (prompt_root / f"{condition}.md").read_text(encoding="utf-8")
                rendered = runner.render_prompt(
                    template,
                    "CASE-opaque",
                    "SOURCE-opaque",
                    "source locator",
                    Path("source.pdf"),
                    "preserve the exact target",
                    Path("workspace"),
                )
                self.assertIn("Blind-grading requirement:", rendered)
                self.assertIn(runner.BLIND_GRADING_TEXT_RULE, rendered)

    def test_forbidden_scan_finds_semantic_identifier(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "prompt.md").write_text("DBOBW-01-ALGORITHM-IDENTITY", encoding="utf-8")
            hits = runner.scan_forbidden(root, ["DBOBW-01-ALGORITHM-IDENTITY"])
            self.assertEqual(hits[0]["path"], "prompt.md")

    def test_agent_manifest_excludes_infrastructure_lake_cache(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "workspace" / ".lake").mkdir(parents=True)
            (root / "workspace" / ".lake" / "cache.olean").write_bytes(b"cache")
            (root / "prompt.md").write_text("prompt", encoding="utf-8")
            self.assertEqual(
                [entry["path"] for entry in runner.file_manifest(root)],
                ["prompt.md"],
            )
            self.assertEqual(
                runner.manifest_sha256(runner.file_manifest(root)),
                grading.manifest_sha256(grading.agent_manifest(root)),
            )

    def test_agent_manifest_rejects_model_created_hardlinks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.txt"
            linked = root / "linked.txt"
            source.write_text("model output", encoding="utf-8")
            try:
                os.link(source, linked)
            except OSError:
                self.skipTest("hard links are unavailable on this filesystem")
            with self.assertRaises(SystemExit):
                runner.file_manifest(root)

    def test_neutral_checker_flags_proof_escape_hatches(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Unsafe.lean"
            path.write_text(
                "axiom bad : False\nconstant hidden : False\ntheorem t : True := by sorry\n",
                encoding="utf-8",
            )
            hits = checker_inner.scan_lean(root, ["Unsafe.lean"])
            self.assertEqual({hit["kind"] for hit in hits}, {"axiom", "constant", "sorry"})

    def test_public_abrl_locator_is_not_scanned_but_agent_provenance_is(self) -> None:
        packet = {
            "source_locator": "ABRL textbook-card chapter 7",
            "agent_final_status": "partial",
            "public_declarations": [],
            "primary_grader_rationale": "The requested inequality remains unproved.",
            "source_amendment": None,
            "lean_artifacts": [],
        }
        grading.require_blind_text(grading.agent_generated_blind_fields(packet), "packet")
        packet["primary_grader_rationale"] = "The ABRL promotion gate passed."
        with self.assertRaises(SystemExit):
            grading.require_blind_text(grading.agent_generated_blind_fields(packet), "packet")

    def test_axiom_parser_distinguishes_kernel_axioms_from_new_constants(self) -> None:
        output = "t depends on axioms: [propext, Classical.choice, hiddenProof]"
        self.assertEqual(
            checker_inner.parsed_axioms(output),
            {"propext", "Classical.choice", "hiddenProof"},
        )

    def test_checker_sandbox_command_renders_windows_paths_without_a_shell(self) -> None:
        command = checker_controller.render_command(
            ["fixture.exe", "--request", "{{CHECKER_REQUEST_PATH}}", "--cid", "{{CIDFILE}}"],
            {
                "{{CHECKER_REQUEST_PATH}}": r"C:\path with spaces\request.json",
                "{{CIDFILE}}": r"C:\path with spaces\container.cid",
            },
        )
        self.assertEqual(command[2], r"C:\path with spaces\request.json")
        self.assertEqual(command[4], r"C:\path with spaces\container.cid")

    def test_checker_sandbox_command_rejects_unresolved_placeholders(self) -> None:
        with self.assertRaises(checker_controller.CheckerFailure):
            checker_controller.render_command(
                ["fixture.exe", "{{MISSING}}"], {"{{OTHER}}": "value"}
            )

    def test_checker_attempt_ids_bind_attempt_number(self) -> None:
        first = checker_controller.checker_attempt_id(
            "a" * 64, "RUN-opaque", "b" * 64, "c" * 64, "d" * 64,
            "e" * 64, 1
        )
        second = checker_controller.checker_attempt_id(
            "a" * 64, "RUN-opaque", "b" * 64, "c" * 64, "d" * 64,
            "e" * 64, 2
        )
        self.assertNotEqual(first, second)
        self.assertTrue(first.endswith("-01"))

    def test_checker_preflight_exception_records_single_terminal_attempt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pack = root / "pack"
            operator = root / "run" / "operator"
            pack.mkdir()
            operator.mkdir(parents=True)
            config = {"posthoc_checker": {
                "driver_sha256": "a" * 64,
                "inner_checker_sha256": "b" * 64,
                "runtime_config_sha256": "c" * 64,
            }}
            (pack / "execution_config.json").write_text(
                json.dumps(config), encoding="utf-8"
            )
            (pack / "aggregate.sha256").write_text("d" * 64 + "\n", encoding="ascii")
            (operator / "job.json").write_text(
                json.dumps({"opaque_run_id": "RUN-opaque"}), encoding="utf-8"
            )
            (operator / "run_state.json").write_text(json.dumps({
                "status": "executed_unchecked", "opaque_run_id": "RUN-opaque",
                "execution_receipt_sha256": "e" * 64,
            }), encoding="utf-8")
            with mock.patch.object(
                checker_controller, "preflight", side_effect=KeyError("public_declarations")
            ):
                with self.assertRaises(checker_controller.CheckerFailure):
                    checker_controller.execute(pack, root / "run")
            state = json.loads((operator / "run_state.json").read_text(encoding="utf-8"))
            self.assertEqual(state["status"], "checker_terminal_failure")
            failures = list((operator / "checker-attempts").glob("*/terminal-failure.json"))
            self.assertEqual(len(failures), 1)
            with self.assertRaises(checker_controller.CheckerFailure):
                checker_controller.execute(pack, root / "run")
    def test_checker_artifact_manifest_is_hash_bound(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "checker-result.json").write_text("{}\n", encoding="utf-8")
            manifest = checker_controller.regular_artifact_manifest(root, 1024)
            digest = checker_controller.artifact_aggregate(manifest)
            (root / "checker-result.json").write_text('{"changed":true}\n', encoding="utf-8")
            changed = checker_controller.regular_artifact_manifest(root, 1024)
            self.assertNotEqual(digest, checker_controller.artifact_aggregate(changed))

    def test_checker_lifecycle_is_inspected_cleaned_and_absent(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cidfile = root / "container.cid"
            active = root / "container.active"
            run_code = (
                "from pathlib import Path; "
                f"Path({str(cidfile)!r}).write_text('container-123\\n'); "
                f"Path({str(active)!r}).write_text('active')"
            )
            inspect_code = (
                "from pathlib import Path; import sys; "
                f"sys.exit(0 if Path({str(active)!r}).exists() else 3)"
            )
            cleanup_code = f"from pathlib import Path; Path({str(active)!r}).unlink(missing_ok=True)"
            outcome = checker_controller.run_sandbox(
                [sys.executable, "-c", run_code],
                [sys.executable, "-c", cleanup_code],
                [sys.executable, "-c", inspect_code],
                [sys.executable, "-c", cleanup_code],
                [sys.executable, "-c", inspect_code],
                root, 10, 4096, cidfile, 3,
            )
            self.assertTrue(outcome["lifecycle_verified_absent"])
            self.assertEqual(outcome["lifecycle"]["cid"]["inspect_before"]["exit_code"], 0)
            self.assertEqual(outcome["lifecycle"]["cid"]["inspect_after"]["exit_code"], 3)

    def test_checker_stdout_is_hard_capped(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            outcome = checker_controller.run_capped_process(
                [sys.executable, "-c", "import sys; sys.stdout.write('x' * 1000000)"],
                root, 10, 1024,
            )
            self.assertTrue(outcome["output_limit_exceeded"])
            self.assertLessEqual(len(outcome["output"].encode("utf-8")), 1024)

    def test_checker_monitor_exception_still_runs_dual_cleanup(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cidfile = root / "container.cid"
            outcomes = [0, 0, 3, 0, 0, 3]

            def fake_run(command, cwd, timeout, maximum):
                if command == ["launch"]:
                    cidfile.write_text("container-123\n", encoding="ascii")
                    raise OSError("monitor failed after launch")
                code = outcomes.pop(0)
                return {
                    "command": command, "exit_code": code, "timed_out": False,
                    "output_limit_exceeded": False, "wall_seconds": 0.0, "output": "",
                }

            with mock.patch.object(
                checker_controller, "run_capped_process", side_effect=fake_run
            ) as invoked:
                with self.assertRaises(checker_controller.CheckerFailure):
                    checker_controller.run_sandbox(
                        ["launch"], ["cid-clean"], ["cid-inspect"],
                        ["label-clean"], ["label-inspect"], root, 10, 1024, cidfile, 3,
                    )
            self.assertEqual(invoked.call_count, 7)
            self.assertFalse(outcomes)

    def test_checker_lifecycle_failure_preserves_bounded_process_diagnostics(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cidfile = root / "container.cid"
            records = {
                "launch": {
                    "command": ["launch"], "exit_code": 17, "timed_out": False,
                    "output_limit_exceeded": False, "wall_seconds": 0.1,
                    "output": "sealed runtime mismatch\n",
                },
                "inspect": {
                    "command": ["inspect"], "exit_code": 9, "timed_out": False,
                    "output_limit_exceeded": False, "wall_seconds": 0.1,
                    "output": "inspect diagnostic\n",
                },
                "cleanup": {
                    "command": ["cleanup"], "exit_code": 8, "timed_out": False,
                    "output_limit_exceeded": False, "wall_seconds": 0.1,
                    "output": "cleanup diagnostic\n",
                },
            }

            def fake_run(command, cwd, timeout, maximum):
                if command == ["launch"]:
                    return records["launch"]
                if "cleanup" in command[0]:
                    return records["cleanup"]
                return records["inspect"]

            with mock.patch.object(
                checker_controller, "run_capped_process", side_effect=fake_run
            ):
                with self.assertRaises(checker_controller.CheckerFailure) as raised:
                    checker_controller.run_sandbox(
                        ["launch"], ["cid-cleanup"], ["cid-inspect"],
                        ["label-cleanup"], ["label-inspect"], root, 10, 4096,
                        cidfile, 3,
                    )
            message = str(raised.exception)
            self.assertIn("launch: exit=17", message)
            self.assertIn("sealed runtime mismatch", message)
            self.assertIn("cid inspect-before: exit=9", message)
            self.assertIn("inspect diagnostic", message)
            self.assertIn("label cleanup: exit=8", message)
            self.assertIn("cleanup diagnostic", message)

    def test_checker_response_is_bounded_regular_json(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "response.json"
            path.write_text('{"ok": true}\n', encoding="utf-8")
            self.assertEqual(
                checker_controller.load_bounded_regular_json(path, 64, "response"),
                {"ok": True},
            )
            with self.assertRaises(checker_controller.CheckerFailure):
                checker_controller.load_bounded_regular_json(path, 4, "response")

    def test_checker_artifact_manifest_rejects_hardlinks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = root / "first.json"
            second = root / "second.json"
            first.write_text("{}\n", encoding="utf-8")
            try:
                os.link(first, second)
            except OSError:
                self.skipTest("hard links unavailable on this filesystem")
            with self.assertRaises(checker_controller.CheckerFailure):
                checker_controller.regular_artifact_manifest(root, 1024)

    def test_checker_result_rejects_string_false(self) -> None:
        request = {
            "sealed_pack_sha256": "a" * 64,
            "execution_receipt_sha256": "b" * 64,
            "completed_agent_manifest_sha256": "c" * 64,
            "final_status": "partial",
            "public_declarations": [],
            "inner_checker_sha256": "d" * 64,
            "checker_contract_sha256": "e" * 64,
            "container_image_digest": "sha256:" + "f" * 64,
            "checker_runtime_config_sha256": "1" * 64,
        }
        result = {
            "schema_version": 1, "opaque_run_id": "RUN", "checker_attempt_id": "ATT",
            "checker_pass": "false", "changed_files": [], "deleted_files": [],
            "forbidden_lean_hits": [], "replay_forbidden_lean_hits": [],
            "replay_changed_files": [], "replay_deleted_files": [],
            "patch_check": {}, "patch_apply": {},
            "replayed_content_matches_completed_workspace": False,
            "post_worker_content_unchanged": False,
            "public_declarations_absent_from_frozen_base": False,
            "cache_prelude": None, "neutral_build": {}, "neutral_canary": None,
            "public_declarations": [], "axiom_dependencies": [], "unexpected_axioms": [],
            "artifact_replay_success": False, "workflow_compliance_pass": True,
            "execution_usage": {}, "sealed_pack_sha256": request["sealed_pack_sha256"],
            "execution_receipt_sha256": request["execution_receipt_sha256"],
            "completed_agent_manifest_sha256": request["completed_agent_manifest_sha256"],
            "agent_claimed_status": "partial", "claim_consistent_with_checker": True,
            "inner_checker_sha256": request["inner_checker_sha256"],
            "checker_contract_sha256": request["checker_contract_sha256"],
            "container_image_digest": request["container_image_digest"],
            "checker_runtime_config_sha256": request["checker_runtime_config_sha256"],
        }
        with self.assertRaises(checker_controller.CheckerFailure):
            checker_controller.validate_checker_result(result, request, "RUN", "ATT")

    def test_compiled_checker_result_requires_successful_declaration_canary(self) -> None:
        request = {
            "sealed_pack_sha256": "a" * 64, "execution_receipt_sha256": "b" * 64,
            "completed_agent_manifest_sha256": "c" * 64, "final_status": "compiled",
            "public_declarations": ["BanditRLProof.X"], "inner_checker_sha256": "d" * 64,
            "checker_contract_sha256": "e" * 64,
            "container_image_digest": "sha256:" + "f" * 64,
            "checker_runtime_config_sha256": "1" * 64,
            "worker_command_prefix": ["worker"], "cache_prelude_argv": [],
            "allowed_axioms": ["Classical.choice", "Quot.sound", "propext"],
        }
        patch_check = {"command": ["git", "apply", "--check", "patch"], "exit_code": 0,
                       "timed_out": False, "wall_seconds": 0.1}
        patch_apply = {"command": ["git", "apply", "patch"], "exit_code": 0,
                       "timed_out": False, "wall_seconds": 0.1}
        result = {
            "schema_version": 1, "opaque_run_id": "RUN", "checker_attempt_id": "ATT",
            "checker_pass": True, "changed_files": ["X.lean"], "deleted_files": [],
            "forbidden_lean_hits": [], "replay_forbidden_lean_hits": [],
            "replay_changed_files": ["X.lean"], "replay_deleted_files": [],
            "patch_check": patch_check, "patch_apply": patch_apply,
            "replayed_content_matches_completed_workspace": True,
            "post_worker_content_unchanged": True,
            "public_declarations_absent_from_frozen_base": True,
            "cache_prelude": None,
            "neutral_build": {**patch_apply, "command": ["worker", "lake", "build"]},
            "neutral_canary": None, "public_declarations": ["BanditRLProof.X"],
            "axiom_dependencies": [], "unexpected_axioms": [],
            "artifact_replay_success": True, "workflow_compliance_pass": True,
            "execution_usage": {}, "sealed_pack_sha256": request["sealed_pack_sha256"],
            "execution_receipt_sha256": request["execution_receipt_sha256"],
            "completed_agent_manifest_sha256": request["completed_agent_manifest_sha256"],
            "agent_claimed_status": "compiled", "claim_consistent_with_checker": True,
            "inner_checker_sha256": request["inner_checker_sha256"],
            "checker_contract_sha256": request["checker_contract_sha256"],
            "container_image_digest": request["container_image_digest"],
            "checker_runtime_config_sha256": request["checker_runtime_config_sha256"],
        }
        with self.assertRaises(checker_controller.CheckerFailure):
            checker_controller.validate_checker_result(result, request, "RUN", "ATT")

    def test_formal_grading_rejects_excluded_checker_fixture(self) -> None:
        config = json.loads(
            (TOOLS.parent / "evaluation" / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        config["posthoc_checker"]["mode"] = "excluded_fixture"
        with self.assertRaises(SystemExit):
            grading.require_production_checker(config, {})

    def test_patch_link_mode_is_rejected_before_replay(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            patch = Path(directory) / "link.patch"
            patch.write_text(
                "diff --git a/link b/link\nnew file mode 120000\nindex 0000000..1234567\n",
                encoding="utf-8",
            )
            with self.assertRaises(SystemExit):
                checker_inner.require_patch_has_no_link_mode(patch)

    def test_isolation_probe_response_requires_complete_typed_write_observations(self) -> None:
        nonce = "a" * 48
        label = f"ABRL-PROBE-{nonce}"
        response = {
            "schema_version": 1, "mode": "checker_isolation_probe",
            "probe_nonce": nonce, "checker_attempt_label": label,
            "checker_runtime_config_sha256": "b" * 64,
            "container_image_digest": "sha256:" + "c" * 64,
            "controller_entrypoint_sha256": "d" * 64,
            "process_exit_code": 0,
            "observations": {
                "network_request_succeeded": False,
                "host_sentinel_visible": False,
                "operator_ground_truth_visible": False,
                "background_probe_started": True,
                "worker_effective_capabilities_hex": "0000000000000000",
                "worker_write_succeeded": {
                    key: False for key in isolation_probe.WORKER_WRITE_KEYS
                },
            },
        }
        self.assertEqual(
            isolation_probe.strict_probe_response(
                response, nonce, label, "b" * 64, "sha256:" + "c" * 64,
                "d" * 64,
            )["network_request_succeeded"],
            False,
        )
        response["observations"]["worker_write_succeeded"].pop("checker_response")
        with self.assertRaises(SystemExit):
            isolation_probe.strict_probe_response(
                response, nonce, label, "b" * 64, "sha256:" + "c" * 64,
                "d" * 64,
            )
        response["observations"]["worker_write_succeeded"]["checker_response"] = False
        response["observations"]["worker_effective_capabilities_hex"] = "not-zero"
        with self.assertRaises(SystemExit):
            isolation_probe.strict_probe_response(
                response, nonce, label, "b" * 64, "sha256:" + "c" * 64,
                "d" * 64,
            )

    def test_adapter_usage_must_match_trace_counts_and_budgets(self) -> None:
        response = {
            "model_invocations": [{
                "attempt": 1, "transport": "codex_cli",
                "observable_id_kind": "codex_thread", "observable_id": "thread-1",
                "process_exit_code": 0, "wall_seconds": 1.0, "usage_observed": True,
            }],
            "usage": {
                "input_tokens": 10,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 2,
                "output_tokens": 5,
                "reasoning_output_tokens": 1,
                "tool_calls": 1,
                "build_attempts": 1,
                "recovery_tool_calls": 1,
                "infrastructure_retries": 0,
                "wall_seconds": 2.0,
                "cost_usd": 0.0095,
            }
        }
        events = [
            {"sequence": 0, "kind": "build_attempt", "success": False},
            {"sequence": 1, "kind": "tool_call", "recovery_phase": True},
            {"sequence": 2, "kind": "usage_summary", "usage": response["usage"]},
        ]
        job = {
            "pricing": {
                "input_tokens": 500.0, "cached_input_tokens": 100.0,
                "cache_write_input_tokens": 250.0,
                "output_tokens": 1000.0,
            },
            "budgets": {
                "maximum_input_tokens": 20,
                "maximum_output_tokens": 20,
                "maximum_tool_calls": 2,
                "maximum_build_attempts": 2,
                "wall_clock_seconds": 5,
                "maximum_model_retries": 0,
                "maximum_cost_usd": 1.0,
            },
            "retry_policy": {
                "infrastructure_retry_limit": 0,
                "semantic_failure_retries": 0,
            },
        }
        self.assertEqual(runner.validate_usage(response, events, job)["tool_calls"], 1)
        events[0] = {"sequence": 0, "kind": "build_attempt", "success": True}
        with self.assertRaises(SystemExit):
            runner.validate_usage(response, events, job)

    def test_runner_executes_only_hash_bound_pack_adapter(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            pack = Path(directory) / "pack"
            code = pack / "execution_code"
            code.mkdir(parents=True)
            run_bytes = Path(runner.__file__).read_bytes()
            prepare_bytes = Path(prepare.__file__).read_bytes()
            adapter_bytes = b"print('sealed adapter')\n"
            (code / Path(runner.__file__).name).write_bytes(run_bytes)
            (code / Path(prepare.__file__).name).write_bytes(prepare_bytes)
            sealed_adapter = code / "execution_adapter_entrypoint"
            sealed_adapter.write_bytes(adapter_bytes)
            runtime = Path(sys.executable).resolve()
            config = {
                "sealed_agent_view": {
                    "run_preparer_sha256": hashlib.sha256(run_bytes).hexdigest(),
                    "materializer_sha256": hashlib.sha256(prepare_bytes).hexdigest(),
                },
                "execution_adapter": {
                    "entrypoint_sha256": hashlib.sha256(adapter_bytes).hexdigest(),
                    "runtime_executable": str(runtime),
                    "runtime_executable_sha256": prepare.sha256_file(runtime),
                    "provider_runtime": {
                        "kind": "excluded_fixture", "executable": str(runtime),
                        "executable_sha256": prepare.sha256_file(runtime),
                        "version": prepare.provider_runtime_version_output(runtime).decode(
                            "utf-8"
                        ).strip(),
                        "version_output_sha256": prepare.sha256_bytes(
                            prepare.provider_runtime_version_output(runtime)
                        ),
                    },
                    "command_argv": [str(runtime), "{{ADAPTER_ENTRYPOINT_PATH}}"],
                },
            }
            runner.self_verify(pack, config)
            sealed_adapter.write_bytes(b"print('changed')\n")
            with self.assertRaises(SystemExit):
                runner.self_verify(pack, config)

    def test_model_retry_trace_binds_observable_invocations_and_reason_budget(self) -> None:
        usage = {
            "input_tokens": 10,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 5,
            "reasoning_output_tokens": 1,
            "tool_calls": 0,
            "build_attempts": 0,
            "recovery_tool_calls": 0,
            "infrastructure_retries": 1,
            "wall_seconds": 2.0,
            "cost_usd": 0.01,
        }
        response = {"model_invocations": [
            {"attempt": 1, "transport": "codex_cli",
             "observable_id_kind": "codex_thread", "observable_id": "thread-1",
             "process_exit_code": 1, "wall_seconds": 0.5, "usage_observed": True},
            {"attempt": 2, "transport": "codex_cli",
             "observable_id_kind": "codex_thread", "observable_id": "thread-2",
             "process_exit_code": 0, "wall_seconds": 1.5, "usage_observed": True},
        ], "usage": usage}
        events = [
            {"sequence": 0, "kind": "model_invocation_retry", "reason": "infrastructure"},
            {"sequence": 1, "kind": "usage_summary", "usage": usage},
        ]
        job = {
            "pricing": {
                "input_tokens": 500.0, "cached_input_tokens": 100.0,
                "cache_write_input_tokens": 250.0,
                "output_tokens": 1000.0,
            },
            "budgets": {
                "maximum_input_tokens": 20,
                "maximum_output_tokens": 20,
                "maximum_tool_calls": 2,
                "maximum_build_attempts": 2,
                "wall_clock_seconds": 5,
                "maximum_model_retries": 1,
                "maximum_cost_usd": 1.0,
            },
            "retry_policy": {
                "infrastructure_retry_limit": 1,
                "semantic_failure_retries": 0,
            },
        }
        self.assertEqual(runner.validate_usage(response, events, job)[
            "infrastructure_retries"
        ], 1)
        response["model_invocations"].append({
            "attempt": 3, "transport": "codex_cli",
            "observable_id_kind": "codex_thread", "observable_id": "thread-3",
            "process_exit_code": 0, "wall_seconds": 1.0, "usage_observed": True,
        })
        with self.assertRaises(SystemExit):
            runner.validate_usage(response, events, job)

    def test_unexpected_executor_exception_records_terminal_failure(self) -> None:
        pack = Path("pack")
        run = Path("run")
        with mock.patch.object(runner, "execute_run", side_effect=FileNotFoundError("missing")):
            with mock.patch.object(runner, "record_operator_failure") as record:
                with self.assertRaises(FileNotFoundError):
                    runner.execute_or_record_failure(pack, run)
                record.assert_called_once_with(run, "FileNotFoundError: missing")

    def test_linked_agent_failure_still_records_a_terminal_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            run = Path(directory)
            operator = run / "operator"
            adapter_dir = operator / "adapter"
            agent = run / "agent"
            output = agent / "output"
            adapter_dir.mkdir(parents=True)
            output.mkdir(parents=True)
            prompt = agent / "prompt.md"
            prompt.write_text("protected\n", encoding="utf-8")
            os.link(prompt, output / "lean-diff.patch")
            runner.dump(operator / "run_state.json", {
                "status": "prepared_unrun",
                "opaque_run_id": "opaque",
                "sealed_pack_sha256": "a" * 64,
                "prepared_job_sha256": "b" * 64,
                "workspace_manifest_sha256": "c" * 64,
            })
            runner.record_operator_failure(run, "linked model output")
            receipt = json.loads(
                (operator / "operator-failure-receipt.json").read_text(encoding="utf-8")
            )
            state = json.loads(
                (operator / "run_state.json").read_text(encoding="utf-8")
            )
            self.assertEqual(receipt["status"], "terminal_operator_failure")
            self.assertIsNone(receipt["agent_manifest_at_failure_sha256"])
            self.assertIn("linked", receipt["agent_manifest_at_failure_error"])
            self.assertEqual(state["status"], "terminal_operator_failure")

    def test_invented_source_critical_field_is_rejected(self) -> None:
        grade = {
            "drift_detected": True,
            "false_rejection": False,
            "source_critical_fields": ["invented-field"],
        }
        with self.assertRaises(SystemExit):
            assembler.validate_variant_fields(grade, "injected_drift", {"algorithm identity"})

    def test_grading_digest_is_name_and_payload_sensitive(self) -> None:
        baseline = grading.digest_payloads({"a": b"one", "b": b"two"})
        self.assertNotEqual(baseline, grading.digest_payloads({"a": b"ONE", "b": b"two"}))
        self.assertNotEqual(baseline, grading.digest_payloads({"x": b"one", "b": b"two"}))

    def test_cohen_kappa_handles_agreement_and_degenerate_labels(self) -> None:
        self.assertEqual(assembler.cohen_kappa([True, False], [True, False]), 1.0)
        self.assertIsNone(assembler.cohen_kappa([True, True], [True, True]))


if __name__ == "__main__":
    unittest.main()
