from __future__ import annotations

import email.message
import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock


TOOLS = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "fetch_target_drift_sources", TOOLS / "fetch_target_drift_sources.py"
)
assert SPEC is not None and SPEC.loader is not None
fetch = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(fetch)


PDF = b"%PDF-1.7\nsource fixture\n%%EOF\n"


class FakeResponse:
    def __init__(
        self, payload: bytes, *, media_type: str = "application/pdf",
        url: str = "https://example.test/source.pdf", status: int = 200
    ) -> None:
        self.payload = payload
        self.offset = 0
        self.status = status
        self.url = url
        self.headers = email.message.Message()
        self.headers["Content-Type"] = media_type
        self.headers["Content-Length"] = str(len(payload))

    def __enter__(self) -> "FakeResponse":
        return self

    def __exit__(self, *_args: object) -> None:
        return None

    def geturl(self) -> str:
        return self.url

    def read(self, size: int = -1) -> bytes:
        if self.offset >= len(self.payload):
            return b""
        end = len(self.payload) if size < 0 else min(len(self.payload), self.offset + size)
        chunk = self.payload[self.offset:end]
        self.offset = end
        return chunk


class FakeOpener:
    def __init__(self, response: FakeResponse) -> None:
        self.response = response
        self.calls = 0

    def open(self, request: object, timeout: int) -> FakeResponse:
        self.calls += 1
        self.request = request
        self.timeout = timeout
        return self.response


def fixtures(payload: bytes = PDF) -> tuple[dict[str, object], dict[str, object]]:
    digest = hashlib.sha256(payload).hexdigest()
    source = {
        "source_id": "SOURCE-1",
        "public_url": "https://example.test/source.pdf",
        "local_path": "UNSET",
        "sha256": digest,
        "edition_note": "test fixture",
    }
    manifest = {
        "schema_version": 2,
        "suite_id": fetch.EXPECTED_SUITE_ID,
        "status": "template_unfrozen",
        "sources": [source, {**source, "source_id": "SOURCE-2"},
                    {**source, "source_id": "SOURCE-3"},
                    {**source, "source_id": "SOURCE-4"}],
    }
    challenges = {
        "cases": [
            {"source_id": source["source_id"], "source_sha256": digest}
            for source in manifest["sources"]
        ]
    }
    return manifest, challenges


class FetchTargetDriftSourcesTests(unittest.TestCase):
    def test_downloads_verified_pdf_to_content_addressed_cache(self) -> None:
        manifest, challenges = fixtures()
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            opener = FakeOpener(FakeResponse(PDF))
            frozen, receipt = fetch.fetch_sources(
                manifest, challenges, cache, opener=opener
            )
            self.assertEqual(frozen["status"], "frozen_ready")
            self.assertEqual(opener.calls, 1)
            expected = hashlib.sha256(PDF).hexdigest()
            path = Path(frozen["sources"][0]["local_path"])
            self.assertEqual(path, cache / "sha256" / expected[:2] / f"{expected}.pdf")
            self.assertEqual(path.read_bytes(), PDF)
            self.assertEqual(receipt[0]["bytes"], len(PDF))

    def test_existing_cache_is_reused_without_network(self) -> None:
        manifest, challenges = fixtures()
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            first = FakeOpener(FakeResponse(PDF))
            fetch.fetch_sources(manifest, challenges, cache, opener=first)
            never = FakeOpener(FakeResponse(b"not used"))
            frozen, _ = fetch.fetch_sources(manifest, challenges, cache, opener=never)
            self.assertEqual(never.calls, 0)
            self.assertEqual(Path(frozen["sources"][0]["local_path"]).read_bytes(), PDF)

    def test_offline_requires_every_cached_pdf(self) -> None:
        manifest, challenges = fixtures()
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(fetch.SourceFetchError, "cache entry is missing"):
                fetch.fetch_sources(manifest, challenges, Path(directory) / "cache", offline=True)

    def test_offline_rejects_corrupted_content_addressed_entry(self) -> None:
        manifest, challenges = fixtures()
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            digest = manifest["sources"][0]["sha256"]
            target = fetch.cache_path(cache, digest)
            target.parent.mkdir(parents=True)
            target.write_bytes(b"not a PDF")
            with self.assertRaisesRegex(fetch.SourceFetchError, "lacks a PDF header"):
                fetch.fetch_sources(manifest, challenges, cache, offline=True)
            self.assertEqual(target.read_bytes(), b"not a PDF")

    def test_hash_mismatch_leaves_no_published_pdf(self) -> None:
        manifest, challenges = fixtures()
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            opener = FakeOpener(FakeResponse(PDF + b"changed"))
            with self.assertRaisesRegex(
                fetch.SourceFetchError, "lacks a PDF EOF marker|SHA-256 mismatch"
            ):
                fetch.fetch_sources(manifest, challenges, cache, opener=opener)
            self.assertEqual(list(cache.rglob("*.pdf")), [])
            self.assertEqual(list(cache.rglob(".partial-*")), [])

    def test_non_pdf_content_type_fails_before_publication(self) -> None:
        manifest, challenges = fixtures()
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            opener = FakeOpener(FakeResponse(PDF, media_type="text/html"))
            with self.assertRaisesRegex(fetch.SourceFetchError, "Content-Type"):
                fetch.fetch_sources(manifest, challenges, cache, opener=opener)
            self.assertEqual(list(cache.rglob("*.pdf")), [])

    def test_template_must_match_challenge_hashes(self) -> None:
        manifest, challenges = fixtures()
        challenges["cases"][0]["source_sha256"] = "0" * 64
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(
                fetch.SourceFetchError, "differs from the frozen challenge"
            ):
                fetch.fetch_sources(manifest, challenges, Path(directory) / "cache")

    def test_template_rejects_non_https_source_url(self) -> None:
        manifest, challenges = fixtures()
        manifest["sources"][0]["public_url"] = "http://example.test/source.pdf"
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(fetch.SourceFetchError, "must use HTTPS"):
                fetch.fetch_sources(manifest, challenges, Path(directory) / "cache")

    def test_cache_and_output_manifest_are_forbidden_inside_repository(self) -> None:
        with self.assertRaisesRegex(
            fetch.SourceFetchError, "outside the Git repository"
        ):
            fetch.external_path(fetch.ROOT / ".tmp" / "sources", "cache root")
        with self.assertRaisesRegex(fetch.SourceFetchError, "outside the Git repository"):
            fetch.external_path(fetch.ROOT / ".tmp" / "sources.json", "output manifest")

    def test_output_manifest_is_newline_terminated_and_never_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "sources.json"
            fetch.write_new_json(output, {"status": "frozen_ready"})
            self.assertTrue(output.read_bytes().endswith(b"\n"))
            self.assertEqual(
                json.loads(output.read_text(encoding="utf-8"))["status"],
                "frozen_ready",
            )
            with self.assertRaisesRegex(fetch.SourceFetchError, "refusing to overwrite"):
                fetch.write_new_json(output, {"status": "changed"})

    def test_output_manifest_race_preserves_competing_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "sources.json"
            competing_payload = b'{"owner":"other-process"}\n'
            original_link = fetch.os.link

            def competing_link(source: object, destination: object) -> None:
                Path(destination).write_bytes(competing_payload)
                original_link(source, destination)

            with mock.patch.object(fetch.os, "link", side_effect=competing_link):
                with self.assertRaisesRegex(
                    fetch.SourceFetchError, "refusing to overwrite"
                ):
                    fetch.write_new_json(output, {"status": "frozen_ready"})

            self.assertEqual(output.read_bytes(), competing_payload)
            self.assertEqual(list(output.parent.glob(".partial-manifest-*")), [])


if __name__ == "__main__":
    unittest.main()
