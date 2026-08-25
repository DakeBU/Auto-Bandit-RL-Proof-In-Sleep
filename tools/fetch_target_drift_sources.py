#!/usr/bin/env python3
"""Fetch and verify the four target-drift-v2 source PDFs without freezing results.

The checked-in source template remains portable and unmodified.  This helper writes
PDF bytes into an operator-selected, content-addressed cache outside the repository
and emits a separate operator-local ``frozen_ready`` source manifest for the existing
preseal pipeline.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import sys
import tempfile
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any, BinaryIO


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "evaluation" / "target-drift-v2" / "source-files.template.json"
DEFAULT_CHALLENGES = ROOT / "evaluation" / "target-drift-v1" / "challenges.json"
EXPECTED_SUITE_ID = "ABRL-TARGET-DRIFT-V2"
MAX_SOURCE_BYTES = 128 * 1024 * 1024
READ_CHUNK_BYTES = 1024 * 1024


class SourceFetchError(RuntimeError):
    """A fail-closed source acquisition or validation error."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SourceFetchError(message)


def load_json(path: Path) -> dict[str, Any]:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            require(key not in result, f"duplicate JSON key {key!r} in {path}")
            result[key] = value
        return result

    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=unique_object
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise SourceFetchError(f"cannot read JSON from {path}: {error}") from error
    require(isinstance(value, dict), f"top-level JSON value in {path} must be an object")
    return value


def is_under(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def external_path(path: Path, label: str) -> Path:
    resolved = path.expanduser().resolve()
    require(
        not is_under(resolved, ROOT.resolve()),
        f"{label} must be outside the Git repository so PDFs and machine paths "
        "cannot be committed",
    )
    return resolved


def validate_https_url(url: Any, label: str) -> str:
    require(isinstance(url, str) and url, f"{label} must be a nonempty string")
    parsed = urllib.parse.urlsplit(url)
    require(parsed.scheme == "https", f"{label} must use HTTPS")
    require(bool(parsed.hostname), f"{label} must name a host")
    require(
        parsed.username is None and parsed.password is None,
        f"{label} must not contain credentials",
    )
    require(not parsed.fragment, f"{label} must not contain a fragment")
    return url


def validate_template(
    manifest: dict[str, Any], challenges: dict[str, Any]
) -> list[dict[str, Any]]:
    require(manifest.get("schema_version") == 2, "source manifest schema_version must be 2")
    require(manifest.get("suite_id") == EXPECTED_SUITE_ID, "source manifest suite_id differs")
    require(
        manifest.get("status") == "template_unfrozen",
        "input source manifest must remain template_unfrozen",
    )
    sources = manifest.get("sources")
    require(isinstance(sources, list) and len(sources) == 4, "expected exactly four source entries")

    challenge_rows = challenges.get("cases")
    require(isinstance(challenge_rows, list) and challenge_rows, "challenge manifest has no cases")
    challenge_hashes: dict[str, str] = {}
    for case in challenge_rows:
        require(isinstance(case, dict), "challenge case must be an object")
        source_id = case.get("source_id")
        digest = case.get("source_sha256")
        require(
            isinstance(source_id, str) and source_id,
            "challenge source_id is invalid",
        )
        require(isinstance(digest, str), f"challenge source hash is missing for {source_id}")
        previous = challenge_hashes.setdefault(source_id, digest)
        require(previous == digest, f"challenge bank carries multiple hashes for {source_id}")

    seen_ids: set[str] = set()
    validated: list[dict[str, Any]] = []
    for source in sources:
        require(isinstance(source, dict), "source entry must be an object")
        require(
            set(source) == {"source_id", "public_url", "local_path", "sha256", "edition_note"},
            "source entry keys differ from the frozen template schema",
        )
        source_id = source["source_id"]
        require(
            isinstance(source_id, str) and source_id,
            "source_id must be a nonempty string",
        )
        require(source_id not in seen_ids, f"duplicate source_id {source_id}")
        seen_ids.add(source_id)
        digest = source["sha256"]
        require(
            isinstance(digest, str)
            and len(digest) == 64
            and all(character in "0123456789abcdef" for character in digest),
            f"source {source_id} must carry a lowercase SHA-256",
        )
        require(
            source["local_path"] == "UNSET",
            f"template local_path must be UNSET for {source_id}",
        )
        validate_https_url(source["public_url"], f"public_url for {source_id}")
        require(
            isinstance(source["edition_note"], str) and source["edition_note"].strip(),
            f"edition_note must be a nonempty string for {source_id}",
        )
        require(
            challenge_hashes.get(source_id) == digest,
            f"source hash for {source_id} differs from the frozen challenge bank",
        )
        validated.append(dict(source))
    require(
        set(challenge_hashes) == seen_ids,
        "source template does not exactly cover challenge sources",
    )
    return validated


def stream_file_facts(
    stream: BinaryIO, output: BinaryIO | None = None
) -> tuple[str, int, bytes, bytes]:
    digest = hashlib.sha256()
    total = 0
    prefix = b""
    tail = b""
    while True:
        chunk = stream.read(READ_CHUNK_BYTES)
        if not chunk:
            break
        require(isinstance(chunk, bytes), "source stream returned non-byte data")
        total += len(chunk)
        require(total <= MAX_SOURCE_BYTES, f"source exceeds {MAX_SOURCE_BYTES} byte limit")
        if len(prefix) < 5:
            prefix = (prefix + chunk)[:5]
        tail = (tail + chunk)[-1024:]
        digest.update(chunk)
        if output is not None:
            output.write(chunk)
    return digest.hexdigest(), total, prefix, tail


def validate_pdf_facts(
    *, source_id: str, expected_sha256: str, actual_sha256: str, size: int,
    prefix: bytes, tail: bytes
) -> None:
    require(size > 0, f"downloaded source is empty for {source_id}")
    require(prefix == b"%PDF-", f"downloaded source lacks a PDF header for {source_id}")
    require(
        tail.rstrip().endswith(b"%%EOF"),
        f"downloaded source lacks a PDF EOF marker for {source_id}",
    )
    require(
        actual_sha256 == expected_sha256,
        f"SHA-256 mismatch for {source_id}: expected {expected_sha256}, got {actual_sha256}",
    )


def validate_cached_pdf(path: Path, source_id: str, expected_sha256: str) -> int:
    require(path.exists(), f"content-addressed cache entry is missing for {source_id}: {path}")
    require(not path.is_symlink(), f"cache entry must not be a symbolic link for {source_id}")
    mode = path.stat().st_mode
    require(stat.S_ISREG(mode), f"cache entry must be a regular file for {source_id}")
    with path.open("rb") as stream:
        actual, size, prefix, tail = stream_file_facts(stream)
    validate_pdf_facts(
        source_id=source_id,
        expected_sha256=expected_sha256,
        actual_sha256=actual,
        size=size,
        prefix=prefix,
        tail=tail,
    )
    return size


class HttpsOnlyRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(
        self, req: urllib.request.Request, fp: Any, code: int, msg: str,
        headers: Any, newurl: str
    ) -> urllib.request.Request | None:
        try:
            validate_https_url(newurl, "redirect URL")
        except SourceFetchError as error:
            raise urllib.error.URLError(str(error)) from error
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def download_pdf(
    source: dict[str, Any], target: Path, opener: Any | None = None
) -> tuple[int, str]:
    source_id = source["source_id"]
    expected = source["sha256"]
    url = validate_https_url(source["public_url"], f"public_url for {source_id}")
    request = urllib.request.Request(
        url,
        headers={"Accept": "application/pdf", "User-Agent": "ABRL-source-freeze/1.0"},
        method="GET",
    )
    opener = opener or urllib.request.build_opener(HttpsOnlyRedirectHandler())
    temporary: Path | None = None
    try:
        try:
            response = opener.open(request, timeout=60)
        except (OSError, urllib.error.URLError, urllib.error.HTTPError) as error:
            raise SourceFetchError(f"HTTPS download failed for {source_id}: {error}") from error
        with response:
            require(
                getattr(response, "status", None) == 200,
                f"HTTP status is not 200 for {source_id}",
            )
            final_url = validate_https_url(response.geturl(), f"effective URL for {source_id}")
            headers = response.headers
            media_type = (
                headers.get_content_type()
                if hasattr(headers, "get_content_type")
                else str(headers.get("Content-Type", "")).split(";", 1)[0].strip().lower()
            )
            require(
                media_type == "application/pdf",
                f"Content-Type is not application/pdf for {source_id}",
            )
            length_text = headers.get("Content-Length")
            expected_length: int | None = None
            if length_text is not None:
                try:
                    expected_length = int(length_text)
                except (TypeError, ValueError) as error:
                    raise SourceFetchError(f"invalid Content-Length for {source_id}") from error
                require(
                    0 < expected_length <= MAX_SOURCE_BYTES,
                    f"Content-Length is invalid for {source_id}",
                )
            require(
                target.parent.is_dir() and not target.parent.is_symlink(),
                f"cache shard directory is not a real directory for {source_id}",
            )
            handle = tempfile.NamedTemporaryFile(
                mode="wb", prefix=".partial-", suffix=".tmp", dir=target.parent, delete=False
            )
            temporary = Path(handle.name)
            with handle:
                actual, size, prefix, tail = stream_file_facts(response, handle)
                handle.flush()
                os.fsync(handle.fileno())
            if expected_length is not None:
                require(
                    size == expected_length,
                    f"download length differs from Content-Length for {source_id}",
                )
            validate_pdf_facts(
                source_id=source_id,
                expected_sha256=expected,
                actual_sha256=actual,
                size=size,
                prefix=prefix,
                tail=tail,
            )

        if target.exists():
            validate_cached_pdf(target, source_id, expected)
        else:
            try:
                os.link(temporary, target)
            except FileExistsError:
                validate_cached_pdf(target, source_id, expected)
            except OSError as error:
                raise SourceFetchError(
                    "cannot atomically publish content-addressed cache entry for "
                    f"{source_id}: {error}"
                ) from error
        return validate_cached_pdf(target, source_id, expected), final_url
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def cache_path(cache_root: Path, digest: str) -> Path:
    return cache_root / "sha256" / digest[:2] / f"{digest}.pdf"


def ensure_cache_shard(cache_root: Path, digest: str) -> None:
    for directory in (cache_root / "sha256", cache_root / "sha256" / digest[:2]):
        if directory.exists():
            require(
                directory.is_dir() and not directory.is_symlink(),
                f"cache component must be a real directory: {directory}",
            )
        else:
            directory.mkdir()
        require(
            is_under(directory.resolve(), cache_root),
            f"cache component escapes the selected cache root: {directory}",
        )


def fetch_sources(
    manifest: dict[str, Any], challenges: dict[str, Any], cache_root: Path,
    *, offline: bool = False, opener: Any | None = None
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    sources = validate_template(manifest, challenges)
    cache_root = external_path(cache_root, "cache root")
    if cache_root.exists():
        require(
            cache_root.is_dir() and not cache_root.is_symlink(),
            "cache root must be a real directory",
        )
    else:
        cache_root.mkdir(parents=True)

    frozen_sources: list[dict[str, Any]] = []
    receipt: list[dict[str, Any]] = []
    for source in sources:
        ensure_cache_shard(cache_root, source["sha256"])
        target = cache_path(cache_root, source["sha256"])
        if offline:
            size = validate_cached_pdf(target, source["source_id"], source["sha256"])
            effective_url = source["public_url"]
        elif target.exists():
            size = validate_cached_pdf(target, source["source_id"], source["sha256"])
            effective_url = source["public_url"]
        else:
            size, effective_url = download_pdf(source, target, opener=opener)
        frozen = dict(source)
        frozen["local_path"] = str(target.resolve())
        frozen_sources.append(frozen)
        receipt.append(
            {
                "source_id": source["source_id"],
                "sha256": source["sha256"],
                "bytes": size,
                "effective_url": effective_url,
                "cache_path": str(target.resolve()),
            }
        )
    return {
        "schema_version": manifest["schema_version"],
        "suite_id": manifest["suite_id"],
        "status": "frozen_ready",
        "sources": frozen_sources,
    }, receipt


def write_new_json(path: Path, value: Any) -> None:
    output = external_path(path, "output manifest")
    require(not output.exists(), f"refusing to overwrite output manifest: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        payload = (
            json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
        ).encode("utf-8")
        handle = tempfile.NamedTemporaryFile(
            mode="wb",
            prefix=".partial-manifest-",
            suffix=".tmp",
            dir=output.parent,
            delete=False,
        )
        temporary = Path(handle.name)
        with handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        try:
            # A hard-link publication is atomic and never replaces an existing path
            # on either POSIX or Windows.  In particular, a concurrent writer that
            # wins after the existence check keeps ownership of its file.
            os.link(temporary, output)
        except FileExistsError as error:
            raise SourceFetchError(
                f"refusing to overwrite output manifest: {output}"
            ) from error
        except OSError as error:
            raise SourceFetchError(
                f"cannot atomically publish output manifest {output}: {error}"
            ) from error
    except OSError as error:
        raise SourceFetchError(f"cannot write output manifest {output}: {error}") from error
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--cache-root", type=Path, required=True)
    parser.add_argument("--output-manifest", type=Path, required=True)
    parser.add_argument(
        "--offline", action="store_true",
        help="forbid downloads and only verify already cached content-addressed PDFs",
    )
    args = parser.parse_args()
    try:
        manifest = load_json(args.manifest.resolve())
        # The hash authority is deliberately not CLI-selectable: it is the frozen,
        # checked-in challenge bank in the same repository snapshot as this tool.
        challenges = load_json(DEFAULT_CHALLENGES)
        output_path = external_path(args.output_manifest, "output manifest")
        require(
            not output_path.exists(),
            f"refusing to overwrite output manifest: {output_path}",
        )
        frozen, receipt = fetch_sources(
            manifest, challenges, args.cache_root, offline=args.offline
        )
        write_new_json(output_path, frozen)
    except SourceFetchError as error:
        raise SystemExit(f"target-drift source fetch failed: {error}") from error

    print(json.dumps({
        "schema_version": 1,
        "suite_id": frozen["suite_id"],
        "status": "source_bytes_verified_result_free",
        "offline": args.offline,
        "output_manifest": str(output_path),
        "sources": receipt,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
