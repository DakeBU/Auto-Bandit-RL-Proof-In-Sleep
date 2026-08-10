#!/usr/bin/env python3
"""Serve BanditRLlib's loopback-only formalization and Lean compiler UI."""

from __future__ import annotations

import argparse
import json
import sys
import subprocess
import tempfile
import threading
import time
from functools import partial
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit


SCRIPT_DIR = Path(__file__).resolve().parent
SITE_DIR = SCRIPT_DIR.parent
ROOT = SITE_DIR.parent
DEFAULT_SITE = SITE_DIR / "_site"
MAX_SOURCE_BYTES = 200_000
MAX_FORMALIZE_BYTES = 100_000
COMPILE_LOCK = threading.Lock()
FORMALIZE_LOCK = threading.Lock()

sys.path.insert(0, str(ROOT / "tools"))
from bandit_formalizer import (  # noqa: E402 - repository-local tool import
    FormalizationError,
    FormalizationRequest,
    ProviderUnavailableError,
    formalize,
    provider_from_env,
)


def lean_version() -> str:
    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--version"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return f"Lean unavailable: {error}"
    return (result.stdout or result.stderr).strip().splitlines()[0]


def formalizer_health() -> tuple[bool, str]:
    try:
        provider = provider_from_env()
    except ProviderUnavailableError as error:
        return False, str(error)
    return True, provider.name


def compile_lean_source(code: str, timeout: int) -> tuple[int, dict[str, object]]:
    if not COMPILE_LOCK.acquire(blocking=False):
        return HTTPStatus.TOO_MANY_REQUESTS, {
            "ok": False,
            "output": "Another Lean snippet is compiling. Try again shortly.",
        }
    started = time.perf_counter()
    cache_root = SITE_DIR / ".site-cache" / "ide"
    cache_root.mkdir(parents=True, exist_ok=True)
    try:
        with tempfile.TemporaryDirectory(prefix="snippet-", dir=cache_root) as temp_name:
            source = Path(temp_name) / "Main.lean"
            with source.open("w", encoding="utf-8", newline="\n") as handle:
                handle.write(code)
            try:
                result = subprocess.run(
                    ["lake", "env", "lean", str(source)],
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    timeout=timeout,
                    check=False,
                )
                combined = "\n".join(part for part in (result.stdout.strip(), result.stderr.strip()) if part)
                combined = combined.replace(str(source), "Main.lean").replace(str(source.parent), "<temporary>")
                ok = result.returncode == 0
                if not combined:
                    combined = "Lean accepted the snippet." if ok else f"Lean exited with code {result.returncode}."
                status = HTTPStatus.OK
            except subprocess.TimeoutExpired as error:
                ok = False
                combined = (
                    f"Lean compilation exceeded the {timeout}-second local timeout.\n"
                    f"{error.stdout or ''}\n{error.stderr or ''}"
                ).strip()
                status = HTTPStatus.REQUEST_TIMEOUT
            except OSError as error:
                ok = False
                combined = f"Could not start the pinned Lean toolchain: {error}"
                status = HTTPStatus.SERVICE_UNAVAILABLE
    finally:
        COMPILE_LOCK.release()
    duration_ms = round((time.perf_counter() - started) * 1000)
    return status, {"ok": ok, "output": combined, "duration_ms": duration_ms}


class IDEHandler(SimpleHTTPRequestHandler):
    server_version = "BanditRLlibIDE/0.2"
    lean_version_text = "Lean version not checked"
    compile_timeout = 120

    def send_json(self, status: int, payload: dict[str, object]) -> None:
        body = (json.dumps(payload, ensure_ascii=False) + "\n").encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:  # noqa: N802 - stdlib handler API
        if urlsplit(self.path).path == "/api/health":
            formalizer_available, formalizer_detail = formalizer_health()
            self.send_json(
                HTTPStatus.OK,
                {
                    "ok": True,
                    "mode": "loopback-local",
                    "lean_version": self.lean_version_text,
                    "source_writes": False,
                    "formalizer_available": formalizer_available,
                    "formalizer": formalizer_detail,
                },
            )
            return
        super().do_GET()

    def do_POST(self) -> None:  # noqa: N802 - stdlib handler API
        path = urlsplit(self.path).path
        if path not in {"/api/compile", "/api/formalize"}:
            self.send_json(HTTPStatus.NOT_FOUND, {"ok": False, "output": "Unknown API endpoint."})
            return
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            length = 0
        limit = MAX_SOURCE_BYTES if path == "/api/compile" else MAX_FORMALIZE_BYTES
        if length <= 0 or length > limit:
            self.send_json(
                HTTPStatus.REQUEST_ENTITY_TOO_LARGE,
                {"ok": False, "output": f"Request body must be between 1 and {limit} bytes."},
            )
            return
        try:
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "output": "Request body is not valid UTF-8 JSON."})
            return
        if path == "/api/formalize":
            self.handle_formalize(payload)
            return
        code = payload.get("code") if isinstance(payload, dict) else None
        if not isinstance(code, str) or not code.strip():
            self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "output": "The `code` field must be a nonempty string."})
            return
        status, response = compile_lean_source(code, self.compile_timeout)
        self.send_json(status, response)

    def handle_formalize(self, payload: object) -> None:
        if not FORMALIZE_LOCK.acquire(blocking=False):
            self.send_json(
                HTTPStatus.TOO_MANY_REQUESTS,
                {"ok": False, "output": "Another formalization request is running. Try again shortly."},
            )
            return
        try:
            request = FormalizationRequest.from_payload(payload)
            candidate = formalize(request)
            result = candidate.to_dict()
            if candidate.lean_source:
                compile_status, compiler = compile_lean_source(candidate.lean_source, self.compile_timeout)
                compiler_ok = bool(compiler.get("ok"))
                result["lean_status"] = "compiles" if compiler_ok else "rejected"
                result["proof_status"] = "candidate-compiles" if compiler_ok else "unproved"
                result["compiler"] = compiler
                status = compile_status if compile_status != HTTPStatus.OK else HTTPStatus.OK
            else:
                result["compiler"] = {"ok": False, "output": "No candidate Lean source was generated."}
                status = HTTPStatus.SERVICE_UNAVAILABLE if candidate.provider_status == "unavailable" else HTTPStatus.OK
            self.send_json(status, {"ok": candidate.provider_status != "unavailable", "result": result})
        except FormalizationError as error:
            self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "output": str(error)})
        except ProviderUnavailableError as error:
            self.send_json(HTTPStatus.SERVICE_UNAVAILABLE, {"ok": False, "output": str(error)})
        finally:
            FORMALIZE_LOCK.release()

    def log_message(self, format: str, *args: object) -> None:
        # Log request metadata only. Lean source remains in the request body and
        # is intentionally never written to the access log.
        super().log_message(format, *args)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8000)
    parser.add_argument("--directory", type=Path, default=DEFAULT_SITE)
    parser.add_argument("--compile-timeout", type=int, default=120)
    args = parser.parse_args()
    if args.host not in {"127.0.0.1", "localhost", "::1"}:
        raise SystemExit("ide_server.py is intentionally loopback-only; use serve_private.py for static sharing")
    directory = args.directory.resolve()
    if not (directory / "index.html").exists():
        raise SystemExit(f"built site not found at {directory}; run website/scripts/build_site.py first")
    IDEHandler.lean_version_text = lean_version()
    IDEHandler.compile_timeout = max(1, args.compile_timeout)
    handler = partial(IDEHandler, directory=str(directory))
    server = ThreadingHTTPServer((args.host, args.port), handler)
    print(f"BanditRLlib Live Formalization: http://{args.host}:{args.port}/ide/")
    print(f"Lean service: {IDEHandler.lean_version_text}")
    print("Security: loopback only; temporary snippets are deleted after each compile.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
