#!/usr/bin/env python3
"""Serve the ABRL research-IDE prototype with a loopback-only Lean compiler."""

from __future__ import annotations

import argparse
import json
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
COMPILE_LOCK = threading.Lock()


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


class IDEHandler(SimpleHTTPRequestHandler):
    server_version = "ABRLResearchIDE/0.1"
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
            self.send_json(
                HTTPStatus.OK,
                {
                    "ok": True,
                    "mode": "loopback-local",
                    "lean_version": self.lean_version_text,
                    "source_writes": False,
                },
            )
            return
        super().do_GET()

    def do_POST(self) -> None:  # noqa: N802 - stdlib handler API
        if urlsplit(self.path).path != "/api/compile":
            self.send_json(HTTPStatus.NOT_FOUND, {"ok": False, "output": "Unknown API endpoint."})
            return
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            length = 0
        if length <= 0 or length > MAX_SOURCE_BYTES:
            self.send_json(
                HTTPStatus.REQUEST_ENTITY_TOO_LARGE,
                {"ok": False, "output": f"Lean source must be between 1 and {MAX_SOURCE_BYTES} bytes."},
            )
            return
        try:
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "output": "Request body is not valid UTF-8 JSON."})
            return
        code = payload.get("code") if isinstance(payload, dict) else None
        if not isinstance(code, str) or not code.strip():
            self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "output": "The `code` field must be a nonempty string."})
            return
        if not COMPILE_LOCK.acquire(blocking=False):
            self.send_json(HTTPStatus.TOO_MANY_REQUESTS, {"ok": False, "output": "Another Lean snippet is compiling. Try again shortly."})
            return
        started = time.perf_counter()
        cache_root = SITE_DIR / ".site-cache" / "ide"
        cache_root.mkdir(parents=True, exist_ok=True)
        try:
            with tempfile.TemporaryDirectory(prefix="snippet-", dir=cache_root) as temp_name:
                source = Path(temp_name) / "Main.lean"
                source.write_text(code, encoding="utf-8", newline="\n")
                try:
                    result = subprocess.run(
                        ["lake", "env", "lean", str(source)],
                        cwd=ROOT,
                        capture_output=True,
                        text=True,
                        encoding="utf-8",
                        errors="replace",
                        timeout=self.compile_timeout,
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
                    combined = f"Lean compilation exceeded the {self.compile_timeout}-second local timeout.\n{error.stdout or ''}\n{error.stderr or ''}".strip()
                    status = HTTPStatus.REQUEST_TIMEOUT
                except OSError as error:
                    ok = False
                    combined = f"Could not start the pinned Lean toolchain: {error}"
                    status = HTTPStatus.SERVICE_UNAVAILABLE
        finally:
            COMPILE_LOCK.release()
        duration_ms = round((time.perf_counter() - started) * 1000)
        self.send_json(status, {"ok": ok, "output": combined, "duration_ms": duration_ms})

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
    print(f"ABRL Research IDE: http://{args.host}:{args.port}/ide/")
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
