#!/usr/bin/env python3
"""Serve the generated ABRL website behind HTTP Basic Authentication."""

from __future__ import annotations

import argparse
import base64
import hmac
import os
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path


class AuthenticatedStaticHandler(SimpleHTTPRequestHandler):
    """Serve static files only after validating the configured credentials."""

    expected_authorization: str

    def _is_authorized(self) -> bool:
        supplied = self.headers.get("Authorization", "")
        return hmac.compare_digest(supplied, self.expected_authorization)

    def _request_authentication(self) -> None:
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="ABRL private preview"')
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self) -> None:  # noqa: N802 - inherited HTTP handler API
        if not self._is_authorized():
            self._request_authentication()
            return
        super().do_GET()

    def do_HEAD(self) -> None:  # noqa: N802 - inherited HTTP handler API
        if not self._is_authorized():
            self._request_authentication()
            return
        super().do_HEAD()

    def end_headers(self) -> None:
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        super().end_headers()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=Path("website/_site"))
    parser.add_argument("--bind", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8001)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    directory = args.directory.resolve()
    if not directory.is_dir():
        raise SystemExit(f"site directory does not exist: {directory}")

    username = os.environ.get("ABRL_SHARE_USER")
    password = os.environ.get("ABRL_SHARE_PASSWORD")
    if not username or not password:
        raise SystemExit(
            "set ABRL_SHARE_USER and ABRL_SHARE_PASSWORD before starting the server"
        )

    token = base64.b64encode(f"{username}:{password}".encode()).decode()
    AuthenticatedStaticHandler.expected_authorization = f"Basic {token}"
    handler = partial(AuthenticatedStaticHandler, directory=str(directory))

    with ThreadingHTTPServer((args.bind, args.port), handler) as server:
        print(
            f"Serving authenticated ABRL preview at "
            f"http://{args.bind}:{args.port}/",
            flush=True,
        )
        server.serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
