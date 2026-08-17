#!/usr/bin/env python3
"""Hard-link a prebuilt `.lake` tree for excluded local plumbing smoke tests.

This fixture is not a sandbox or a substitute for the real image/cache-mount
attestation.  The frozen smoke config names the exact source path and command.
"""

from __future__ import annotations

import argparse
import os
import shutil
from pathlib import Path


def populate_lake_cache(source_lake: Path, workspace: Path) -> None:
    destination = workspace / ".lake"
    if destination.exists():
        return
    if not source_lake.is_dir():
        raise SystemExit(f"prebuilt .lake directory is missing: {source_lake}")
    destination.mkdir()
    for source in source_lake.rglob("*"):
        relative = source.relative_to(source_lake)
        parts = relative.parts
        if any(parts[index:index + 2] == ("build", "ir")
               for index in range(max(0, len(parts) - 1))):
            continue
        target = destination / relative
        if source.is_dir():
            target.mkdir(exist_ok=True)
        elif source.is_file():
            target.parent.mkdir(parents=True, exist_ok=True)
            try:
                os.link(source, target)
            except OSError:
                shutil.copy2(source, target)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prebuilt-lake", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, default=Path.cwd())
    args = parser.parse_args()
    populate_lake_cache(args.prebuilt_lake.resolve(), args.workspace.resolve())


if __name__ == "__main__":
    main()
