#!/usr/bin/env python3
"""PID-1 controller for the production target-drift agent container.

The host launcher keeps Docker stdin open for the lifetime of one adapter run.
If that control channel closes, this controller terminates its direct child and
exits.  Because the controller is PID 1 in a private PID namespace, Linux then
removes every remaining process in that namespace, including descendants that
created a new session or process group.
"""

from __future__ import annotations

import argparse
import json
import os
import queue
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
CONTROL_CHANNEL_EOF = "control_channel_eof"
CHILD_EXITED = "child_exited"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift agent PID-1 controller failed: {message}")


def dump_atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def kill_process_group(process: subprocess.Popen[bytes], grace_seconds: float = 1.0) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + grace_seconds
    while process.poll() is None and time.monotonic() < deadline:
        time.sleep(0.02)
    if process.poll() is None:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def control_channel(events: "queue.Queue[str]") -> None:
    try:
        while sys.stdin.buffer.read(65536):
            pass
    finally:
        events.put(CONTROL_CHANNEL_EOF)


def run_controller(command: list[str], ready: Path, exit_record: Path) -> int:
    require(sys.platform.startswith("linux"), "production lifecycle requires Linux")
    require(os.getpid() == 1, "controller must be PID 1 in a private PID namespace")
    require(bool(command) and all(isinstance(item, str) and item for item in command),
            "controller requires an argv command")

    events: "queue.Queue[str]" = queue.Queue()

    def on_signal(signum: int, _frame: Any) -> None:
        events.put(f"signal_{signum}")

    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(signum, on_signal)

    started = time.monotonic()
    child = subprocess.Popen(command, start_new_session=True)
    dump_atomic(ready, {
        "schema_version": SCHEMA_VERSION,
        "controller_pid": os.getpid(),
        "child_pid": child.pid,
        "control_channel": "docker_stdin",
        "pid_namespace_requirement": "controller_is_pid_1",
    })
    threading.Thread(target=control_channel, args=(events,), daemon=True).start()

    reason = ""
    while not reason:
        try:
            reason = events.get(timeout=0.05)
        except queue.Empty:
            if child.poll() is not None:
                reason = CHILD_EXITED

    if reason != CHILD_EXITED:
        kill_process_group(child)
    else:
        # Kill any descendant that stayed in the child's process group.  A
        # descendant that escaped the group is removed when PID 1 exits.
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    return_code = child.poll()
    if return_code is None:
        try:
            return_code = child.wait(timeout=2)
        except subprocess.TimeoutExpired:
            return_code = -int(signal.SIGKILL)
    dump_atomic(exit_record, {
        "schema_version": SCHEMA_VERSION,
        "reason": reason,
        "child_return_code": return_code,
        "measured_wall_seconds": round(time.monotonic() - started, 6),
        "namespace_cleanup_boundary": "kernel_removes_all_processes_when_pid_1_exits",
    })
    return return_code if reason == CHILD_EXITED and return_code == 0 else 125


def run_fixture(evidence: Path) -> int:
    """Spawn a session-escaping heartbeat process for the lifecycle probe."""
    heartbeat = evidence / "escape-heartbeat.txt"
    child_script = (
        "import pathlib,time,sys; p=pathlib.Path(sys.argv[1]); i=0; "
        "\nwhile True:\n i+=1; p.write_text(str(i)); time.sleep(0.05)"
    )
    escaped = subprocess.Popen(
        [sys.executable, "-c", child_script, str(heartbeat)],
        start_new_session=True,
    )
    dump_atomic(evidence / "fixture.json", {
        "schema_version": SCHEMA_VERSION,
        "fixture_pid": os.getpid(),
        "escaped_session_pid": escaped.pid,
        "escaped_process_group": os.getpgid(escaped.pid),
    })
    while True:
        time.sleep(60)


def main() -> None:
    if sys.argv[1:2] == ["--probe-fixture-child"]:
        require(len(sys.argv) == 3, "probe fixture requires one evidence directory")
        raise SystemExit(run_fixture(Path(sys.argv[2])))
    parser = argparse.ArgumentParser()
    parser.add_argument("--ready-file", type=Path, required=True)
    parser.add_argument("--exit-file", type=Path, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    raise SystemExit(run_controller(command, args.ready_file, args.exit_file))


if __name__ == "__main__":
    main()
