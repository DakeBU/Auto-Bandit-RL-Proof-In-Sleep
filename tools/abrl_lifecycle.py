#!/usr/bin/env python3
"""Deterministic lifecycle primitives for the ABRL proof harness.

This module is intentionally dependency-free.  It keeps authoritative proof
state out of model conversation, supports read-only replay before mutation,
and provides the small concurrency/retry contracts exercised by faux-provider
tests.  It does not execute agents or edit Lean declarations.
"""

from __future__ import annotations

import contextlib
import datetime as _dt
import hashlib
import json
import os
import re
import threading
import time
from collections import Counter
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator, Sequence, TypeVar


SCHEMA_VERSION = 1
MEMORY_TYPES = {
    "verified_lemma",
    "partial_route",
    "failed_path",
    "source_fact",
    "decision",
    "checkpoint",
}
VERIFIED_STATUSES = {"compiled", "accepted", "verified", "leanCompiled"}
READY_DEPENDENCY_STATUSES = VERIFIED_STATUSES | {"available", "satisfied"}
TERMINAL_TRIAL_STATUSES = {"compiled", "accepted"}
FORBIDDEN_LEAN_PATTERN = re.compile(r"\b(sorry|admit|axiom|postulate)\b")
DECLARATION_PATTERN = re.compile(
    r"^(?:noncomputable\s+)?(?:partial\s+)?"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)\b"
)
T = TypeVar("T")


def utc_now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat()


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def content_hash(value: Any) -> str:
    raw = value if isinstance(value, str) else canonical_json(value)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def normalize_statement(statement: str) -> str:
    return re.sub(r"\s+", " ", statement).strip()


def statement_hash(statement: str) -> str:
    return content_hash(normalize_statement(statement))


def stable_id(prefix: str, payload: Any) -> str:
    return f"{prefix}-{content_hash(payload)[:16]}"


def read_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip():
            continue
        value = json.loads(raw)
        if not isinstance(value, dict):
            raise ValueError(f"{path}:{line_number}: JSONL row must be an object")
        rows.append(value)
    return rows


def atomic_write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    suffix = f".{os.getpid()}.{threading.get_ident()}.tmp"
    temporary = path.with_name(path.name + suffix)
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def append_jsonl(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(canonical_json(value) + "\n")
        handle.flush()
        os.fsync(handle.fileno())


def parse_task_from_digest(path: Path) -> str:
    if not path.exists():
        return ""
    text = path.read_text(encoding="utf-8", errors="replace")
    match = re.search(r"^Task:\s*`?([^`\r\n]+)`?\s*$", text, re.MULTILINE)
    return match.group(1).strip() if match else ""


def newest_memory_digest(root: Path) -> Path | None:
    candidates = list((root / "runs").glob("**/memory_digest.md"))
    return max(candidates, key=lambda path: path.stat().st_mtime_ns) if candidates else None


def latest_terminal_trial(rows: Sequence[dict[str, Any]]) -> tuple[int, dict[str, Any]] | None:
    for index in range(len(rows) - 1, -1, -1):
        if rows[index].get("status") in TERMINAL_TRIAL_STATUSES:
            return index, rows[index]
    return None


def reconstruct_frontier(rows: Sequence[dict[str, Any]]) -> dict[str, Any]:
    latest = latest_terminal_trial(rows)
    if latest is None:
        return {
            "selected_task": "",
            "selected_leaf": "",
            "source_status": "missing",
            "last_accepted_verifier": None,
        }
    index, row = latest
    evidence = {
        "trial_index": index,
        "time": row.get("time", ""),
        "task": row.get("task", ""),
        "role": row.get("role", ""),
        "kind": row.get("kind", ""),
        "status": row.get("status", ""),
        "lean": row.get("lean", ""),
        "notes": row.get("notes", ""),
        "run_id": row.get("run_id", ""),
    }
    return {
        "selected_task": row.get("task", ""),
        "selected_leaf": row.get("task", ""),
        "source_status": row.get("status", ""),
        "last_accepted_verifier": evidence,
    }


def analyze_frontier(
    root: Path,
    *,
    trials_path: Path | None = None,
    memory_digest_path: Path | None = None,
    frontier_path: Path | None = None,
) -> dict[str, Any]:
    """Reconstruct lifecycle state without writing any file."""
    trials_path = trials_path or root / "runs" / "trials.jsonl"
    rows = read_jsonl(trials_path)
    inferred = reconstruct_frontier(rows)
    digest_path = memory_digest_path or newest_memory_digest(root)
    digest_task = parse_task_from_digest(digest_path) if digest_path else ""
    frontier_path = frontier_path or root / "runs" / "active_frontier.json"
    recorded = read_json(frontier_path, None)
    mismatches: list[dict[str, str]] = []
    selected_task = str(inferred.get("selected_task", ""))
    if digest_task and selected_task and digest_task != selected_task:
        mismatches.append({
            "kind": "stale_memory_digest",
            "memory_task": digest_task,
            "trial_task": selected_task,
        })
    if recorded:
        recorded_leaf = str(recorded.get("current_leaf", {}).get("id", ""))
        recorded_verifier = recorded.get("last_accepted_verifier") or {}
        recorded_evidence_task = str(
            recorded_verifier.get("task", "")
        )
        if recorded_evidence_task and selected_task and recorded_evidence_task != selected_task:
            mismatches.append({
                "kind": "recorded_verifier_drift",
                "recorded_task": recorded_evidence_task,
                "trial_task": selected_task,
            })
        if not recorded_leaf:
            mismatches.append({
                "kind": "missing_recorded_leaf",
                "recorded_task": recorded_evidence_task,
                "trial_task": selected_task,
            })
    return {
        "schema_version": SCHEMA_VERSION,
        "mode": "shadow-read-only",
        "analyzed_at": utc_now(),
        "trials_path": str(trials_path),
        "trial_rows": len(rows),
        "status_counts": dict(sorted(Counter(str(row.get("status", "")) for row in rows).items())),
        "inferred_frontier": inferred,
        "memory_digest": {
            "path": str(digest_path) if digest_path else "",
            "task": digest_task,
        },
        "recorded_frontier": recorded,
        "mismatches": mismatches,
        "would_mutate": False,
    }


def legacy_prompt(rows: Sequence[dict[str, Any]]) -> str:
    return json.dumps(list(rows), indent=2, ensure_ascii=False)


def trial_transition_indexes(rows: Sequence[dict[str, Any]]) -> list[int]:
    indexes: list[int] = []
    prior_task = ""
    for index, row in enumerate(rows):
        if row.get("status") not in TERMINAL_TRIAL_STATUSES:
            continue
        task = str(row.get("task", ""))
        if task and task != prior_task:
            indexes.append(index)
            prior_task = task
    return indexes


def trial_rows_to_memory(rows: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for index, row in enumerate(rows):
        if row.get("status") not in TERMINAL_TRIAL_STATUSES:
            continue
        task = str(row.get("task", ""))
        record_type = "verified_lemma" if row.get("status") in VERIFIED_STATUSES else "checkpoint"
        payload = {
            "legacy_trial_index": index,
            "task": task,
            "status": row.get("status", ""),
            "lean": row.get("lean", ""),
            "notes": row.get("notes", ""),
        }
        records.append({
            "id": stable_id("mem", payload),
            "type": record_type,
            "created_at": row.get("time", ""),
            "provenance": {"kind": "legacy_trial", "reference": str(index)},
            "task": task,
            "roles": [row.get("role", "lower")],
            "assumptions": [],
            "declaration": row.get("lean", ""),
            "file": "",
            "status": row.get("status", ""),
            "verifier_evidence": [row.get("notes", "")],
            "supersession": {"supersedes": [], "reason": ""},
            "details": payload,
        })
    return records


def replay_transitions(
    rows: Sequence[dict[str, Any]],
    *,
    count: int = 3,
    role: str = "lower",
    memory_limit: int = 5,
) -> dict[str, Any]:
    indexes = trial_transition_indexes(rows)
    selected = indexes[-count:] if count > 0 else []
    reports: list[dict[str, Any]] = []
    for index in selected:
        prefix = list(rows[: index + 1])
        frontier = reconstruct_frontier(prefix)
        records = trial_rows_to_memory(prefix)
        packet = select_memory(records, task=frontier["selected_task"], role=role, limit=memory_limit)
        old_prompt = legacy_prompt(prefix)
        new_prompt = render_memory_packet(packet)
        reports.append({
            "trial_index": index,
            "old_selected_frontier": frontier["selected_task"],
            "new_selected_frontier": frontier["selected_task"],
            "old_prompt_characters": len(old_prompt),
            "new_prompt_characters": len(new_prompt),
            "selected_memory_ids": [record["id"] for record in packet],
        })
    return {
        "schema_version": SCHEMA_VERSION,
        "mode": "shadow-replay",
        "transition_count": len(reports),
        "transitions": reports,
        "would_mutate": False,
    }


def validate_memory_record(record: dict[str, Any]) -> None:
    required = {
        "id",
        "type",
        "created_at",
        "provenance",
        "task",
        "assumptions",
        "declaration",
        "file",
        "status",
        "verifier_evidence",
        "supersession",
    }
    missing = sorted(required - record.keys())
    if missing:
        raise ValueError(f"memory record missing fields: {', '.join(missing)}")
    if record["type"] not in MEMORY_TYPES:
        raise ValueError(f"invalid memory type: {record['type']}")
    if not isinstance(record["provenance"], dict):
        raise ValueError("memory provenance must be an object")
    if not isinstance(record["assumptions"], list):
        raise ValueError("memory assumptions must be a list")
    if not isinstance(record["verifier_evidence"], list):
        raise ValueError("memory verifier_evidence must be a list")
    supersession = record["supersession"]
    if not isinstance(supersession, dict) or not isinstance(supersession.get("supersedes", []), list):
        raise ValueError("memory supersession must contain a supersedes list")


def make_memory_record(
    *,
    record_type: str,
    task: str,
    provenance: dict[str, Any],
    assumptions: Sequence[str] = (),
    declaration: str = "",
    file: str = "",
    status: str,
    verifier_evidence: Sequence[str] = (),
    supersedes: Sequence[str] = (),
    supersession_reason: str = "",
    roles: Sequence[str] = (),
    details: dict[str, Any] | None = None,
    created_at: str | None = None,
) -> dict[str, Any]:
    core = {
        "type": record_type,
        "task": task,
        "provenance": provenance,
        "assumptions": list(assumptions),
        "declaration": declaration,
        "file": file,
        "status": status,
        "verifier_evidence": list(verifier_evidence),
        "supersession": {
            "supersedes": list(supersedes),
            "reason": supersession_reason,
        },
        "roles": list(roles),
        "details": details or {},
    }
    record = {
        "id": stable_id("mem", core),
        "created_at": created_at or utc_now(),
        **core,
    }
    validate_memory_record(record)
    return record


def active_memory_records(records: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    for record in records:
        validate_memory_record(record)
    superseded = {
        str(record_id)
        for record in records
        for record_id in record.get("supersession", {}).get("supersedes", [])
    }
    return [record for record in records if record["id"] not in superseded]


def select_memory(
    records: Sequence[dict[str, Any]],
    *,
    task: str,
    role: str,
    limit: int = 5,
    explicit_verified_ids: Sequence[str] = (),
) -> list[dict[str, Any]]:
    if limit < 0:
        raise ValueError("memory limit must be nonnegative")
    active = active_memory_records(records)
    by_id = {str(record["id"]): record for record in active}
    explicit: list[dict[str, Any]] = []
    for record_id in explicit_verified_ids:
        record = by_id.get(record_id)
        if record is None:
            raise ValueError(f"verified memory id not found or superseded: {record_id}")
        if record["type"] != "verified_lemma" or record["status"] not in VERIFIED_STATUSES:
            raise ValueError(f"explicit memory id is not a verified lemma: {record_id}")
        explicit.append(record)
    relevant = [
        record
        for record in active
        if record.get("task") == task
        and (not record.get("roles") or role in record.get("roles", []))
        and record["id"] not in {item["id"] for item in explicit}
    ]
    recent = relevant[-limit:] if limit else []
    return explicit + recent


def render_memory_packet(records: Sequence[dict[str, Any]]) -> str:
    payload = {
        "policy": "explicit verified lemmas plus bounded role-relevant recent records",
        "record_count": len(records),
        "records": list(records),
    }
    return json.dumps(payload, indent=2, ensure_ascii=False)


def dependency_fingerprint(node: dict[str, Any]) -> str:
    return content_hash(node.get("dependencies", []))


def missing_dependencies(node: dict[str, Any]) -> list[dict[str, str]]:
    missing: list[dict[str, str]] = []
    for dependency in node.get("dependencies", []):
        if dependency.get("status") not in READY_DEPENDENCY_STATUSES:
            missing.append({
                "kind": str(dependency.get("kind", "unknown")),
                "name": str(dependency.get("name", "")),
                "status": str(dependency.get("status", "missing")),
            })
    return missing


def dispatch_leaf(frontier: dict[str, Any], leaf_id: str) -> dict[str, Any]:
    nodes = frontier.setdefault("dag", {}).setdefault("nodes", [])
    node = next((item for item in nodes if item.get("id") == leaf_id), None)
    if node is None:
        raise ValueError(f"unknown DAG leaf: {leaf_id}")
    if node.get("status") == "running":
        raise ValueError(f"duplicate dispatch rejected for running leaf: {leaf_id}")
    if node.get("status") in VERIFIED_STATUSES:
        raise ValueError(f"terminal leaf cannot be redispatched: {leaf_id}")
    fingerprint = dependency_fingerprint(node)
    missing = missing_dependencies(node)
    if missing:
        if node.get("status") == "blocked" and node.get("blocked_dependency_fingerprint") == fingerprint:
            names = ", ".join(f"{item['kind']}:{item['name']}" for item in missing)
            raise ValueError(f"blocked dependency unchanged for {leaf_id}: {names}")
        node["status"] = "blocked"
        node["missing_dependencies"] = missing
        node["blocked_dependency_fingerprint"] = fingerprint
        return {"dispatched": False, "status": "blocked", "missing_dependencies": missing}
    node["status"] = "running"
    node["missing_dependencies"] = []
    node["blocked_dependency_fingerprint"] = ""
    node["dispatch_count"] = int(node.get("dispatch_count", 0)) + 1
    transaction_id = stable_id("dispatch", {
        "leaf": leaf_id,
        "count": node["dispatch_count"],
        "dependencies": fingerprint,
    })
    node["active_transaction"] = transaction_id
    frontier["current_leaf"] = {
        **frontier.get("current_leaf", {}),
        "id": leaf_id,
        "status": "running",
    }
    return {"dispatched": True, "status": "running", "transaction_id": transaction_id}


def recover_interrupted_frontier(frontier: dict[str, Any]) -> list[str]:
    recovered: list[str] = []
    for node in frontier.get("dag", {}).get("nodes", []):
        if node.get("status") == "running" and node.get("active_transaction"):
            node["status"] = "ready" if not missing_dependencies(node) else "blocked"
            node["recovered_transaction"] = node.pop("active_transaction")
            recovered.append(str(node.get("id", "")))
    if frontier.get("current_leaf", {}).get("id") in recovered:
        frontier["current_leaf"]["status"] = "ready"
    return recovered


def make_frontier_record(
    *,
    root_objective: str,
    leaf_id: str,
    leaf_kind: str,
    statement: str,
    declaration: str,
    file: str,
    source_status: str,
    dependencies: Sequence[dict[str, Any]],
    last_accepted_verifier: dict[str, Any] | None,
    shadow_evidence: dict[str, Any] | None = None,
    leaf_status: str = "ready",
    explicit_verified_lemma_ids: Sequence[str] = (),
) -> dict[str, Any]:
    normalized = normalize_statement(statement)
    record_core = {
        "root_objective": root_objective,
        "current_leaf": {
            "id": leaf_id,
            "kind": leaf_kind,
            "status": leaf_status,
            "statement": normalized,
            "statement_hash": statement_hash(normalized),
            "declaration": declaration,
            "file": file,
            "source_status": source_status,
            "dependencies": list(dependencies),
        },
        "dag": {
            "nodes": [{
                "id": leaf_id,
                "kind": leaf_kind,
                "status": (
                    leaf_status
                    if all(dep.get("status") in READY_DEPENDENCY_STATUSES for dep in dependencies)
                    else "blocked"
                ),
                "dependencies": list(dependencies),
                "dispatch_count": 0,
            }],
        },
        "last_accepted_verifier": last_accepted_verifier,
        "memory_policy": {
            "recent_role_relevant_limit": 5,
            "explicit_verified_lemma_ids": list(explicit_verified_lemma_ids),
            "whole_history_default": False,
        },
        "shadow_gate": shadow_evidence or {"status": "pending"},
        "mutation_policy": {
            "canonical_path_queue": True,
            "cross_process_lock": True,
            "same_file_serialized": True,
            "disjoint_files_parallel": True,
        },
        "autonomous_execution": {
            "enabled": False,
            "requires_deterministic_gates": True,
            "requires_explicit_user_request": True,
        },
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "record_id": stable_id("frontier", record_core),
        "updated_at": utc_now(),
        **record_core,
    }


def _strip_lean_comments(text: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        char = text[index]
        if in_string:
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            result.append(char)
            index += 1
        elif text.startswith("/-", index):
            depth = 1
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                break
            result.append("\n")
            index = end + 1
        else:
            result.append(char)
            index += 1
    return "".join(result)


def lean_declaration_header(path: Path, declaration: str) -> str:
    """Extract one declaration header up to its top-level assignment."""
    text = _strip_lean_comments(path.read_text(encoding="utf-8"))
    short_name = declaration.rsplit(".", 1)[-1]
    pattern = re.compile(
        rf"(?m)^\s*(?:(?:noncomputable|partial)\s+)*"
        rf"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)"
        rf"(?:\s+|\s*\n\s*){re.escape(short_name)}\b"
    )
    match = pattern.search(text)
    if match is None:
        raise ValueError(f"declaration not found in {path}: {declaration}")
    start = match.start()
    bracket_stack: list[str] = []
    in_string = False
    escaped = False
    index = start
    while index < len(text):
        char = text[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        if char in "([{":
            bracket_stack.append(char)
        elif char in ")]}":
            if bracket_stack:
                bracket_stack.pop()
        elif text.startswith(":=", index) and not bracket_stack:
            line_start = text.rfind("\n", start, index) + 1
            line_prefix = text[line_start:index].strip()
            if re.match(r"^(?:.*:\s*)?let(?:I)?\b", line_prefix):
                index += 2
                continue
            return normalize_statement(text[start:index])
        index += 1
    raise ValueError(f"top-level assignment not found for {declaration}")


def make_statement_fence(
    *,
    declaration: str,
    file: str,
    statement: str,
    source_assumptions: Sequence[str] = (),
) -> dict[str, Any]:
    normalized = normalize_statement(statement)
    return {
        "schema_version": SCHEMA_VERSION,
        "declaration": declaration,
        "file": file,
        "statement": normalized,
        "statement_hash": statement_hash(normalized),
        "source_assumptions": list(source_assumptions),
        "created_at": utc_now(),
    }


def safe_verify(
    root: Path,
    fence: dict[str, Any],
    *,
    lean_files: Sequence[Path] | None = None,
) -> dict[str, Any]:
    file_path = root / str(fence["file"])
    current = lean_declaration_header(file_path, str(fence["declaration"]))
    findings: list[dict[str, str]] = []
    current_hash = statement_hash(current)
    if current_hash != fence.get("statement_hash"):
        findings.append({
            "kind": "statement_mutation",
            "expected_hash": str(fence.get("statement_hash", "")),
            "actual_hash": current_hash,
        })
    for assumption in fence.get("source_assumptions", []):
        if normalize_statement(str(assumption)) not in current:
            findings.append({
                "kind": "source_assumption_removed",
                "assumption": str(assumption),
            })
    if lean_files is None:
        lean_files = list((root / "BanditRLProof").rglob("*.lean")) + list(
            (root / "Tests").rglob("*.lean")
        )
    for path in lean_files:
        text = _strip_lean_comments(path.read_text(encoding="utf-8", errors="replace"))
        text = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
        match = FORBIDDEN_LEAN_PATTERN.search(text)
        if match:
            findings.append({
                "kind": "forbidden_lean_declaration",
                "file": str(path),
                "token": match.group(1),
            })
    return {
        "ok": not findings,
        "declaration": fence["declaration"],
        "expected_statement_hash": fence["statement_hash"],
        "actual_statement_hash": current_hash,
        "source_assumptions_preserved": not any(
            item["kind"] == "source_assumption_removed" for item in findings
        ),
        "findings": findings,
    }


class InterProcessFileLock:
    """Small cross-process lock backed by one repository-local lock file."""

    def __init__(self, path: Path, timeout: float = 10.0):
        self.path = path
        self.timeout = timeout
        self.handle: Any = None

    def __enter__(self) -> "InterProcessFileLock":
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.handle = self.path.open("a+b")
        self.handle.seek(0, os.SEEK_END)
        if self.handle.tell() == 0:
            self.handle.write(b"0")
            self.handle.flush()
        deadline = time.monotonic() + self.timeout
        while True:
            try:
                self.handle.seek(0)
                if os.name == "nt":
                    import msvcrt

                    msvcrt.locking(self.handle.fileno(), msvcrt.LK_NBLCK, 1)
                else:
                    import fcntl

                    fcntl.flock(self.handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                return self
            except OSError:
                if time.monotonic() >= deadline:
                    self.handle.close()
                    raise TimeoutError(f"timed out acquiring lock {self.path}")
                time.sleep(0.01)

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        if self.handle is None:
            return
        self.handle.seek(0)
        if os.name == "nt":
            import msvcrt

            msvcrt.locking(self.handle.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl

            fcntl.flock(self.handle.fileno(), fcntl.LOCK_UN)
        self.handle.close()


class RepositoryMutationQueue:
    """Serialize canonical paths in-process and across repository processes."""

    _guard = threading.Lock()
    _locks: dict[str, threading.RLock] = {}

    def __init__(self, root: Path):
        self.root = root.resolve()
        self.lock_dir = self.root / ".abrl" / "locks"

    def canonical(self, path: Path) -> Path:
        candidate = path if path.is_absolute() else self.root / path
        return candidate.resolve()

    @classmethod
    def _thread_lock(cls, key: str) -> threading.RLock:
        with cls._guard:
            return cls._locks.setdefault(key, threading.RLock())

    def _lock_file(self, key: str) -> Path:
        return self.lock_dir / f"{content_hash(key)}.lock"

    def run(self, paths: Sequence[Path], action: Callable[[], T]) -> T:
        keys = sorted({os.path.normcase(str(self.canonical(path))) for path in paths})
        thread_locks = [self._thread_lock(key) for key in keys]
        process_locks = [InterProcessFileLock(self._lock_file(key)) for key in keys]
        with contextlib.ExitStack() as stack:
            for lock in thread_locks:
                stack.enter_context(lock)
            for lock in process_locks:
                stack.enter_context(lock)
            return action()


class SessionStore:
    """Append-only session tree plus a separate deterministic state file."""

    def __init__(self, root: Path, session_id: str):
        self.root = root
        self.session_id = session_id
        self.events_path = root / "runs" / "lifecycle_sessions.jsonl"
        self.state_path = root / ".abrl" / "lifecycle_state.json"
        self.queue = RepositoryMutationQueue(root)

    def _default_state(self) -> dict[str, Any]:
        return {
            "schema_version": SCHEMA_VERSION,
            "session_id": self.session_id,
            "next_sequence": 0,
            "current_entry_id": "",
            "current_leaf": "",
            "branches": {},
            "directive_queue": [],
            "active_transaction": None,
            "active_tool": None,
        }

    def state(self) -> dict[str, Any]:
        state = read_json(self.state_path, self._default_state())
        if state.get("session_id") != self.session_id:
            return self._default_state()
        return state

    def _append_locked(
        self,
        state: dict[str, Any],
        event_type: str,
        payload: dict[str, Any],
        *,
        parent_id: str | None = None,
    ) -> dict[str, Any]:
        sequence = int(state.get("next_sequence", 0))
        effective_parent = (
            str(state.get("current_entry_id", "")) if parent_id is None else parent_id
        )
        identity = {
            "session_id": self.session_id,
            "sequence": sequence,
            "parent_id": effective_parent,
            "event_type": event_type,
            "payload": payload,
        }
        event = {
            "schema_version": SCHEMA_VERSION,
            "entry_id": stable_id("entry", identity),
            "session_id": self.session_id,
            "sequence": sequence,
            "parent_id": effective_parent,
            "event_type": event_type,
            "created_at": utc_now(),
            "payload": payload,
        }
        append_jsonl(self.events_path, event)
        state["next_sequence"] = sequence + 1
        state["current_entry_id"] = event["entry_id"]
        if "current_leaf" in payload:
            state["current_leaf"] = payload["current_leaf"]
        return event

    def append(self, event_type: str, payload: dict[str, Any]) -> dict[str, Any]:
        def mutation() -> dict[str, Any]:
            state = self.state()
            event = self._append_locked(state, event_type, payload)
            atomic_write_json(self.state_path, state)
            return event

        return self.queue.run([self.events_path, self.state_path], mutation)

    def fork(self, branch_id: str, *, abandoned_reason: str, summary: str) -> dict[str, Any]:
        def mutation() -> dict[str, Any]:
            state = self.state()
            event = self._append_locked(state, "branch_fork", {
                "branch_id": branch_id,
                "abandoned_reason": abandoned_reason,
                "summary": summary,
            })
            state.setdefault("branches", {})[branch_id] = {
                "entry_id": event["entry_id"],
                "common_prefix_parent_id": event["parent_id"],
                "abandoned_reason": abandoned_reason,
                "summary": summary,
            }
            atomic_write_json(self.state_path, state)
            return event

        return self.queue.run([self.events_path, self.state_path], mutation)

    def restore_branch(self, branch_id: str) -> dict[str, Any]:
        def mutation() -> dict[str, Any]:
            state = self.state()
            branch = state.get("branches", {}).get(branch_id)
            if branch is None:
                raise ValueError(f"unknown session branch: {branch_id}")
            prior_entry = str(state.get("current_entry_id", ""))
            event = self._append_locked(
                state,
                "branch_restored",
                {
                    "branch_id": branch_id,
                    "restored_from_entry_id": prior_entry,
                    "branch_summary": branch.get("summary", ""),
                },
                parent_id=str(branch["entry_id"]),
            )
            branch["restored_entry_id"] = event["entry_id"]
            atomic_write_json(self.state_path, state)
            return event

        return self.queue.run([self.events_path, self.state_path], mutation)

    def enqueue_directive(self, kind: str, text: str) -> dict[str, Any]:
        if kind not in {"steering", "follow_up"}:
            raise ValueError("directive kind must be steering or follow_up")
        def mutation() -> dict[str, Any]:
            state = self.state()
            event = self._append_locked(state, "directive_queued", {"kind": kind, "text": text})
            state.setdefault("directive_queue", []).append({
                "entry_id": event["entry_id"],
                "kind": kind,
                "text": text,
            })
            atomic_write_json(self.state_path, state)
            return event

        return self.queue.run([self.events_path, self.state_path], mutation)

    def begin_transaction(self, transaction_id: str, current_leaf: str) -> dict[str, Any]:
        def mutation() -> dict[str, Any]:
            state = self.state()
            if state.get("active_transaction"):
                raise ValueError("a lifecycle transaction is already active")
            event = self._append_locked(state, "transaction_started", {
                "transaction_id": transaction_id,
                "current_leaf": current_leaf,
            })
            state["active_transaction"] = transaction_id
            atomic_write_json(self.state_path, state)
            return event

        return self.queue.run([self.events_path, self.state_path], mutation)

    def settle_transaction(self, outcome: str) -> dict[str, Any]:
        def mutation() -> dict[str, Any]:
            state = self.state()
            transaction_id = state.get("active_transaction")
            if not transaction_id:
                raise ValueError("no active lifecycle transaction")
            settled = self._append_locked(state, "transaction_settled", {
                "transaction_id": transaction_id,
                "outcome": outcome,
            })
            state["active_transaction"] = None
            directives = list(state.get("directive_queue", []))
            ordered = [item for item in directives if item["kind"] == "steering"] + [
                item for item in directives if item["kind"] == "follow_up"
            ]
            released: list[dict[str, Any]] = []
            for directive in ordered:
                event_type = (
                    "steering_applied" if directive["kind"] == "steering" else "follow_up_released"
                )
                event = self._append_locked(state, event_type, {
                    "directive_entry_id": directive["entry_id"],
                    "text": directive["text"],
                    "after_transaction": transaction_id,
                })
                released.append({"kind": directive["kind"], "entry_id": event["entry_id"]})
            state["directive_queue"] = []
            state["replan_required"] = any(item["kind"] == "steering" for item in ordered)
            state["released_directives"] = released
            atomic_write_json(self.state_path, state)
            return {"settled": settled, "released": released}

        return self.queue.run([self.events_path, self.state_path], mutation)

    def recover(self) -> dict[str, Any]:
        state = self.state()
        recovered = False
        transaction = state.get("active_transaction")
        if transaction:
            state["active_transaction"] = None
            state["recovered_transaction"] = transaction
            recovered = True
        if state.get("active_tool"):
            state["restored_active_tool"] = state["active_tool"]
            state["active_tool"] = None
            recovered = True
        if recovered:
            self.queue.run([self.state_path], lambda: atomic_write_json(self.state_path, state))
        return state

    @contextlib.contextmanager
    def active_tool(self, tool_name: str) -> Iterator[None]:
        state = self.state()
        previous = state.get("active_tool")
        state["active_tool"] = tool_name
        self.queue.run([self.state_path], lambda: atomic_write_json(self.state_path, state))
        try:
            yield
        finally:
            restored = self.state()
            restored["active_tool"] = previous
            self.queue.run([self.state_path], lambda: atomic_write_json(self.state_path, restored))


def should_compact(measured_provider_usage: int | None, threshold: int) -> bool:
    return measured_provider_usage is not None and measured_provider_usage >= threshold


def compact_context(
    entries: Sequence[dict[str, Any]],
    *,
    measured_provider_usage: int | None,
    threshold: int,
    recent_complete_turns: int = 5,
    authoritative: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if not should_compact(measured_provider_usage, threshold):
        return {
            "compacted": False,
            "entries": list(entries),
            "measured_provider_usage": measured_provider_usage,
        }
    tail = list(entries[-recent_complete_turns:]) if recent_complete_turns else []
    preserved_keys = {
        "declarations",
        "files_read",
        "files_modified",
        "errors",
        "source_assumptions",
    }
    preserved: dict[str, list[Any]] = {key: [] for key in sorted(preserved_keys)}
    for entry in entries:
        payload = entry.get("payload", entry)
        for key in preserved_keys:
            value = payload.get(key)
            if value:
                preserved[key].extend(value if isinstance(value, list) else [value])
    return {
        "compacted": True,
        "measured_provider_usage": measured_provider_usage,
        "threshold": threshold,
        "recent_complete_tail": tail,
        "preserved_exact": preserved,
        "authoritative": authoritative or {},
        "summary_is_advisory": True,
    }


class TransientProviderError(RuntimeError):
    pass


class MathematicalFailure(RuntimeError):
    pass


class LeanGateFailure(RuntimeError):
    pass


def call_with_bounded_retry(
    operation: Callable[[], T],
    *,
    max_retries: int = 2,
    on_event: Callable[[dict[str, Any]], None] | None = None,
) -> tuple[T, list[dict[str, Any]]]:
    events: list[dict[str, Any]] = []
    attempt = 0
    while True:
        try:
            value = operation()
            event = {"kind": "provider_success", "attempt": attempt + 1, "retry_count": attempt}
            events.append(event)
            if on_event:
                on_event(event)
            return value, events
        except TransientProviderError as error:
            event = {
                "kind": "transient_provider_failure",
                "attempt": attempt + 1,
                "retry_count": attempt,
                "error": str(error),
            }
            events.append(event)
            if on_event:
                on_event(event)
            if attempt >= max_retries:
                raise
            attempt += 1


class FauxProvider:
    def __init__(self, outcomes: Sequence[Any]):
        self.outcomes = list(outcomes)
        self.calls = 0

    def __call__(self) -> Any:
        if self.calls >= len(self.outcomes):
            raise AssertionError("faux provider exhausted")
        outcome = self.outcomes[self.calls]
        self.calls += 1
        if isinstance(outcome, BaseException):
            raise outcome
        return outcome


def validate_parallel_lower_routes(routes: Sequence[dict[str, Any]]) -> dict[str, Any]:
    if len(routes) < 2:
        return {"allowed": False, "reason": "fewer than two routes"}
    fingerprints = [str(route.get("route_fingerprint", "")) for route in routes]
    if any(not fingerprint for fingerprint in fingerprints) or len(set(fingerprints)) != len(fingerprints):
        return {"allowed": False, "reason": "routes are not materially distinct"}
    owners: set[str] = set()
    for route in routes:
        if not route.get("expected_information_gain"):
            return {"allowed": False, "reason": "missing expected information gain"}
        files = {os.path.normcase(str(Path(path))) for path in route.get("owned_files", [])}
        if owners.intersection(files):
            return {"allowed": False, "reason": "file ownership overlaps"}
        owners.update(files)
    return {"allowed": True, "reason": "distinct routes with disjoint ownership"}


def discover_skills(
    manifests: Sequence[dict[str, Any]],
    *,
    precedence: dict[str, str] | None = None,
) -> list[dict[str, Any]]:
    required = {"name", "version", "provenance", "allowed_roles", "model_visible"}
    precedence = precedence or {}
    selected: dict[str, dict[str, Any]] = {}
    for manifest in sorted(manifests, key=lambda item: (str(item.get("name", "")), str(item.get("provenance", "")))):
        missing = required - manifest.keys()
        if missing:
            raise ValueError(f"skill manifest missing fields: {', '.join(sorted(missing))}")
        name = str(manifest["name"])
        prior = selected.get(name)
        if prior is None:
            selected[name] = manifest
            continue
        winner = precedence.get(name)
        if not winner:
            raise ValueError(f"skill collision without precedence: {name}")
        candidates = {str(prior["provenance"]): prior, str(manifest["provenance"]): manifest}
        if winner not in candidates:
            raise ValueError(f"skill precedence does not match collision: {name} -> {winner}")
        selected[name] = candidates[winner]
    return [selected[name] for name in sorted(selected)]


def retrieval_record(
    *,
    task: str,
    query: str,
    candidates: Sequence[str],
    rejections: Sequence[dict[str, str]],
    compiled_scratch: str,
    provenance: str,
) -> dict[str, Any]:
    return make_memory_record(
        record_type="source_fact",
        task=task,
        provenance={"kind": "local_first_retrieval", "reference": provenance},
        status="verified" if compiled_scratch else "searched",
        verifier_evidence=[compiled_scratch] if compiled_scratch else [],
        details={
            "query": query,
            "search_order": ["local declarations", "ABRL theorem cards", "Mathlib cards"],
            "candidates": list(candidates),
            "rejections": list(rejections),
            "compiled_scratch": compiled_scratch,
        },
    )
