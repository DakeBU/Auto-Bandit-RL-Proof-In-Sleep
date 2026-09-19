"""Reading memberships over the existing Lean index, never a second theorem store."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def unique(items, label):
    result = {}
    for item in items:
        key = item["id"]
        if key in result:
            raise ValueError(f"duplicate {label} ID: {key}")
        result[key] = item
    return result


def topic_formalization_nodes(topic, nodes):
    """Resolve reading references; reviewed packets never imply topic completion."""
    mapping = topic.get("formalization")
    if mapping is None:
        return []
    reviewed = mapping.get("semantic_status") == "accepted-with-explicit-delta"
    if mapping.get("schema_version") != 1 or mapping.get("semantic_status") not in {"review-pending", "accepted-with-explicit-delta"}:
        raise ValueError("topic formalization requires explicit pending independent review")
    receipts = {}
    if reviewed:
        if mapping.get("topic_complete") is not False or not mapping.get("review_receipts"):
            raise ValueError("reviewed topic mapping requires receipts and incomplete topic boundary")
        for receipt in mapping["review_receipts"]:
            relative = receipt.get("path", "")
            path = (ROOT / relative).resolve()
            try:
                path.relative_to(ROOT / "runs")
            except ValueError:
                raise ValueError("invalid topic review receipt path")
            if not relative.startswith("runs/") or not path.is_file():
                raise ValueError("invalid topic review receipt path")
            raw = path.read_bytes()
            if hashlib.sha256(raw).hexdigest() != receipt.get("sha256"):
                raise ValueError("topic review receipt hash drift")
            evidence = json.loads(raw)
            if evidence.get("semantic_verdict") not in {"accepted", "accepted-with-explicit-delta"}:
                raise ValueError("topic receipt lacks independent semantic acceptance")
            if relative in receipts:
                raise ValueError("duplicate topic review receipt")
            receipts[relative] = evidence
    if not re.fullmatch(r"[0-9a-f]{40}", mapping.get("source_commit", "")):
        raise ValueError("topic formalization needs an exact source commit")
    source = mapping.get("source", {})
    if not source.get("title") or not source.get("url", "").startswith("https://") or not re.fullmatch(r"[0-9a-f]{64}", source.get("sha256", "")):
        raise ValueError("topic formalization needs a frozen primary source")
    if not mapping.get("title") or not mapping.get("scope") or not mapping.get("qualifications"):
        raise ValueError("topic formalization must disclose scope and qualifications")
    refs = mapping.get("declarations", [])
    result = []
    for ref in refs:
        if reviewed and ref.get("review_receipt") not in receipts:
            raise ValueError("topic declaration lacks bound review receipt")
        node_id = "declaration:" + ref["name"]
        if node_id not in nodes:
            raise ValueError(f"unknown topic declaration: {node_id}")
        if reviewed:
            evidence = receipts[ref["review_receipt"]]
            module_path = nodes[node_id]["module"].replace(".", "/") + ".lean"
            module_hash = evidence.get("production_hashes", {}).get(module_path)
            if module_hash:
                if hashlib.sha256((ROOT / module_path).read_bytes()).hexdigest() != module_hash:
                    raise ValueError("topic reviewed module hash drift")
            elif ref["name"] not in evidence.get("targets", []):
                raise ValueError("topic receipt does not cover declaration or owning module")
        if ref.get("statement_sha256") != nodes[node_id]["statement_sha256"]:
            raise ValueError(f"topic statement hash drift: {node_id}")
        if ref.get("role") not in {"model", "algorithm", "producer", "endpoint", "canary", "reuse"} or not ref.get("source_locator"):
            raise ValueError(f"missing topic declaration role or source locator: {node_id}")
        if node_id in result:
            raise ValueError(f"duplicate topic declaration: {node_id}")
        result.append(node_id)
    if not result:
        raise ValueError("empty topic formalization mapping")
    return sorted(result)


def build_registry(config, chapters, spine, wiki, declarations, verified, commit):
    if config.get("schema_version") != 1:
        raise ValueError("unsupported book registry schema")
    books = unique(config["books"], "book")
    topics = unique(wiki.get("topics", []), "topic")
    families = unique(wiki["families"], "setting")
    if topics.keys() & families.keys():
        raise ValueError("duplicate setting/topic ID")
    for key in [*books, *topics, *families]:
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", key):
            raise ValueError(f"unsafe route ID: {key}")
    nodes = {}
    for declaration in declarations:
        node_id = "declaration:" + declaration["full_name"]
        if node_id in nodes:
            raise ValueError(f"duplicate canonical ID: {node_id}")
        nodes[node_id] = {
            "id": node_id,
            "module": declaration["module"],
            "url": f"modules/{declaration['module_slug']}/index.html#{declaration['anchor']}",
            "status": "stated" if declaration["placeholder"] or declaration["kind"] == "axiom" else "compiled" if verified else "source",
            "statement_sha256": hashlib.sha256(declaration["statement"].encode()).hexdigest(),
            "identity_basis": "source-private-name" if declaration["private"] else "source-qualified-name",
            "books": [], "chapters": [], "settings": [],
        }
    chapter_registry = {}
    for chapter in chapters:
        chapter_id = "teaching:" + chapter["slug"]
        chapter_registry[chapter_id] = {
            "id": chapter_id, "title": chapter["title"],
            "url": f"chapters/{chapter['slug']}/index.html",
            "node_ids": ["declaration:" + d["full_name"] for d in declarations if d["chapter"] == chapter["slug"]],
        }
    for chapter in spine["chapters"]:
        chapter_id = "spine:" + chapter["slug"]
        names = {item["name"] for item in chapter.get("lean_correspondence", [])}
        names.update(chapter.get("primary_declarations", []))
        chapter_registry[chapter_id] = {
            "id": chapter_id, "title": f"Chapter {chapter['number']}: {chapter['title']}",
            "url": f"textbook-spine/{chapter['slug']}/index.html",
            "node_ids": sorted("declaration:" + name for name in names),
        }
    for chapter in chapter_registry.values():
        for node_id in chapter["node_ids"]:
            if node_id not in nodes:
                raise ValueError(f"unknown declaration reference: {node_id}")
            nodes[node_id]["chapters"].append(chapter["id"])
    for book in books.values():
        if book["status"] not in {"source-mapped", "planned"}:
            raise ValueError("book status is a reading-map status, not a Lean gate")
        refs = book["chapter_refs"]
        if len(refs) != len(set(refs)) or any(ref not in chapter_registry for ref in refs):
            raise ValueError(f"invalid chapter reference in {book['id']}")
        for ref in refs:
            for node_id in chapter_registry[ref]["node_ids"]:
                if book["id"] not in nodes[node_id]["books"]:
                    nodes[node_id]["books"].append(book["id"])
    cases = unique(wiki["cases"], "case")
    settings = {}
    for setting in [*families.values(), *topics.values()]:
        setting_id = setting["id"]
        is_topic = setting_id in topics
        case_refs = [] if is_topic else [c["id"] for c in cases.values() if c["family"] == setting_id]
        for ref in setting.get("related_cases", []):
            if ref not in cases:
                raise ValueError(f"unknown related case: {ref}")
        for ref in setting.get("related_chapters", []):
            if ref not in chapter_registry:
                raise ValueError(f"unknown related chapter: {ref}")
        node_ids = sorted({"declaration:" + name for ref in case_refs for name in cases[ref]["lean"]["declarations"]})
        if is_topic:
            node_ids = topic_formalization_nodes(setting, nodes)
        settings[setting_id] = {
            "id": setting_id, "title": setting["title"],
            "kind": setting.get("kind", "setting"),
            "url": f"banditrlwiki/topics/{setting_id}/index.html" if is_topic else f"banditrlwiki/settings/{setting_id}/index.html",
            "case_refs": case_refs, "node_ids": node_ids,
            "status": ("mapped-reviewed-partial" if node_ids and setting["formalization"]["semantic_status"] == "accepted-with-explicit-delta" else "mapped-review-pending" if node_ids else "source-audit-pending") if is_topic else "case-indexed",
        }
        if is_topic and setting.get("formalization"):
            settings[setting_id]["formalization"] = setting["formalization"]
        for node_id in node_ids:
            if node_id not in nodes:
                raise ValueError(f"unknown setting declaration: {node_id}")
            nodes[node_id]["settings"].append(setting_id)
    return {
        "schema_version": 1, "source_commit": commit, "lean_verified": verified,
        "identity": "declaration:<source-qualified Lean name>; existing IDs preserved; renames require an explicit migration",
        "membership_semantics": "reading references, not proof dependencies or complete textbook coverage",
        "edge_kinds": {
            "module-import": "source-scanned module imports",
            "teaching-prerequisite": "reviewed pedagogical edge, not a proof dependency",
            "lean-type": "compiled environment constant occurrence in declaration type; separate versioned export",
            "lean-value": "compiled environment constant occurrence in declaration value; separate versioned export, not kernel trace",
        },
        "books": list(books.values()), "chapters": list(chapter_registry.values()),
        "settings": list(settings.values()), "nodes": list(nodes.values()),
    }


def membership_index(registry):
    return {node["id"]: node for node in registry["nodes"]}
