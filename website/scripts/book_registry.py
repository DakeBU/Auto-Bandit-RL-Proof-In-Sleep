"""Reading memberships over the existing Lean index, never a second theorem store."""
from __future__ import annotations

import hashlib
import re


def unique(items, label):
    result = {}
    for item in items:
        key = item["id"]
        if key in result:
            raise ValueError(f"duplicate {label} ID: {key}")
        result[key] = item
    return result


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
        settings[setting_id] = {
            "id": setting_id, "title": setting["title"],
            "kind": setting.get("kind", "setting"),
            "url": f"banditrlwiki/topics/{setting_id}/index.html" if is_topic else f"banditrlwiki/settings/{setting_id}/index.html",
            "case_refs": case_refs, "node_ids": node_ids,
            "status": "source-audit-pending" if is_topic else "case-indexed",
        }
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
