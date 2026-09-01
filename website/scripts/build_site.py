#!/usr/bin/env python3
"""Build the BanditRLlib literate formalization website produced by ABRL."""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import html
import json
import os
import posixpath
import re
import shutil
import subprocess
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
SITE_DIR = SCRIPT_DIR.parent
ROOT = SITE_DIR.parent
CONTENT_DIR = SITE_DIR / "content"
DIAGRAM_DIR = SITE_DIR / "diagrams"
STATIC_DIR = SITE_DIR / "static"
PUBLIC_REPO_DIR = SITE_DIR / "public-repo"
COMMUNITY_DIR = SITE_DIR / "community"
DEFAULT_OUTPUT = SITE_DIR / "_site"
HARNESS_COMPARISON_PATH = ROOT / "runs" / "harness-comparison" / "latest.json"

GITHUB_REPO = "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep"
PUBLIC_SITE_REPO = GITHUB_REPO
PUBLIC_SITE_URL = "https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep"
LIBRARY_NAME = "BanditRLlib"
RESEARCH_PROJECT = "Auto-Bandit-RL-Proof-In-Sleep"
PAPER_TITLE = (
    "ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library "
    "for Bandit and Reinforcement Learning Theory"
)
PRIMARY_TEXTBOOK_TITLE = "Bandit Algorithms"
PRIMARY_TEXTBOOK_AUTHORS = "Tor Lattimore and Csaba Szepesvári"
PRIMARY_TEXTBOOK_URL = "https://tor-lattimore.com/downloads/book/book.pdf"
ASSET_VERSION = "20260901g"
CATALOG_PAGE_SIZE = 100
MILESTONE_PAGE_SIZE = 20
TEACHING_PREVIEW_COUNT = 6
SOURCE_BRANCH = "main"
PUBLIC_BASE_URL = ""
PUBLIC_SNAPSHOT_BASE_URL = ""
SITE_CHAPTERS: list[dict[str, Any]] = []
SITE_READINGS: dict[str, dict[str, Any]] = {}
SITE_TEXTBOOK_SPINE: dict[str, Any] = {}
SITE_BANDITRLWIKI: dict[str, Any] = {}

STATUS_LABELS = {
    "compiled": "Compiled",
    "prototype": "Prototype",
    "partial": "Partial",
    "planned": "Planned",
    "proposed": "Proposed",
    "blocked": "Blocked",
    "stated": "Stated, proof incomplete",
    "source": "Source indexed",
    "integrated": "Integrated",
}

WIKI_LITERATURE_STATUS_LABELS = {
    "minimax-matched": "Minimax matched",
    "near-minimax": "Near minimax",
    "asymptotic-matched": "Asymptotically matched",
    "upper-only": "Upper bound only",
    "lower-only": "Lower bound only",
    "closest-known": "Closest known",
    "literature-open": "Literature open",
    "source-audit-pending": "Source audit pending",
}

WIKI_LEAN_STATUS_LABELS = {
    "compiled": "Compiled local route",
    "partial": "Partial local route",
    "stated": "Statement only",
    "planned": "Planned",
    "blocked": "Blocked",
    "not-mapped": "Not yet mapped",
}

WIKI_SOURCE_STATUS_LABELS = {
    "exact-source-theorem": "Exact source theorem",
    "faithful-restatement": "Faithful restatement",
    "normalized-comparison": "Normalized comparison statement",
    "closest-known": "Closest-known result",
    "primary-reference-pending": "Primary reference pending",
}

KIND_LABELS = {
    "def": "definition",
    "abbrev": "abbreviation",
    "structure": "structure",
    "class": "typeclass",
    "inductive": "inductive type",
    "theorem": "theorem",
    "lemma": "lemma",
    "axiom": "axiom",
    "opaque": "opaque declaration",
}

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?P<modifiers>(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*)"
    r"(?P<kind>abbrev|def|theorem|lemma|structure|class|inductive|axiom|opaque)"
    r"\s+(?P<name>[A-Za-z0-9_'.]+)"
)
DECL_HEAD_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?P<modifiers>(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*)"
    r"(?P<kind>abbrev|def|theorem|lemma|structure|class|inductive|axiom|opaque)\s*$"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)")
SECTION_RE = re.compile(r"^\s*section(?:\s+[A-Za-z0-9_.]+)?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.]+))?\s*$")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")
PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_text_lf(path: Path, content: str) -> None:
    """Write UTF-8 with stable LF endings on supported Python 3 versions."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(content)


def rel_source(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def module_name(path: Path) -> str:
    return rel_source(path)[:-5].replace("/", ".")


def slugify(value: str) -> str:
    value = re.sub(r"[^A-Za-z0-9]+", "-", value).strip("-").lower()
    return value or "item"


def module_slug(value: str, max_length: int = 96) -> str:
    """Return a stable URL slug that stays below Windows path limits."""
    slug = slugify(value)
    if len(slug) <= max_length:
        return slug
    digest = hashlib.sha1(value.encode("utf-8")).hexdigest()[:12]
    prefix = slug[: max_length - len(digest) - 1].rstrip("-")
    return f"{prefix}-{digest}"


def breakable_identifier(value: str) -> str:
    """Escape an identifier and add visual wrap opportunities without changing copied text."""
    pieces: list[str] = []
    for index, char in enumerate(value):
        previous = value[index - 1] if index else ""
        following = value[index + 1] if index + 1 < len(value) else ""
        camel_boundary = char.isupper() and (
            previous.islower() or (previous.isupper() and following.islower())
        )
        if camel_boundary:
            pieces.append("<wbr>")
        pieces.append(html.escape(char))
        if char in "._/":
            pieces.append("<wbr>")
    return "".join(pieces)


def normalize_math_source(value: str) -> str:
    """Give every teaching formula an explicit MathJax delimiter pair."""
    source = value.strip()
    if not source:
        return r"\(\text{No mathematical statement recorded.}\)"
    inline_open = source.count(r"\(")
    inline_close = source.count(r"\)")
    display_open = source.count(r"\[")
    display_close = source.count(r"\]")
    if inline_open != inline_close or display_open != display_close:
        source = re.sub(r"\\[()\[\]]", "", source).strip()
        return f"\\[{source}\\]"
    if "\\(" in source or "\\[" in source:
        return source
    return f"\\[{source}\\]"


def render_math_statement(label: str, source: str, fallback: str) -> str:
    """Render MathJax progressively and retain readable text if its CDN is unavailable."""
    normalized = normalize_math_source(source)
    return (
        '<div class="math-statement" data-math-statement tabindex="0" '
        f'role="region" aria-label="{html.escape(label)}">'
        f'<strong>{html.escape(label)}.</strong> '
        '<span class="math-fallback-note" aria-hidden="true">Formula renderer unavailable; readable fallback: </span>'
        f'<span class="math-fallback">{html.escape(fallback)}</span>'
        f'<span class="math-tex" aria-hidden="true">{html.escape(normalized)}</span>'
        '<span class="overflow-hint" aria-hidden="true">Swipe to read the full formula <span>→</span></span>'
        "</div>"
    )


def decl_anchor(full_name: str) -> str:
    digest = hashlib.sha1(full_name.encode("utf-8")).hexdigest()[:12]
    return f"decl-{digest}"


def strip_lean_comments(line: str, block_depth: int) -> tuple[str, int]:
    visible: list[str] = []
    index = 0
    in_string = False
    escaped = False
    while index < len(line):
        if block_depth:
            if line.startswith("/-", index):
                block_depth += 1
                index += 2
            elif line.startswith("-/", index):
                block_depth -= 1
                index += 2
            else:
                index += 1
            continue
        char = line[index]
        if in_string:
            visible.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if line.startswith("--", index):
            break
        if line.startswith("/-", index):
            block_depth += 1
            index += 2
            continue
        visible.append(char)
        if char == '"':
            in_string = True
        index += 1
    return "".join(visible), block_depth


def compact_statement(lines: list[str], start: int) -> str:
    parts: list[str] = []
    for raw in lines[start : min(len(lines), start + 90)]:
        stripped = raw.strip()
        if not stripped:
            continue
        compact = re.sub(r"\s+", " ", stripped)
        is_result_let = stripped.startswith("let ")
        if ":=" in stripped and not is_result_let:
            before = compact.split(":=", 1)[0].rstrip()
            if before:
                parts.append(before)
            break
        parts.append(compact)
        if stripped == "where" or stripped.endswith(" where"):
            break
        if sum(len(part) for part in parts) > 8000:
            break
    return " ".join(parts)[:8000]


def docstring_before(lines: list[str], start: int) -> str:
    index = start - 1
    while index >= 0 and (not lines[index].strip() or lines[index].lstrip().startswith("@[")):
        index -= 1
    if index < 0 or "-/" not in lines[index]:
        return ""
    end = index
    while index >= 0 and "/--" not in lines[index]:
        index -= 1
    if index < 0:
        return ""
    raw = "\n".join(lines[index : end + 1])
    if not raw.lstrip().startswith("/--"):
        return ""
    raw = raw[raw.find("/--") + 3 :]
    raw = raw[: raw.rfind("-/")]
    cleaned = []
    for line in raw.splitlines():
        line = re.sub(r"^\s*\*?\s?", "", line.rstrip())
        cleaned.append(line)
    return "\n".join(cleaned).strip()


def module_docstring(text: str) -> str:
    match = re.search(r"/-!(.*?)-/", text, re.DOTALL)
    if not match:
        return ""
    cleaned = []
    for line in match.group(1).splitlines():
        cleaned.append(re.sub(r"^\s*\*?\s?", "", line.rstrip()))
    return "\n".join(cleaned).strip()


def markdown_prose_summary(text: str, limit: int = 620) -> str:
    """Return the first prose paragraph of a small Lean/Markdown doc block."""

    heading_fallback = ""
    for block in re.split(r"\n\s*\n", text.strip()):
        lines = [line.strip() for line in block.splitlines() if line.strip()]
        if not lines:
            continue
        if lines[0].startswith("#"):
            heading_fallback = re.sub(r"^#+\s*", "", lines[0]).strip()
            lines = lines[1:]
            if not lines:
                continue
        prose = " ".join(lines)
        prose = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", prose)
        prose = re.sub(r"`([^`]+)`", r"\1", prose)
        prose = re.sub(r"\s+", " ", prose).strip()
        if prose:
            return prose[:limit].rstrip()
    return heading_fallback[:limit].rstrip()


def scan_module(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    imports = [
        match.group(1)
        for line in lines
        if (match := IMPORT_RE.match(line)) and match.group(1).startswith("BanditRLProof")
    ]
    scopes: list[tuple[str, list[str], str | None]] = []
    visible_lines: list[str] = []
    declarations: list[dict[str, Any]] = []
    block_depth = 0

    for lineno, raw in enumerate(lines, start=1):
        line, block_depth = strip_lean_comments(raw, block_depth)
        visible_lines.append(line)
        if match := NAMESPACE_RE.match(line):
            name = match.group(1)
            scopes.append(("namespace", name.split("."), name))
            continue
        if SECTION_RE.match(line):
            scopes.append(("section", [], None))
            continue
        if match := END_RE.match(line):
            name = match.group(1)
            if not scopes:
                continue
            if name:
                for index in range(len(scopes) - 1, -1, -1):
                    kind, parts, label = scopes[index]
                    if kind == "namespace" and (label == name or parts[-1:] == name.split(".")[-1:]):
                        del scopes[index:]
                        break
                else:
                    scopes.pop()
            else:
                scopes.pop()
            continue
        match = DECL_RE.match(line)
        declaration_name = match.group("name") if match else ""
        declaration_kind = match.group("kind") if match else ""
        declaration_modifiers = match.group("modifiers") if match else ""
        if not match:
            # Large generated theorem statements often put `theorem` on its
            # own line and the (very long) declaration name on the next line.
            # The old scanner silently omitted every declaration written in
            # that style, including the current RL route endpoint.
            head = DECL_HEAD_RE.match(line)
            if not head:
                continue
            for following in lines[lineno:]:
                candidate = re.match(r"^\s*([A-Za-z0-9_'.]+)", following)
                if candidate:
                    declaration_name = candidate.group(1)
                    break
                if following.strip() and not following.lstrip().startswith(("--", "/-", "-/")):
                    break
            if not declaration_name:
                continue
            declaration_kind = head.group("kind")
            declaration_modifiers = head.group("modifiers")
        namespace_parts: list[str] = []
        for kind, parts, _label in scopes:
            if kind == "namespace":
                namespace_parts.extend(parts)
        name = declaration_name
        # A dotted declaration name is still relative to the currently open
        # namespace in Lean.  For example, `theorem Confidence.foo` inside
        # `MDP.EstimatedModelPlan` and inside `MDP.FiniteBatchModel` denotes
        # two different declarations.  Treating every dotted name as absolute
        # collapsed those declarations in the documentation index as the RL
        # tree grew.
        full_name = ".".join(namespace_parts + [name])
        modifiers = declaration_modifiers.strip().split()
        declarations.append(
            {
                "kind": declaration_kind,
                "name": name,
                "full_name": full_name,
                "file": rel_source(path),
                "line": lineno,
                "statement": compact_statement(lines, lineno - 1),
                "docstring": docstring_before(lines, lineno - 1),
                "private": "private" in modifiers,
                "placeholder": False,
                "anchor": decl_anchor(full_name),
            }
        )

    for index, declaration in enumerate(declarations):
        start = declaration["line"] - 1
        stop = declarations[index + 1]["line"] - 1 if index + 1 < len(declarations) else len(lines)
        body = "\n".join(visible_lines[start:stop])
        declaration["placeholder"] = bool(PLACEHOLDER_RE.search(body))

    docstring = module_docstring(text)
    return {
        "name": module_name(path),
        "file": rel_source(path),
        "slug": module_slug(module_name(path)),
        "imports": imports,
        "docstring": docstring,
        "summary": markdown_prose_summary(docstring),
        "declarations": declarations,
        "placeholder_count": sum(1 for decl in declarations if decl["placeholder"]),
    }


def scan_lean_tree() -> list[dict[str, Any]]:
    paths = sorted((ROOT / "BanditRLProof").rglob("*.lean"))
    aggregator = ROOT / "BanditRLProof.lean"
    if aggregator.exists():
        paths.insert(0, aggregator)
    return [scan_module(path) for path in paths]


def assign_chapters(modules: list[dict[str, Any]], chapters: list[dict[str, Any]]) -> None:
    for module in modules:
        assigned = None
        assigned_specificity = (-1, -1)
        for chapter in chapters:
            for pattern in chapter["module_globs"]:
                if not fnmatch.fnmatch(module["file"], pattern):
                    continue
                has_glob = any(token in pattern for token in "*?[")
                specificity = (0 if has_glob else 1, sum(token not in "*?[]" for token in pattern))
                if specificity > assigned_specificity:
                    assigned = chapter
                    assigned_specificity = specificity
        if assigned is None:
            assigned = chapters[0]
        module["chapter"] = assigned["slug"]
        module["chapter_title"] = assigned["short_title"]
        for declaration in module["declarations"]:
            declaration["chapter"] = assigned["slug"]
            declaration["chapter_title"] = assigned["short_title"]
            declaration["module"] = module["name"]
            declaration["module_slug"] = module["slug"]


def source_url(file: str, line: int | None = None) -> str:
    if PUBLIC_BASE_URL:
        return f"{PUBLIC_BASE_URL.rstrip('/')}/source-access/"
    url = f"{GITHUB_REPO}/blob/{SOURCE_BRANCH}/{file}"
    return f"{url}#L{line}" if line else url


def page_root(page_path: str) -> str:
    parent = posixpath.dirname(page_path)
    return posixpath.relpath(".", parent or ".")


def href_from(page_path: str, target: str) -> str:
    fragment = ""
    if "#" in target:
        target, fragment = target.split("#", 1)
        fragment = f"#{fragment}"
    parent = posixpath.dirname(page_path) or "."
    result = posixpath.relpath(target, parent)
    return f"{result}{fragment}"


def public_page_url(page_path: str) -> str:
    """Return the canonical public URL for one generated HTML page."""
    if page_path == "index.html":
        return f"{PUBLIC_SITE_URL}/"
    if page_path.endswith("/index.html"):
        return f"{PUBLIC_SITE_URL}/{page_path[:-10]}"
    return f"{PUBLIC_SITE_URL}/{page_path}"


def status_badge(status: str) -> str:
    label = STATUS_LABELS.get(status, status.replace("-", " ").title())
    return f'<span class="status {html.escape(status)}">{html.escape(label)}</span>'


def highlight_lean(statement: str) -> str:
    token_re = re.compile(
        r'("(?:\\.|[^"\\])*")'
        r"|(\b(?:theorem|lemma|def|abbrev|structure|class|inductive|axiom|opaque|where|by|fun|let|in|if|then|else|match|with|forall|exists|noncomputable|private|protected)\b)"
        r"|(\b\d+(?:\.\d+)?\b)"
    )
    pieces: list[str] = []
    cursor = 0
    for match in token_re.finditer(statement):
        pieces.append(html.escape(statement[cursor : match.start()]))
        value = html.escape(match.group(0))
        if match.group(1):
            pieces.append(f'<span class="str">{value}</span>')
        elif match.group(2):
            pieces.append(f'<span class="kw">{value}</span>')
        else:
            pieces.append(f'<span class="num">{value}</span>')
        cursor = match.end()
    pieces.append(html.escape(statement[cursor:]))
    return "".join(pieces)


def diagram_source(name: str, status_counts: Counter[str] | None = None) -> str:
    source = (DIAGRAM_DIR / name).read_text(encoding="utf-8")
    if status_counts:
        for key in ("compiled", "partial", "planned", "blocked", "stated"):
            source = source.replace(f"{{{{{key}}}}}", str(status_counts.get(key, 0)))
    return source


def render_diagram(
    page_path: str,
    filename: str,
    caption: str,
    status_counts: Counter[str] | None = None,
    extra_class: str = "",
) -> str:
    source = diagram_source(filename, status_counts)
    source_href = href_from(page_path, f"diagrams/{filename}")
    classes = "diagram" + (f" {extra_class}" if extra_class else "")
    return (
        f'<figure class="{html.escape(classes, quote=True)}" tabindex="0" role="region" '
        f'aria-label="{html.escape(caption, quote=True)}">'
        f'<pre class="mermaid" aria-label="{html.escape(caption)}">{html.escape(source)}</pre>'
        f"<figcaption>{html.escape(caption)} · "
        f'<a href="{source_href}">editable Mermaid source</a></figcaption>'
        "</figure>"
    )


def render_list(items: list[str]) -> str:
    if not items:
        return '<p class="empty">None recorded.</p>'
    return "<ul>" + "".join(f"<li>{html.escape(item)}</li>" for item in items) + "</ul>"


def module_href(page_path: str, module: dict[str, Any], anchor: str = "") -> str:
    target = f"modules/{module['slug']}/index.html"
    if anchor:
        target += f"#{anchor}"
    return href_from(page_path, target)


def declaration_href(page_path: str, declaration: dict[str, Any]) -> str:
    target = f"modules/{declaration['module_slug']}/index.html#{declaration['anchor']}"
    return href_from(page_path, target)


def layout(
    page_path: str,
    title: str,
    body: str,
    toc: list[tuple[str, str]],
    current: str,
    verified: bool,
    generated_at: str,
    has_math: bool = True,
    extra_scripts: tuple[str, ...] = (),
    wide: bool = False,
) -> str:
    root = page_root(page_path)
    start_items = [
        ("overview", "Overview", "index.html"),
        ("installation", "Installation", "installation/index.html"),
    ]
    library_items = [
        ("catalog", "Lean declarations", "declarations/index.html"),
        ("map", "Implementation map", "implementation-map/index.html"),
        ("lean-graph", "Lean Graph", "lean-graph/index.html"),
        ("proof-lab", "Proof Graph Laboratory", "proof-graph-laboratory/index.html"),
    ]
    research_items = [
        ("banditrlwiki", "BanditRLwiki", "banditrlwiki/index.html"),
        ("banditrlwiki-frontier", "Frontier leaves", "banditrlwiki/frontier/index.html"),
        ("banditrlwiki-papers", "Paper index", "banditrlwiki/papers/index.html"),
        ("banditrlwiki-progress", "Audit progress", "banditrlwiki/progress/index.html"),
    ]
    formalize_items = [
        ("ide", "Live Formalization", "ide/index.html"),
        ("workflow", "ABRL Harness", "workflow/index.html"),
    ]
    community_items = [
        ("community", "Contribute", "community/index.html"),
        ("contributors", "Contributors", "contributors/index.html"),
        ("roadmap", "Roadmap", "roadmap/index.html"),
        ("attribution", "Attribution", "attribution/index.html"),
    ]

    def nav_links(items: list[tuple[str, str, str]]) -> str:
        return "".join(
            f'<a href="{href_from(page_path, target)}"'
            + (' aria-current="page"' if key == current or target == page_path else "")
            + f">{html.escape(label)}</a>"
            for key, label, target in items
        )

    start_nav = nav_links(start_items)
    library_nav = nav_links(library_items)
    research_nav = nav_links(research_items)
    formalize_nav = nav_links(formalize_items)
    community_nav = nav_links(community_items)
    def book_link(index: int, chapter: dict[str, Any]) -> str:
        target = f"chapters/{chapter['slug']}/index.html"
        active = ' aria-current="page"' if page_path == target else ""
        return (
            f'<a class="book-nav-link" href="{href_from(page_path, target)}"{active}>'
            f'<span>{index:02d}</span>{html.escape(chapter["short_title"])}</a>'
        )

    book_nav = nav_links([("learning", "All chapters", "learning/index.html")]) + "".join(
        book_link(index, chapter)
        for index, chapter in enumerate(SITE_CHAPTERS, start=1)
    )
    def spine_link(chapter: dict[str, Any]) -> str:
        target = f"textbook-spine/{chapter['slug']}/index.html"
        active = ' aria-current="page"' if page_path == target else ""
        return (
            f'<a class="spine-nav-link" href="{href_from(page_path, target)}"{active}>'
            f'<span>{chapter["number"]}</span>{html.escape(chapter["title"])}</a>'
        )

    spine_nav = nav_links(
        [("textbook-spine", "Part IV overview", "textbook-spine/index.html")]
    ) + "".join(spine_link(chapter) for chapter in SITE_TEXTBOOK_SPINE.get("chapters", []))

    def nav_group(key: str, label: str, links: str, active: bool = False) -> str:
        active_class = " active" if active else ""
        active_data = "true" if active else "false"
        open_attribute = " open" if active else ""
        return (
            f'<details class="nav-group{active_class}" data-nav-group="{html.escape(key)}" '
            f'data-nav-group-active="{active_data}"{open_attribute}>'
            f'<summary class="nav-group-title"><span>{html.escape(label)}</span>'
            '<span class="nav-group-chevron" aria-hidden="true">⌄</span></summary>'
            f'<div class="nav-group-links">{links}</div></details>'
        )

    chapter_keys = {chapter["slug"] for chapter in SITE_CHAPTERS}
    sidebar_groups = "".join(
        [
            nav_group("start", "Start", start_nav, current in {"overview", "installation"}),
            nav_group("book-map", "Learn · Book map", book_nav, current == "learning" or current in chapter_keys),
            nav_group("textbook-spine", "Textbook spine · Part IV", spine_nav, current == "textbook-spine"),
            nav_group(
                "research",
                "Research atlas",
                research_nav,
                current in {"banditrlwiki", "banditrlwiki-frontier", "banditrlwiki-papers", "banditrlwiki-progress"},
            ),
            nav_group("library", "Library", library_nav, current in {"catalog", "map", "lean-graph", "proof-lab"}),
            nav_group("formalize", "Formalize", formalize_nav, current in {"ide", "workflow"}),
            nav_group(
                "community",
                "Community",
                community_nav,
                current in {"community", "contributors", "roadmap", "attribution"},
            ),
        ]
    )
    toc_html = (
        '<aside class="side-nav" data-page-toc aria-label="On this page">'
        '<button class="side-nav-toggle" type="button" data-toc-toggle '
        'aria-controls="page-toc-links" aria-expanded="false">'
        '<span class="side-nav-toggle-label">On this page</span>'
        f'<span class="side-nav-current" data-toc-current>{html.escape(toc[0][1])}</span>'
        '<span class="side-nav-chevron" aria-hidden="true">⌄</span></button>'
        '<strong class="side-nav-label">On this page</strong>'
        '<nav class="side-nav-links" id="page-toc-links">'
        + "".join(
            f'<a data-toc-link href="#{html.escape(anchor)}">{html.escape(label)}</a>'
            for anchor, label in toc
        )
        + "</nav></aside>"
        if toc
        else ""
    )
    verification_class = "" if verified else " unverified"
    verification_long = (
        "Lean gate passed before this site build; local proof declarations are shown as compiled."
        if verified
        else "Preview build: run the Lean gate and rebuild with --lean-verified before treating local declarations as compiled."
    )
    verification_short = (
        "Lean-verified build · exact declarations linked."
        if verified
        else "Preview build · not Lean-verified."
    )
    mathjax = ""
    if has_math:
        mathjax = f"""
  <script>
    window.MathJax = {{
      tex: {{ inlineMath: [['\\\\(', '\\\\)']], displayMath: [['\\\\[', '\\\\]']] }},
      options: {{ skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code'] }}
    }};
  </script>
  <script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>"""
    extra_script_tags = "".join(
        f'\n  <script src="{root}/{html.escape(script)}?v={ASSET_VERSION}"></script>'
        for script in extra_scripts
    )
    page_shell_class = "page-shell wide-page" if wide else "page-shell"
    canonical_url = public_page_url(page_path)
    social_title = f"{title} · BanditRLlib"
    social_description = (
        "Verified bandit and reinforcement-learning theory in Lean, with "
        "source-mapped teaching chapters, exact declarations, and explicit proof boundaries."
    )
    return f"""<!doctype html>
<html lang="en" data-theme="blueprint">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="description" content="BanditRLlib: verified bandit and reinforcement-learning theory in Lean, produced by the target-faithful ABRL autoformalization harness.">
  <meta name="citation_title" content="{html.escape(PAPER_TITLE)}">
  <meta property="og:type" content="website">
  <meta property="og:site_name" content="BanditRLlib">
  <meta property="og:title" content="{html.escape(social_title, quote=True)}">
  <meta property="og:description" content="{html.escape(social_description, quote=True)}">
  <meta property="og:url" content="{html.escape(canonical_url, quote=True)}">
  <meta name="twitter:card" content="summary">
  <meta name="twitter:title" content="{html.escape(social_title, quote=True)}">
  <meta name="twitter:description" content="{html.escape(social_description, quote=True)}">
  <link rel="canonical" href="{html.escape(canonical_url, quote=True)}">
  <meta name="theme-color" content="#176b70">
  <title>{html.escape(social_title)}</title>
  <link rel="icon" href="{root}/static/favicon.svg" type="image/svg+xml">
  <link rel="stylesheet" href="{root}/static/site.css?v={ASSET_VERSION}">
  {mathjax}
</head>
<body data-site-root="{root}">
  <a class="skip-link" href="#main-content">Skip to content</a>
  <header class="mobile-bar">
    <button class="sidebar-toggle" type="button" data-sidebar-toggle aria-controls="site-sidebar" aria-expanded="false"><span aria-hidden="true">☰</span><span class="visually-hidden">Open site navigation</span></button>
    <a class="mobile-brand" href="{href_from(page_path, 'index.html')}">BanditRLlib</a>
  </header>
  <aside class="site-sidebar" id="site-sidebar" data-site-sidebar aria-label="Site navigation">
    <div class="sidebar-heading">
      <button class="sidebar-close" type="button" data-sidebar-toggle aria-controls="site-sidebar" aria-expanded="false"><span aria-hidden="true">×</span><span class="visually-hidden">Close site navigation</span></button>
      <a class="brand" href="{href_from(page_path, 'index.html')}">
        <span class="brand-mark" aria-hidden="true">B</span>
        <span><strong>BanditRLlib</strong><small>Verified Lean library</small></span>
      </a>
    </div>
    <div class="search-shell sidebar-search">
      <label class="nav-group-title" for="global-search"><span>Search the Lean library</span><kbd aria-hidden="true">/</kbd></label>
      <input id="global-search" class="global-search" data-global-search type="search" placeholder="Declaration or module…" autocomplete="off" role="combobox" aria-autocomplete="list" aria-controls="global-search-results" aria-expanded="false" aria-keyshortcuts="/">
      <ul id="global-search-results" class="search-results" data-global-results role="listbox" aria-label="Lean declaration search results" aria-live="polite" hidden></ul>
    </div>
    <nav class="sidebar-nav" aria-label="Primary">
      {sidebar_groups}
    </nav>
    <div class="sidebar-footer">
      <a href="{GITHUB_REPO}">GitHub repository <span aria-hidden="true">↗</span></a>
      <div class="theme-switcher" aria-label="Site style">
        <button type="button" data-theme-choice="blueprint" aria-pressed="true">Blueprint</button>
        <button type="button" data-theme-choice="modern" aria-pressed="false">Modern</button>
        <button type="button" data-theme-choice="bold" aria-pressed="false">Bold</button>
      </div>
    </div>
  </aside>
  <button class="sidebar-scrim" type="button" data-sidebar-scrim aria-label="Close site navigation" aria-hidden="true" tabindex="-1"></button>
  <div class="site-content">
    <div class="verification-strip{verification_class}"><span class="verification-long">{html.escape(verification_long)}</span><span class="verification-short">{html.escape(verification_short)}</span></div>
    <div class="{page_shell_class}">
      <main class="page-main" id="main-content">{body}</main>
      {toc_html}
    </div>
    <footer class="site-footer">
      <div class="footer-inner">
        <p><strong>BanditRLlib</strong> is the public Lean library and community interface produced by <strong>Auto-Bandit-RL-Proof-In-Sleep (ABRL)</strong>. Generated from current sources at {html.escape(generated_at)}; exact Lean statements and verification status take precedence.</p>
        <p>Organization inspired by <a href="https://github.com/shosonoda/lean-ridgelet">Sho Sonoda's Lean-Ridgelet</a> and <a href="https://statsmllib.github.io/">StatsMLlib</a>; no participation or endorsement is implied. <a href="{href_from(page_path, 'attribution/index.html')}">Attribution details</a>.</p>
      </div>
    </footer>
  </div>
  <script src="{root}/static/site.js?v={ASSET_VERSION}"></script>{extra_script_tags}
</body>
</html>
"""


def write_page(output: Path, page_path: str, content: str) -> None:
    target = output / Path(page_path)
    target.parent.mkdir(parents=True, exist_ok=True)
    clean = "\n".join(line.rstrip() for line in content.splitlines()) + "\n"
    write_text_lf(target, clean)


def render_book_map(
    page_path: str,
    chapters: list[dict[str, Any]],
    *,
    detailed: bool = False,
) -> str:
    cards = []
    for index, chapter in enumerate(chapters, start=1):
        reading = SITE_READINGS.get(chapter["slug"], {})
        primary = reading.get("primary", {})
        source_line = (
            f'<span class="book-source">{html.escape(primary.get("sections", ""))} · '
            f'{html.escape(primary.get("pages", ""))}</span>'
            if primary
            else ""
        )
        milestone_counts = chapter.get("milestone_counts", {})
        milestone_line = " · ".join(
            f"{count} {STATUS_LABELS.get(status, status).lower()}"
            for status, count in milestone_counts.items()
            if count
        )
        scope_line = (
            '<span class="book-scope">Extension and milestone ledger'
            + (f" · {html.escape(milestone_line)}" if milestone_line else " · no registered milestones")
            + "</span>"
        )
        audience = (
            f'<p class="book-audience"><strong>Reader.</strong> {html.escape(chapter["audience"])}</p>'
            if detailed
            else ""
        )
        cards.append(
            f"""
<a class="book-chapter-card" href="{href_from(page_path, f"chapters/{chapter['slug']}/index.html")}">
  <span class="book-chapter-number" aria-hidden="true">{index:02d}</span>
  <div class="book-chapter-copy">
    <span class="book-chapter-meta"><span>Canonical chapter core</span>{status_badge(chapter['status'])}</span>
    <strong>{html.escape(chapter['title'])}</strong>
    {scope_line}
    {source_line}
    <span class="book-summary">{html.escape(chapter['summary'])}</span>
    {audience}
  </div>
  <span class="book-chapter-arrow" aria-hidden="true">→</span>
</a>"""
        )
    return '<div class="book-map-grid">' + "".join(cards) + "</div>"


def render_learning_routes(page_path: str) -> str:
    routes = [
        ("Stochastic finite arms", "Start with bookkeeping, add concentration, then compare ETC and optimism.", ["foundations", "probability", "etc", "ucb"]),
        ("Linear and contextual", "Build the probability interface before moving from optimism to confidence ellipsoids.", ["probability", "ucb", "oful"]),
        ("Bayesian", "Use the common probability layer, then follow posterior sampling and its information route.", ["probability", "thompson"]),
        ("Adversarial and OCO", "Move from importance weighting in EXP3 to regularized FTRL and Tsallis geometry.", ["probability", "exp3", "tsallis"]),
        ("Finite-horizon RL", "Reuse probability and optimism interfaces before entering Bellman recursion and UCBVI.", ["probability", "ucb", "finite-horizon-rl"]),
    ]
    chapter_by_slug = {chapter["slug"]: chapter for chapter in SITE_CHAPTERS}
    cards = []
    for title, description, slugs in routes:
        steps = "".join(
            f'<li><a href="{href_from(page_path, f"chapters/{slug}/index.html")}">'
            f'<span>{index:02d}</span>{html.escape(chapter_by_slug[slug]["title"])}</a></li>'
            for index, slug in enumerate(slugs, start=1)
        )
        cards.append(
            f'<article class="learning-route-card" data-learning-route><h3>{html.escape(title)}</h3>'
            f'<p>{html.escape(description)}</p><ol>{steps}</ol></article>'
        )
    return '<div class="learning-route-grid">' + "".join(cards) + "</div>"


def effective_evidence_status(status: str, verified: bool) -> str:
    """Never render a local compiled claim in an unverified preview build."""
    return status if status != "compiled" or verified else "source"


def render_textbook_spine_map(
    page_path: str,
    spine: dict[str, Any],
    verified: bool,
) -> str:
    cards = []
    for chapter in spine["chapters"]:
        route = f"textbook-spine/{chapter['slug']}/index.html"
        cards.append(
            f"""
<a class="spine-chapter-card" href="{href_from(page_path, route)}">
  <span class="spine-chapter-number">Chapter {chapter['number']}</span>
  <span class="spine-chapter-status">{status_badge(effective_evidence_status(chapter['status'], verified))}</span>
  <strong>{html.escape(chapter['title'])}</strong>
  <span>{html.escape(chapter['print_pages'])} print · {html.escape(chapter['pdf_pages'])} PDF</span>
  <p>{html.escape(chapter['status_note'])}</p>
  <span class="spine-chapter-arrow" aria-hidden="true">→</span>
</a>"""
        )
    return '<div class="textbook-spine-grid">' + "".join(cards) + "</div>"


def validate_textbook_spine(
    spine: dict[str, Any],
    decl_by_name: dict[str, dict[str, Any]],
) -> None:
    source = spine.get("canonical_source", {})
    if source.get("official_url") != PRIMARY_TEXTBOOK_URL:
        raise ValueError("textbook spine must use the official author-hosted PDF")
    if source.get("doi") != "10.1017/9781108571401":
        raise ValueError("textbook spine DOI is not the canonical CUP identifier")
    chapters = spine.get("chapters", [])
    if [chapter.get("number") for chapter in chapters] != list(range(13, 18)):
        raise ValueError("textbook spine chapters must be ordered exactly 13 through 17")
    if len({chapter.get("slug") for chapter in chapters}) != len(chapters):
        raise ValueError("textbook spine chapter slugs must be unique")
    for chapter in chapters:
        if chapter.get("status") not in STATUS_LABELS:
            raise ValueError(f"unknown textbook spine status: {chapter.get('status')}")
        if chapter.get("core_status") and chapter.get("core_status") not in STATUS_LABELS:
            raise ValueError(f"unknown textbook spine core status: {chapter.get('core_status')}")
        for section in chapter.get("section_coverage", []):
            if section.get("status") not in STATUS_LABELS:
                raise ValueError(
                    f"unknown textbook section status: {section.get('status')}"
                )
        for item in chapter.get("lean_correspondence", []):
            if item.get("status") == "compiled" and item.get("name") not in decl_by_name:
                raise ValueError(
                    f"compiled textbook spine declaration is not indexed: {item.get('name')}"
                )
        for name in chapter.get("primary_declarations", []):
            if name not in decl_by_name:
                raise ValueError(f"primary textbook declaration is not indexed: {name}")
        if chapter["number"] > 13 and chapter.get("status") == "compiled":
            raise ValueError("future Part IV chapters cannot be promoted before their gates")


def build_textbook_spine(
    output: Path,
    spine: dict[str, Any],
    decl_by_name: dict[str, dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    source = spine["canonical_source"]
    landing_path = "textbook-spine/index.html"
    landing_body = f"""
<section class="hero" id="spine">
  <p class="eyebrow">Canonical textbook sequence</p>
  <h1 class="page-title">{html.escape(spine['title'])}</h1>
  <p class="lede">{html.escape(spine['summary'])}</p>
  <div class="callout warning"><strong>Scope boundary.</strong> This is a separate chapter-by-chapter lower-bound spine. The existing ten-chapter Book Map remains a curated curriculum and is not relabeled as a completed formalization of the entire book.</div>
</section>

<section id="source">
  <h2>Canonical source</h2>
  <article class="source-card spine-source-card">
    <span class="panel-kicker">{html.escape(source['part'])}</span>
    <h3>{html.escape(source['title'])}</h3>
    <p>{html.escape(source['authors'])}</p>
    <dl>
      <div><dt>Edition</dt><dd>{html.escape(source['edition'])}</dd></div>
      <div><dt>Publisher</dt><dd>{html.escape(source['publisher'])}, {source['year']}</dd></div>
      <div><dt>DOI</dt><dd><a href="{html.escape(source['doi_url'], quote=True)}">{html.escape(source['doi'])}</a></dd></div>
    </dl>
    <a class="button compact" href="{html.escape(source['official_url'], quote=True)}">Open the formal PDF <span aria-hidden="true">↗</span></a>
  </article>
</section>

<section id="chapters">
  <h2>Chapters 13–17</h2>
  <p class="section-intro">Work advances in source order. A chapter can expose compiled leaves while its broader source theorem remains partial or planned.</p>
  {render_textbook_spine_map(landing_path, spine, verified)}
</section>

<section id="dependencies">
  <h2>Part IV dependency spine</h2>
  <p>The graph is a route map, not proof evidence. Each chapter page names the declarations and missing bridges that determine its status.</p>
  {render_diagram(landing_path, 'part-iv-lower-bounds.mmd', 'Part IV finite-arm lower-bound dependency spine')}
</section>
"""
    write_page(
        output,
        landing_path,
        layout(
            landing_path,
            spine["title"],
            landing_body,
            [("spine", "Textbook spine"), ("source", "Canonical source"),
             ("chapters", "Chapters 13–17"), ("dependencies", "Dependencies")],
            "textbook-spine",
            verified,
            generated_at,
        ),
    )

    spine_chapters = spine["chapters"]
    for chapter_index, chapter in enumerate(spine_chapters):
        page_path = f"textbook-spine/{chapter['slug']}/index.html"
        chapter_source_html = ""
        if chapter.get("chapter_doi_url") and chapter.get("chapter_doi"):
            chapter_source_html = (
                '<p><strong>Chapter DOI.</strong> '
                f'<a href="{html.escape(chapter["chapter_doi_url"], quote=True)}">'
                f'{html.escape(chapter["chapter_doi"])}</a>'
                + (
                    ' · <a href="'
                    + html.escape(chapter["chapter_url"], quote=True)
                    + '">CUP chapter page</a>'
                    if chapter.get("chapter_url")
                    else ""
                )
                + "</p>"
            )
        sections = render_list(chapter["sections"])
        goals = render_list(chapter["learning_goals"])
        status_summary_html = ""
        chapter_meta_status = status_badge(effective_evidence_status(chapter['status'], verified))
        if chapter.get("core_status"):
            status_summary_html = f"""
  <div class="spine-status-summary" aria-label="Chapter status at two scopes">
    <article><span>{html.escape(chapter.get('core_status_label', 'Core theorem spine'))}</span>{status_badge(effective_evidence_status(chapter['core_status'], verified))}</article>
    <article><span>{html.escape(chapter.get('chapter_status_label', 'Whole chapter coverage'))}</span>{status_badge(effective_evidence_status(chapter['status'], verified))}</article>
  </div>"""
            chapter_meta_status = ""
        section_coverage_html = ""
        if chapter.get("section_coverage"):
            coverage_rows = "".join(
                f'<tr><th scope="row">{html.escape(item["section"])}</th>'
                f'<td>{status_badge(effective_evidence_status(item["status"], verified))}</td>'
                f'<td>{html.escape(item["scope"])}</td></tr>'
                for item in chapter["section_coverage"]
            )
            section_coverage_html = (
                '<h3>Section coverage</h3><div class="table-wrap" tabindex="0" '
                'role="region" aria-label="Textbook section coverage"><table>'
                '<thead><tr><th>Section</th><th>Status</th><th>Formalization boundary</th></tr></thead>'
                f'<tbody>{coverage_rows}</tbody></table></div>'
            )
        definitions = "".join(
            f"""
<article class="spine-definition-card">
  <div class="spine-card-heading"><h3>{html.escape(item['name'])}</h3>{status_badge(effective_evidence_status(item['status'], verified))}</div>
  {render_math_statement(item['name'], item['math'], item['fallback'])}
</article>"""
            for item in chapter["definitions"]
        )
        steps = "".join(
            f'<li><span class="algorithm-step-number" aria-hidden="true">{index:02d}</span>'
            f'<div><strong>{html.escape(step["title"])}</strong><p>{html.escape(step["detail"])}</p></div></li>'
            for index, step in enumerate(chapter["flow"]["steps"], start=1)
        )
        source_theorem = chapter.get("source_theorem")
        if source_theorem:
            quantifier_html = ""
            if chapter.get("quantifier_contract"):
                quantifier_html = (
                    '<div class="spine-quantifier-contract"><strong>Quantifier contract.</strong>'
                    + render_list(chapter["quantifier_contract"])
                    + '</div>'
                )
            primary_declarations_html = ""
            if chapter.get("primary_declarations"):
                primary_declarations_html = (
                    '<div class="spine-primary-declarations"><strong>Direct Lean endpoints.</strong><ul>'
                    + "".join(
                        '<li><a href="'
                        + declaration_href(page_path, decl_by_name[name])
                        + '"><code>'
                        + html.escape(name)
                        + '</code></a></li>'
                        for name in chapter["primary_declarations"]
                    )
                    + '</ul></div>'
                )
            theorem_html = f"""
<article class="source-theorem-card spine-theorem-card">
  <div class="source-theorem-heading"><div><span class="panel-kicker">Source theorem · faithful restatement</span><h3>{html.escape(source_theorem['label'])}</h3></div>{status_badge(effective_evidence_status(source_theorem['status'], verified))}</div>
  <p>{html.escape(source_theorem['plain'])}</p>
  {render_math_statement(source_theorem['label'], source_theorem['math'], source_theorem['fallback'])}
  {quantifier_html}
  {primary_declarations_html}
  <div class="callout warning"><strong>Lean boundary.</strong> {html.escape(source_theorem['boundary'])}</div>
</article>"""
        else:
            theorem_html = (
                '<div class="callout warning source-boundary"><strong>Source target pending.</strong> '
                + html.escape(chapter["source_boundary"])
                + "</div>"
            )
        correspondence_rows = []
        for item in chapter.get("lean_correspondence", []):
            declaration = decl_by_name.get(item["name"])
            name_html = f"<code>{html.escape(item['name'])}</code>"
            statement_html = "No local declaration is indexed."
            if declaration:
                name_html = (
                    f'<a href="{declaration_href(page_path, declaration)}">'
                    f'<code>{html.escape(item["name"])}</code></a>'
                )
                statement_html = (
                    '<details><summary>Exact compact Lean statement</summary>'
                    f'<pre class="lean-code"><code>{html.escape(declaration["statement"])}</code></pre></details>'
                )
            correspondence_rows.append(
                f"""
<tr><td>{name_html}</td><td>{status_badge(effective_evidence_status(item['status'], verified))}</td><td>{html.escape(item['role'])}{statement_html}</td></tr>"""
            )
        correspondence_html = (
            '<div class="table-wrap lean-correspondence-table" tabindex="0" role="region" aria-label="Lean correspondence">'
            '<table><thead><tr><th>Lean declaration</th><th>Status</th><th>Role and exact type</th></tr></thead>'
            f'<tbody>{"".join(correspondence_rows)}</tbody></table></div>'
            if correspondence_rows
            else '<p class="empty">No local Lean declaration is claimed for this planned chapter.</p>'
        )
        dependency_html = "".join(
            f'<article class="spine-dependency-node"><code>{html.escape(node["id"])}</code>'
            f'<strong>{html.escape(node["label"])}</strong>'
            f'{status_badge(effective_evidence_status(node["status"], verified))}</article>'
            for node in chapter["dependency_nodes"]
        )
        previous_chapter = spine_chapters[chapter_index - 1] if chapter_index else None
        next_chapter = spine_chapters[chapter_index + 1] if chapter_index + 1 < len(spine_chapters) else None
        chapter_pager = render_sequence_pager(
            page_path,
            sequence_label="Bandit Algorithms · Part IV",
            index=chapter_index,
            total=len(spine_chapters),
            landing_path="textbook-spine/index.html",
            previous=(
                f"textbook-spine/{previous_chapter['slug']}/index.html",
                f"Chapter {previous_chapter['number']}: {previous_chapter['title']}",
            ) if previous_chapter else None,
            next_item=(
                f"textbook-spine/{next_chapter['slug']}/index.html",
                f"Chapter {next_chapter['number']}: {next_chapter['title']}",
            ) if next_chapter else None,
        )
        body = f"""
<section class="hero spine-chapter-hero" id="chapter">
  <p class="eyebrow">{html.escape(source['part'])}</p>
  <h1 class="page-title">Chapter {chapter['number']}: {html.escape(chapter['title'])}</h1>
  <p class="lede">{html.escape(chapter['status_note'])}</p>
  {status_summary_html}
  <div class="spine-chapter-meta">{chapter_meta_status}<span>Printed pp. {html.escape(chapter['print_pages'])}</span><span>PDF pp. {html.escape(chapter['pdf_pages'])}</span></div>
</section>

<section id="source">
  <h2>Source map</h2>
  <p><cite>{html.escape(source['title'])}</cite>, {html.escape(source['authors'])}, {html.escape(source['publisher'])} ({source['year']}), DOI <a href="{html.escape(source['doi_url'], quote=True)}">{html.escape(source['doi'])}</a>.</p>
  {chapter_source_html}
  {sections}
  {section_coverage_html}
  <p><a class="button compact" href="{html.escape(source['official_url'], quote=True)}">Open the formal PDF <span aria-hidden="true">↗</span></a></p>
</section>

<section id="goals"><h2>Learning goals</h2>{goals}</section>

<section id="definitions"><h2>Necessary definitions and statements</h2><div class="spine-definition-grid">{definitions}</div></section>

<section id="flow" class="algorithm-panel">
  <div><span class="panel-kicker">{html.escape(chapter['flow']['kind'])}</span><h2>{html.escape(chapter['flow']['title'])}</h2></div>
  <ol class="algorithm-flow">{steps}</ol>
</section>

<section id="source-theorem"><h2>Key source theorem and boundary</h2>{theorem_html}</section>

<section id="lean"><h2>Lean correspondence</h2><p>Only declarations that exist in the current index and pass the verified build may render as compiled.</p>{correspondence_html}</section>

<section id="dependencies"><h2>Dependency graph</h2><div class="spine-dependency-grid">{dependency_html}</div></section>

<section id="reading"><h2>Reading path</h2>{render_list(chapter['reading_path'])}</section>

<section id="gaps"><h2>Strict status and remaining gaps</h2>{render_list(chapter['gaps'])}</section>

{chapter_pager}
"""
        toc = [
            ("chapter", f"Chapter {chapter['number']}"), ("source", "Source map"),
            ("goals", "Learning goals"), ("definitions", "Definitions"),
            ("flow", "Proof flow"), ("source-theorem", "Source theorem"),
            ("lean", "Lean correspondence"), ("dependencies", "Dependencies"),
            ("reading", "Reading path"), ("gaps", "Status and gaps"),
            ("continue-reading", "Continue reading"),
        ]
        write_page(
            output,
            page_path,
            layout(
                page_path,
                f"Chapter {chapter['number']}: {chapter['title']}",
                body,
                toc,
                "textbook-spine",
                verified,
                generated_at,
            ),
        )


def render_reading_guide(page_path: str, chapter: dict[str, Any], reading: dict[str, Any]) -> str:
    primary = reading["primary"]
    companion = reading.get("companion")
    companions = ([companion] if companion else []) + reading.get("companions", [])

    def source_card(source: dict[str, str], label: str) -> str:
        return f"""
<article class="source-card">
  <span class="panel-kicker">{html.escape(label)}</span>
  <h3>{html.escape(source['title'])}</h3>
  <p>{html.escape(source['authors'])}</p>
  <dl><div><dt>Location</dt><dd>{html.escape(source['sections'])}</dd></div><div><dt>Pages</dt><dd>{html.escape(source['pages'])}</dd></div></dl>
  <a class="button compact" href="{html.escape(source['url'], quote=True)}">Open the source <span aria-hidden="true">↗</span></a>
</article>"""

    sources = source_card(primary, f"Primary spine · {primary['edition']}")
    for companion_source in companions:
        sources += source_card(companion_source, "Algorithm-specific companion")

    notation_items = "".join(
        '<div><dt><code>'
        + html.escape(item["term"])
        + '</code></dt><dd>'
        + html.escape(item["meaning"])
        + '</dd></div>'
        for item in reading["notation"]
    )
    notation_html = f"""
  <aside class="notation-primer" id="notation" aria-labelledby="notation-title">
    <div><span class="panel-kicker">Reader checkpoint</span><h3 id="notation-title">Notation you will meet</h3></div>
    <dl>{notation_items}</dl>
  </aside>"""

    algorithm = reading["algorithm"]
    steps = "".join(
        f'<li><span class="algorithm-step-number" aria-hidden="true">{index:02d}</span>'
        f'<div><strong>{html.escape(step["title"])}</strong><p>{html.escape(step["detail"])}</p></div></li>'
        for index, step in enumerate(algorithm["steps"], start=1)
    )
    theorems = ([reading["source_theorem"]] if reading.get("source_theorem") else []) + reading.get("source_theorems", [])
    if theorems:
        theorem_cards = []
        for theorem in theorems:
            contract = theorem.get("contract", {})
            contract_html = ""
            if contract:
                contract_order = (
                    ("Model", "model"),
                    ("Assumptions", "assumptions"),
                    ("Algorithm parameters", "parameters"),
                    ("Regret notion", "regret"),
                    ("Guarantee", "guarantee"),
                )
                contract_items = "".join(
                    f'<div><dt>{html.escape(label)}</dt><dd>{html.escape(str(contract[key]))}</dd></div>'
                    for label, key in contract_order
                    if contract.get(key)
                )
                contract_html = (
                    '<dl class="source-theorem-contract" aria-label="Source theorem contract">'
                    + contract_items
                    + '</dl>'
                )
            theorem_cards.append(f"""
<article class="source-theorem-card">
  <div class="source-theorem-heading"><div><span class="panel-kicker">Source theorem · faithful restatement</span><h3>{html.escape(theorem['label'])}</h3></div><a href="{html.escape(theorem['url'], quote=True)}">Original source ↗</a></div>
  <p>{html.escape(theorem['plain'])}</p>
  {contract_html}
  {render_math_statement('Source mathematical statement', theorem['math'], theorem['fallback'])}
  <p class="source-note"><strong>BanditRLlib relationship.</strong> {html.escape(theorem['relationship'])}</p>
  <p class="copyright-note">The mathematical content is restated in this site's notation; wording is ours. See {html.escape(theorem['pages'])} in the linked source for the original statement and full assumptions.</p>
</article>""")
        theorem_html = "".join(theorem_cards)
    else:
        theorem_html = f"""
<div class="callout warning source-boundary"><strong>No single source theorem.</strong> {html.escape(reading['source_boundary'])}</div>"""

    return f"""
<section id="source-guide" class="source-guide">
  <p class="eyebrow">Textbook crosswalk</p>
  <h2>Read the mathematics before the Lean interface</h2>
  <p class="section-intro">The Book Map is a curated formalization curriculum anchored in <em>Bandit Algorithms</em>, not a chapter-for-chapter reproduction of one book. Page numbers below use its free online edition; companion papers cover algorithm-specific results.</p>
  <div class="source-grid source-grid-{len(companions) + 1}">{sources}</div>
  {notation_html}
  <div class="algorithm-panel" id="algorithm">
    <div><span class="panel-kicker">{html.escape(algorithm['kind'])} · ordered flow</span><h3>{html.escape(algorithm['title'])}</h3><p class="algorithm-intro">Read top to bottom: each step supplies the state or proof fact used by the next one.</p></div>
    <ol class="algorithm-flow">{steps}</ol>
  </div>
  {theorem_html}
</section>"""


def render_chapter_compass(page_path: str, chapter: dict[str, Any], reading: dict[str, Any]) -> str:
    primary = reading["primary"]
    algorithm = reading["algorithm"]
    theorem_count = int(bool(reading.get("source_theorem"))) + len(reading.get("source_theorems", []))
    theorem_note = (
        f"{theorem_count} source theorem restatement{'s' if theorem_count != 1 else ''}, with assumptions and original links."
        if theorem_count
        else "The source boundary is explicit because no single theorem represents this chapter."
    )
    return f"""
<nav class="chapter-compass" data-chapter-compass aria-label="Chapter reading order">
  <a href="#orientation"><span class="chapter-compass-step">01 · Orient</span><strong>What you need</strong><small>{len(chapter['learning_goals'])} learning goals and the intended reader.</small></a>
  <a href="#source-guide"><span class="chapter-compass-step">02 · Learn</span><strong>{html.escape(algorithm['title'])}</strong><small>{html.escape(primary['sections'])} · {html.escape(primary['pages'])}. {html.escape(theorem_note)}</small></a>
  <a href="#teaching-notes"><span class="chapter-compass-step">03 · Verify</span><strong>Mathematics ↔ Lean</strong><small>Read intuition and proof structure, then open the exact compiled declaration.</small></a>
</nav>"""


def render_sequence_pager(
    page_path: str,
    *,
    sequence_label: str,
    index: int,
    total: int,
    landing_path: str,
    previous: tuple[str, str] | None,
    next_item: tuple[str, str] | None,
) -> str:
    """Render a compact, keyboard-friendly previous/index/next reading route."""

    def adjacent_link(item: tuple[str, str] | None, direction: str) -> str:
        if item is None:
            return '<span class="chapter-pager-spacer" aria-hidden="true"></span>'
        target, title = item
        if direction == "previous":
            direction_label = '<span aria-hidden="true">←</span> Previous'
        else:
            direction_label = 'Next <span aria-hidden="true">→</span>'
        return (
            f'<a class="chapter-pager-link {direction}" href="{href_from(page_path, target)}">'
            f'<span class="chapter-pager-direction">{direction_label}</span>'
            f'<strong>{html.escape(title)}</strong></a>'
        )

    return f"""
<nav class="chapter-pager" id="continue-reading" aria-label="{html.escape(sequence_label)} reading sequence">
  <div class="chapter-pager-heading"><span class="eyebrow">Continue reading</span><strong>{html.escape(sequence_label)}</strong></div>
  <div class="chapter-pager-links">
    {adjacent_link(previous, 'previous')}
    <a class="chapter-pager-index" href="{href_from(page_path, landing_path)}"><span>All chapters</span><strong>{index + 1} of {total}</strong></a>
    {adjacent_link(next_item, 'next')}
  </div>
</nav>"""


def render_contributor_cards(
    page_path: str,
    contributors: list[dict[str, Any]],
    *,
    include_invitation: bool = True,
) -> str:
    cards = []
    for contributor in contributors:
        initials = "".join(part[0] for part in contributor["name"].split() if part)[:2].upper()
        name = html.escape(contributor["name"])
        profile = contributor.get("profile", "")
        name_html = f'<a href="{html.escape(profile)}">{name}</a>' if profile else name
        handle = contributor.get("handle", "")
        handle_html = f"@{html.escape(handle)} · " if handle else ""
        cards.append(
            f"""
<article class="contributor-card">
  <div class="contributor-avatar" aria-hidden="true">{html.escape(initials)}</div>
  <div>
    <h3>{name_html}</h3>
    <p class="contributor-handle">{handle_html}{html.escape(contributor['role'])}</p>
    <p>{html.escape(contributor['contribution'])}</p>
  </div>
</article>"""
        )
    if include_invitation:
        cards.append(
        f"""
<a class="contributor-card contributor-invite" href="{href_from(page_path, 'community/index.html')}">
  <div class="contributor-avatar" aria-hidden="true">+</div>
  <div><h3>Your name here</h3><p>Propose a sourced theorem, improve a teaching note, or submit a Lean-checked lemma packet.</p><strong>How to contribute →</strong></div>
</a>"""
        )
    return '<div class="contributor-grid">' + "".join(cards) + "</div>"


def render_highlight(
    page_path: str,
    highlight: dict[str, Any],
    declaration: dict[str, Any],
    verified: bool,
) -> str:
    status = "compiled" if verified and not declaration["placeholder"] else (
        "stated" if declaration["placeholder"] or declaration["kind"] == "axiom" else "source"
    )
    dependency_links = []
    for dependency in highlight.get("dependencies", []):
        dependency_links.append(f"<code>{html.escape(dependency)}</code>")
    dependencies = ", ".join(dependency_links) if dependency_links else "No direct teaching dependency recorded."
    match_kind = highlight.get("source_match", "")
    match_labels = {
        "closest-source": "Closest local match to the source theorem",
        "extension": "Compiled extension",
        "consumer": "Downstream consumer",
    }
    match_badge = (
        f'<span class="source-match {html.escape(match_kind)}">{html.escape(match_labels[match_kind])}</span>'
        if match_kind in match_labels
        else ""
    )
    return f"""
<article class="theorem-panel{' source-match-panel' if match_badge else ''}" id="{declaration['anchor']}-teaching">
  <div class="theorem-header">
    <div class="declaration-heading"><span class="panel-kicker">Lean declaration</span>{match_badge}<h3>{html.escape(declaration['full_name'])}</h3></div>
    {status_badge(status)}
  </div>
  <div class="theorem-body">
    <p><strong>Plain-English statement.</strong> {html.escape(highlight['plain'])}</p>
    {render_math_statement('Mathematical reading', highlight['math'], highlight['plain'])}
    <dl class="teaching-grid">
      <div><dt>Intuition</dt><dd>{html.escape(highlight['intuition'])}</dd></div>
      <div><dt>Why it is needed</dt><dd>{html.escape(highlight['why'])}</dd></div>
      <div><dt>Place in the proof</dt><dd>{html.escape(highlight['position'])}</dd></div>
      <div><dt>Proof idea</dt><dd>{html.escape(highlight['proof_idea'])}</dd></div>
      <div><dt>Lean reading notes</dt><dd>{html.escape(highlight['lean_notes'])}</dd></div>
      <div><dt>Teaching dependencies</dt><dd>{dependencies}</dd></div>
    </dl>
    <details class="exact-lean">
      <summary>Exact Lean statement</summary>
      <pre class="lean-code" tabindex="0" role="region" aria-label="Exact Lean statement"><code>{highlight_lean(declaration['statement'])}</code></pre>
    </details>
    <div class="source-links">
      <a href="{declaration_href(page_path, declaration)}">Open in the declaration catalog</a>
      <a href="{source_url(declaration['file'], declaration['line'])}">Open source at line {declaration['line']}</a>
    </div>
  </div>
</article>
"""


def render_primary_textbook_banner() -> str:
    return f"""
<aside class="primary-textbook-banner" id="primary-textbook" aria-labelledby="primary-textbook-title">
  <div class="primary-textbook-identity">
    <span class="primary-textbook-label">Current primary textbook</span>
    <strong class="primary-textbook-title" id="primary-textbook-title"><cite>{html.escape(PRIMARY_TEXTBOOK_TITLE)}</cite></strong>
    <span class="primary-textbook-authors">{html.escape(PRIMARY_TEXTBOOK_AUTHORS)} · free online edition</span>
  </div>
  <p>The ten-chapter Book Map uses this book as its main mathematical spine. Original papers supplement OFUL, Tsallis-INF, UCBVI, and other source-specific results.</p>
  <a class="button compact" href="{PRIMARY_TEXTBOOK_URL}">Open the free textbook <span aria-hidden="true">↗</span></a>
</aside>
"""


def load_harness_comparison() -> dict[str, Any]:
    """Load the deterministic harness-comparison ledger used by the CLI."""
    if not HARNESS_COMPARISON_PATH.exists():
        raise SystemExit(
            "missing runs/harness-comparison/latest.json; run "
            "`python3 tools/bandit.py harness-compare` before building the site"
        )
    payload = load_json(HARNESS_COMPARISON_PATH)
    required = {
        "schema_version",
        "matched_experiments",
        "minimum_matched_experiments",
        "matched_evidence",
        "decision",
    }
    missing = sorted(required - set(payload))
    if missing:
        raise SystemExit(
            "runs/harness-comparison/latest.json is missing required fields: "
            + ", ".join(missing)
        )
    if set(payload.get("matched_evidence", {})) != {"hierarchical", "master-worker"}:
        raise SystemExit(
            "runs/harness-comparison/latest.json must report hierarchical and master-worker arms"
        )
    return payload


def render_current_snapshot(
    page_path: str,
    modules: list[dict[str, Any]],
    declarations: list[dict[str, Any]],
    chapters: list[dict[str, Any]],
    results: list[dict[str, Any]],
    verified: bool,
) -> str:
    """Render a compact, evidence-derived answer to 'what changed?' on the landing page."""
    comparison = load_harness_comparison()
    matched_count = len(comparison["matched_experiments"])
    minimum_count = int(comparison["minimum_matched_experiments"])
    decision = comparison["decision"]
    decision_status = str(decision.get("status", "unrecorded")).replace("-", " ")
    next_harness = str(decision.get("next_experiment_harness", "unrecorded"))
    source_theorem_count = sum(
        int(bool(reading.get("source_theorem"))) + len(reading.get("source_theorems", []))
        for reading in SITE_READINGS.values()
    )
    frontier = next(
        (
            result
            for result in results
            if result.get("id") == "NEURIPS-2025-SGB-PHASE-TRANSITION-FOLLOWON"
        ),
        None,
    )
    if frontier is None:
        raise SystemExit("results.json is missing the current SGB Theorem-2 frontier")
    first_missing = str(frontier.get("missing", ["No open bridge recorded."])[0])
    frontier_href = href_from(
        page_path,
        f"implementation-map/index.html#{slugify(frontier['id'])}",
    )
    placeholder_count = sum(1 for declaration in declarations if declaration["placeholder"])
    proof_count = sum(
        1 for declaration in declarations if declaration["kind"] in {"theorem", "lemma"}
    )
    verification_badge = status_badge("compiled" if verified and not placeholder_count else "source")
    snapshot_href = f"{GITHUB_REPO}/tree/{SOURCE_BRANCH}"
    return f"""
<section class="current-snapshot" id="current-snapshot" aria-labelledby="current-snapshot-title">
  <div class="snapshot-heading">
    <div><p class="eyebrow">Current evidence snapshot</p><h2 id="current-snapshot-title">What is available now—and what is still open</h2></div>
    <a class="snapshot-commit" href="{snapshot_href}">Source <code>{html.escape(SOURCE_BRANCH[:12])}</code> ↗</a>
  </div>
  <p class="section-intro">These cards are generated from the Lean index, teaching crosswalks, implementation ledger, and harness-comparison log. They are not hand-entered completion percentages.</p>
  <div class="evidence-snapshot-grid">
    <article class="snapshot-card">
      <div class="snapshot-card-top"><span class="level-label">Lean snapshot</span>{verification_badge}</div>
      <strong class="snapshot-value">{len(declarations):,}</strong>
      <span class="snapshot-unit">indexed declarations</span>
      <p>{len(modules):,} modules · {proof_count:,} theorems and lemmas · {placeholder_count:,} declarations with <code>sorry</code> or <code>admit</code>.</p>
      <a href="{href_from(page_path, 'declarations/index.html')}">Search exact declarations →</a>
    </article>
    <article class="snapshot-card">
      <div class="snapshot-card-top"><span class="level-label">Teaching layer</span><span class="status integrated">Source mapped</span></div>
      <strong class="snapshot-value">{len(chapters)}</strong>
      <span class="snapshot-unit">Book Map chapters</span>
      <p>{source_theorem_count} source-theorem restatements and {len(SITE_TEXTBOOK_SPINE.get('chapters', []))} Part-IV chapter pages connect algorithms, page references, mathematics, and Lean.</p>
      <a href="{href_from(page_path, 'learning/index.html')}">Follow a reading route →</a>
    </article>
    <article class="snapshot-card">
      <div class="snapshot-card-top"><span class="level-label">Harness comparison</span>{status_badge('prototype')}</div>
      <strong class="snapshot-value">{matched_count}/{minimum_count}</strong>
      <span class="snapshot-unit">matched experiments</span>
      <p>Decision: {html.escape(decision_status)}. The default is retained; the next evidence-gathering arm is <code>{html.escape(next_harness)}</code>.</p>
      <a href="{href_from(page_path, 'workflow/index.html#comparison-evidence')}">Inspect the comparison ledger →</a>
    </article>
    <article class="snapshot-card">
      <div class="snapshot-card-top"><span class="level-label">Active theorem frontier</span>{status_badge(frontier['status'])}</div>
      <strong class="snapshot-title">SGB Theorem-2 follow-on</strong>
      <p><strong>First named open bridge.</strong> {html.escape(first_missing)}</p>
      <a href="{frontier_href}">Open evidence and remaining gaps →</a>
    </article>
  </div>
</section>
"""


def build_index(
    output: Path,
    modules: list[dict[str, Any]],
    declarations: list[dict[str, Any]],
    chapters: list[dict[str, Any]],
    authors: list[dict[str, Any]],
    results: list[dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    page_path = "index.html"
    counts = Counter(decl["kind"] for decl in declarations)
    status_counts = Counter(result["status"] for result in results)
    placeholder_count = sum(1 for decl in declarations if decl["placeholder"])
    book_map = render_book_map(page_path, chapters)
    learning_routes = render_learning_routes(page_path)
    textbook_spine_map = render_textbook_spine_map(page_path, SITE_TEXTBOOK_SPINE, verified)
    contributor_cards = render_contributor_cards(page_path, authors, include_invitation=False)
    primary_textbook = render_primary_textbook_banner()
    current_snapshot = render_current_snapshot(
        page_path,
        modules,
        declarations,
        chapters,
        results,
        verified,
    )
    wiki_cases = SITE_BANDITRLWIKI.get("cases", [])
    wiki_families = SITE_BANDITRLWIKI.get("families", [])
    wiki_source_pending = sum(
        1 for case in wiki_cases if case["comparison"]["status"] == "source-audit-pending"
    )
    body = f"""
<section class="hero" id="overview">
  <p class="eyebrow">Verified bandit and reinforcement-learning theory in Lean</p>
  <h1>BanditRLlib</h1>
  <p class="lede">Learn bandit and reinforcement-learning theory beside its compiled Lean interfaces, search exact declarations, and contribute one reviewable lemma at a time.</p>
  <div class="hero-actions">
    <a class="button primary" href="{href_from(page_path, 'learning/index.html')}">Start the Book Map</a>
    <a class="button" href="{href_from(page_path, 'declarations/index.html')}">Search Declarations</a>
    <a class="button" href="{href_from(page_path, 'community/index.html')}">Contribute a Lemma</a>
  </div>
  {primary_textbook}
  <p class="paper-title"><strong>Paper.</strong> {html.escape(PAPER_TITLE)}</p>
  <p class="hero-secondary-links"><a href="{GITHUB_REPO}">GitHub repository ↗</a><span aria-hidden="true">·</span><a href="{href_from(page_path, 'banditrlwiki/index.html')}">Compare minimax frontiers</a><span aria-hidden="true">·</span><a href="{href_from(page_path, 'ide/index.html')}">Local experimental workspace</a></p>
</section>

{current_snapshot}

<section id="two-systems">
  <p class="eyebrow">Powered by two connected systems</p>
  <h2>One engine produces verified mathematics; one library makes it reusable.</h2>
  <div class="two-system-grid">
    <article class="info-card system-card"><span class="level-label">Research system</span><h3>ABRL Adaptive Harness</h3><p>A fixed mathematical target enters an evidence-aware scheduler. The hierarchical route remains the default; bounded master–worker trials are compared on substantive proof progress before both routes meet the same Lean and reviewer gate.</p><a href="{href_from(page_path, 'workflow/index.html')}">Inspect the ABRL harness →</a></article>
    <article class="info-card system-card"><span class="level-label">User-facing library</span><h3>BanditRLlib</h3><p>Compiled Lean declarations → searchable reusable library → textbook-aligned learning → LaTeX↔Lean formalization → community lemma intake.</p><a href="{href_from(page_path, 'declarations/index.html')}">Browse BanditRLlib →</a></article>
  </div>
  {render_diagram(page_path, 'system-architecture.mmd', 'A research target enters ABRL and returns as reusable, reviewer-gated BanditRLlib mathematics')}
</section>

<section id="three-roles">
  <h2>BanditRLlib, three ways to use it</h2>
  <div class="role-grid">
    <article class="role-card learn-role">
      <span class="role-number">01</span><p class="eyebrow">For students</p>
      <h3>Learn from a Lean-aligned textbook</h3>
      <p>Follow ten chapters from finite bandit bookkeeping through concentration, stochastic and adversarial algorithms, stopping times, and finite-horizon RL. Read intuition and mathematics before opening the exact type.</p>
      <a href="{href_from(page_path, 'learning/index.html')}">Follow the teaching path →</a>
    </article>
    <article class="role-card browse-role">
      <span class="role-number">02</span><p class="eyebrow">For library users</p>
      <h3>Find the exact lemma you need</h3>
      <p>Search all {len(declarations):,} indexed declarations, filter by chapter and kind, inspect module imports, and distinguish compiled endpoints from broader routes that remain partial or blocked.</p>
      <a href="{href_from(page_path, 'declarations/index.html')}">Search the declaration catalog →</a>
    </article>
    <article class="role-card contribute-role">
      <span class="role-number">03</span><p class="eyebrow">For contributors</p>
      <h3>Add knowledge from another field</h3>
      <p>Submit a structured lemma packet with the source theorem, natural-language statement, LaTeX, Lean draft, dependencies, and honest verification status. Live Formalization already exports the same machine-readable format for ABRL review.</p>
      <a href="{href_from(page_path, 'community/index.html')}">Read the contribution guide →</a>
    </article>
  </div>
</section>

<details class="homepage-details">
  <summary><span>Project scope and completion boundaries</span><small>Live inventory · project purpose</small></summary>
  <div class="homepage-details-content">
<section id="live-inventory">
  <h2>Live source inventory</h2>
  <p>The numbers below are generated from the current internal <code>BanditRLProof/</code> namespace at build time. <strong>BanditRLlib</strong> is the public library name; the mature namespace is intentionally unchanged.</p>
  <div class="stats-grid">
    <div class="stat"><span class="stat-value">{len(modules):,}</span><span class="stat-label">Lean source modules, including the root aggregator</span></div>
    <div class="stat"><span class="stat-value">{len(declarations):,}</span><span class="stat-label">Indexed definitions, structures, theorems, and lemmas</span></div>
    <div class="stat"><span class="stat-value">{counts['theorem'] + counts['lemma']:,}</span><span class="stat-label">Theorems and lemmas</span></div>
    <div class="stat"><span class="stat-value">{placeholder_count:,}</span><span class="stat-label">Declarations containing <code>sorry</code> or <code>admit</code></span></div>
  </div>
  <div class="callout warning"><strong>Two levels of completion.</strong> A local declaration can compile while a broader textbook or upstream-compatible route remains partial. The site reports both levels separately; theorem cards and paper references are never counted as local proofs.</div>
</section>

<section id="purpose">
  <h2>What this project is building</h2>
  <p>Bandit and reinforcement-learning proofs mix finite combinatorics, probability kernels, conditional expectation, concentration, optimization, and algorithm-specific bookkeeping. ABRL organizes that work into small Lean-checkable leaves. An automated hierarchy proposes and proves leaves; reinforcement-learning ideas help select promising proof routes; bandit objectives allocate effort among those routes; and Lean is the final certificate.</p>
  <p>The current tree is no longer only a finite-bandit foundation. It contains concrete ETC, ordinary UCB, a conservative bounded generated KL-UCB route, stationary Thompson, EXP3, and Tsallis endpoints; an OFUL chain reaching self-normalized confidence and one horizon-free policy with all-time, all-horizon, and stopping consumers, plus a separately labeled horizon-indexed expected-consistency family; and a finite-horizon RL development that now reaches a canonical known-reward Hoeffding UCBVI-CH high-probability cumulative episode pseudo-regret theorem and its failure-aware expected consumer on one generated adaptive process. Natural-causal consistency and stopping-time RL remain independent compiled extensions. Bernstein/minimax and stochastic-reward UCBVI, sharp KL-Chernoff and asymptotically optimal KL-UCB refinements, full BwK, preference, federated, and several modern routes remain partial, planned, or blocked at named interfaces.</p>
  <div class="callout"><strong>Identity boundary.</strong> ABRL is the proving system and research project. BanditRLlib is the verified Lean library, website, formalization workspace, and contribution interface produced by that system.</div>
</section>
  </div>
</details>

<section id="banditrlwiki">
  <p class="eyebrow">Upper bounds · lower bounds · local Lean evidence</p>
  <h2>BanditRLwiki: compare results under the same assumptions</h2>
  <p>The research atlas currently indexes {len(wiki_cases)} theorem-comparison cases across {len(wiki_families)} assumption families. Each case fixes its reward model, feedback, horizon, regret notion, and salient parameters before comparing rates. Published optimality, theorem-level source audit, and local Lean compilation are three independent ledgers.</p>
  <div class="two-system-grid">
    <article class="info-card"><span class="level-label">Literature map</span><h3>Find the best compatible upper and lower theorem</h3><p>Open a setting, inspect the precise comparison signature, follow primary-paper links, and see every remaining logarithmic, constant, parameter, or model-class mismatch.</p><a href="{href_from(page_path, 'banditrlwiki/index.html')}">Open BanditRLwiki →</a></article>
    <article class="info-card"><span class="level-label">Frontier leaves</span><h3>Separate open mathematics from open formalization</h3><p>{wiki_source_pending} {'case remains' if wiki_source_pending == 1 else 'cases remain'} in the source-audit queue. The Frontier never turns a missing reference into a literature-open claim, and every Lean blocker names the exact missing bridge.</p><a href="{href_from(page_path, 'banditrlwiki/frontier/index.html')}">Inspect frontier leaves →</a></article>
  </div>
</section>

<section id="book-map">
  <p class="eyebrow">Formalized textbook map</p>
  <h2>Book map: ten routes through bandits and RL</h2>
  <p class="section-intro">The curriculum is anchored in Lattimore and Szepesvári's <em>Bandit Algorithms</em>, with algorithm-specific papers for OFUL, Tsallis-INF, and UCBVI. It is a source-mapped learning path, not a chapter-for-chapter reproduction of one book. Each card reports online-edition pages and the chapter's canonical compiled boundary.</p>
  {book_map}
</section>

<details class="homepage-details">
  <summary><span>More project paths</span><small>Part IV spine · contributors · installation</small></summary>
  <div class="homepage-details-content">
<section id="textbook-spine">
  <p class="eyebrow">Chapter-by-chapter source spine</p>
  <h2>Part IV: Lower Bounds</h2>
  <p class="section-intro">This separate layer follows Chapters 13–17 of <em>Bandit Algorithms</em> in order. It does not change the ten-chapter Book Map or imply that the whole textbook is complete.</p>
  {textbook_spine_map}
  <p><a class="button" href="{href_from(page_path, 'textbook-spine/index.html')}">Open the Part IV spine</a></p>
</section>

<section id="contributors">
  <p class="eyebrow">People behind the project</p>
  <h2>Authors</h2>
  <p>The project authors are listed separately from future community contributors. Roles are intentionally neutral unless contribution metadata is explicitly recorded.</p>
  {contributor_cards}
  <p><a class="button" href="{href_from(page_path, 'contributors/index.html')}">Meet the contributors</a></p>
</section>

<section id="installation">
  <p class="eyebrow">Reproduce the formalization</p>
  <h2>Installation</h2>
  <div class="installation-steps compact-steps">
    <article><span>01</span><h3>Install Lean</h3><p>Install Git, Python 3, and <a href="https://lean-lang.org/install/">Lean through Elan</a>. The repository pins <code>leanprover/lean4:v4.29.1</code>.</p></article>
    <article><span>02</span><h3>Clone the repository</h3><pre class="command-block" tabindex="0" role="region" aria-label="Repository clone commands"><code>git clone {GITHUB_REPO}.git
cd Auto-Bandit-RL-Proof-In-Sleep</code></pre></article>
    <article><span>03</span><h3>Run the proof gate</h3><pre class="command-block" tabindex="0" role="region" aria-label="Lean proof gate commands"><code>lake update
python3 tools/bandit.py check</code></pre></article>
  </div>
  <p><a class="button" href="{href_from(page_path, 'installation/index.html')}">Full installation guide</a></p>
</section>
  </div>
</details>

<section id="how-to-contribute">
  <p class="eyebrow">A reviewable path into the library</p>
  <h2>How to contribute</h2>
  <ol class="contribution-steps">
    <li><strong>Choose one claim.</strong><span>Start from a book, paper, proof gap, or existing chapter and record the exact source and assumptions.</span></li>
    <li><strong>Agree on the statement.</strong><span>Open a lemma proposal before a large formalization so scope, namespace, and dependencies can be reviewed.</span></li>
    <li><strong>Compile and explain.</strong><span>Add the Lean declaration, tests, plain-English statement, proof idea, and an honest status.</span></li>
    <li><strong>Submit for integration.</strong><span>The project gate and maintainer review decide when a result becomes indexed as compiled.</span></li>
  </ol>
  <div class="hero-actions"><a class="button primary" href="{href_from(page_path, 'community/index.html')}">Read how to contribute</a><a class="button" href="{GITHUB_REPO}/issues/new?template=lemma-proposal.yml">Propose a lemma</a></div>
</section>

<details class="homepage-details">
  <summary><span>Research details and local tools</span><small>Progress · reading routes · Live Formalization</small></summary>
  <div class="homepage-details-content">
<section id="progress">
  <h2>Progress without invented percentages</h2>
  <p>This chart counts the explicit milestones in the website's implementation map. It does not estimate what percentage of all bandit or RL mathematics has been formalized.</p>
  {render_diagram(page_path, 'progress.mmd', 'Status of the explicitly mapped theorem-route milestones', status_counts)}
</section>

<section id="reading-order">
  <p class="eyebrow">Choose a mathematical route</p>
  <h2>Five reading paths through the same library</h2>
  <p>Each route reuses the common foundations but emphasizes a different proof technology. These are pedagogical paths, not additional completion claims.</p>
  {learning_routes}
</section>

<section id="research-workspace">
  <h2>BanditRLlib and Live Formalization share one contribution language</h2>
  <p>The workspace renders editable LaTeX, loads reviewed LaTeX-to-Lean mappings, visualizes declaration dependencies, and can call the pinned Lean compiler through a loopback-only companion server. It can now export a versioned lemma packet for community review; a future authenticated compiler can submit that same packet directly as a proposed contribution.</p>
  <div class="callout warning"><strong>Static-site boundary.</strong> GitHub Pages does not compile Lean or send source to a hosted proving service. Compilation and provider-backed formalization require the explicitly started loopback-only local companion server.</div>
  <div class="hero-actions"><a class="button primary" href="{href_from(page_path, 'ide/index.html')}">Open Live Formalization</a><a class="button" href="{href_from(page_path, 'community/index.html#machine-contract')}">Inspect the contribution contract</a></div>
</section>
  </div>
</details>
"""
    toc = [
        ("overview", "Overview"),
        ("primary-textbook", "Primary textbook"),
        ("current-snapshot", "Current evidence"),
        ("two-systems", "ABRL + BanditRLlib"),
        ("three-roles", "Three ways to use BanditRLlib"),
        ("live-inventory", "Live inventory"),
        ("purpose", "Project purpose"),
        ("banditrlwiki", "BanditRLwiki"),
        ("book-map", "Book map"),
        ("textbook-spine", "Part IV spine"),
        ("contributors", "Contributors"),
        ("installation", "Installation"),
        ("how-to-contribute", "How to contribute"),
        ("progress", "Progress"),
        ("reading-order", "Reading order"),
        ("research-workspace", "Live Formalization"),
    ]
    write_page(
        output,
        page_path,
        layout(page_path, "Overview", body, toc, "overview", verified, generated_at),
    )


def build_implementation_map(
    output: Path,
    modules: list[dict[str, Any]],
    decl_by_name: dict[str, dict[str, Any]],
    chapter_by_slug: dict[str, dict[str, Any]],
    results: list[dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    page_path = "implementation-map/index.html"
    result_rows = []
    result_items = []
    for result in results:
        declaration_links = []
        for name in result["declarations"]:
            decl = decl_by_name[name]
            declaration_links.append(
                f'<a href="{declaration_href(page_path, decl)}"><code>{html.escape(name)}</code></a>'
            )
        dependencies = "<br>".join(
            f"<code>{html.escape(name)}</code>" for name in result.get("depends_on", [])
        ) or "No recorded prerequisite milestone."
        missing = "<br>".join(html.escape(item) for item in result["missing"]) or "No remaining gap inside this milestone contract."
        chapter = chapter_by_slug[result["chapter"]]
        chapter_href = href_from(page_path, f"chapters/{chapter['slug']}/index.html")
        chapter_cell = (
            f'<a href="{chapter_href}">{html.escape(chapter["short_title"])}</a>'
        )
        if result.get("textbook_spine"):
            spine_chapter = next(
                item for item in SITE_TEXTBOOK_SPINE["chapters"]
                if item["slug"] == result["textbook_spine"]
            )
            spine_href = href_from(
                page_path, f"textbook-spine/{spine_chapter['slug']}/index.html"
            )
            chapter_cell = (
                f'<a href="{spine_href}">'
                f'Part IV · Chapter {spine_chapter["number"]}</a>'
            )
        search = html.escape(
            f"{result['id']} {result['title']} {result['informal']} {chapter['short_title']}".lower(),
            quote=True,
        )
        row_html = f"""
<tr id="{slugify(result['id'])}" data-milestone-row data-search="{search}" data-status="{html.escape(result['status'])}" data-chapter="{html.escape(result['chapter'])}">
  <td><a href="#{slugify(result['id'])}">{html.escape(result['title'])}</a><br><code>{html.escape(result['id'])}</code></td>
  <td>{chapter_cell}</td>
  <td>{status_badge(result['status'])}</td>
  <td class="milestone-evidence"><p>{html.escape(result['informal'])}</p><details><summary>Lean evidence and boundary</summary><dl><div><dt>Declarations</dt><dd>{"<br>".join(declaration_links) if declaration_links else "No local declaration yet"}</dd></div><div><dt>Depends on</dt><dd>{dependencies}</dd></div><div><dt>Remaining gap</dt><dd>{missing}</dd></div></dl></details></td>
</tr>"""
        result_rows.append(row_html)
        result_items.append(
            {
                "id": slugify(result["id"]),
                "search": f"{result['id']} {result['title']} {result['informal']} {chapter['short_title']}".lower(),
                "status": result["status"],
                "chapter": result["chapter"],
                "html": row_html,
            }
        )
    write_text_lf(
        output / "implementation-map" / "milestone-data.json",
        json.dumps(
            {"page_size": MILESTONE_PAGE_SIZE, "items": result_items},
            ensure_ascii=False,
            separators=(",", ":"),
        ),
    )
    module_rows = []
    for module in modules:
        chapter = chapter_by_slug[module["chapter"]]
        module_status = "stated" if module["placeholder_count"] else ("compiled" if verified else "source")
        module_rows.append(
            f"""
<tr data-module-row data-search="{html.escape(f'{module["name"]} {chapter["short_title"]} {module["file"]}'.lower(), quote=True)}" data-chapter="{html.escape(module['chapter'])}">
  <td><a href="{module_href(page_path, module)}"><code>{html.escape(module['name'])}</code></a></td>
  <td><a href="{href_from(page_path, f"chapters/{chapter['slug']}/index.html")}">{html.escape(chapter['short_title'])}</a></td>
  <td>{len(module['declarations']):,}</td>
  <td>{len(module['imports']):,}</td>
  <td>{status_badge(module_status)}</td>
  <td><a href="{source_url(module['file'])}">{html.escape(module['file'])}</a></td>
</tr>"""
        )
    body = f"""
<section class="hero" id="map">
  <p class="eyebrow">Mathematics ↔ prose ↔ Lean</p>
  <h1 class="page-title">Implementation map</h1>
  <p class="lede">A theorem-route milestone can be locally compiled, partial, stated without a finished proof, planned, or blocked. The declaration catalog below is generated from source; the milestone ledger records the mathematical boundary.</p>
</section>

<section id="status-key">
  <h2>Status vocabulary</h2>
  <div class="card-grid">
    <div class="info-card">{status_badge('compiled')}<p>The named declaration exists and the publishing gate compiled the Lean project.</p></div>
    <div class="info-card">{status_badge('partial')}<p>Useful declarations compile, but the stated route still has named missing steps.</p></div>
    <div class="info-card">{status_badge('stated')}<p>A target or Lean declaration is stated but its proof is incomplete. None is promoted to compiled.</p></div>
    <div class="info-card">{status_badge('planned')}<p>The result is part of the roadmap but has no claimed local endpoint.</p></div>
    <div class="info-card">{status_badge('blocked')}<p>Progress requires a specific missing law transport, algorithm construction, or mathematical interface.</p></div>
  </div>
  {render_diagram(page_path, 'formalization-map.mmd', 'How informal mathematics and Lean declarations cross-link')}
</section>

<section id="milestones">
  <h2>Mathematical milestone map</h2>
  <p class="section-intro">Start with the mathematical claim and status. Open a row's evidence only when you need exact declarations, dependencies, and the remaining boundary.</p>
  <div class="filter-bar" data-milestone-filters>
    <div class="filter-field grow"><label for="milestone-query">Milestone, concept, or chapter</label><input id="milestone-query" data-milestone-query type="search" placeholder="e.g. UCBVI, posterior, all-time"></div>
    <div class="filter-field"><label for="milestone-status">Status</label><select id="milestone-status" data-milestone-status><option value="">All statuses</option>{''.join(f'<option value="{status}">{STATUS_LABELS.get(status, status.title())}</option>' for status in ('compiled', 'partial', 'planned', 'blocked', 'stated'))}</select></div>
    <div class="filter-field"><label for="milestone-chapter">Chapter</label><select id="milestone-chapter" data-milestone-chapter><option value="">All chapters</option>{''.join(f'<option value="{chapter["slug"]}">{html.escape(chapter["short_title"])}</option>' for chapter in chapter_by_slug.values())}</select></div>
  </div>
  <p class="result-count" data-milestone-count aria-live="polite">Showing the first {min(MILESTONE_PAGE_SIZE, len(result_rows))} of {len(result_rows)} milestones.</p>
  <div class="table-wrap" data-milestone-list data-milestone-total="{len(result_rows)}" data-milestone-page-size="{MILESTONE_PAGE_SIZE}" tabindex="0" role="region" aria-label="Mathematical milestones">
    <table>
      <thead><tr><th>Result</th><th>Chapter</th><th>Status</th><th>Meaning and evidence</th></tr></thead>
      <tbody data-milestone-body>{''.join(result_rows[:MILESTONE_PAGE_SIZE])}</tbody>
    </table>
  </div>
  <div class="catalog-actions"><button class="button compact" type="button" data-milestone-more hidden>Show {min(MILESTONE_PAGE_SIZE, max(0, len(result_rows) - MILESTONE_PAGE_SIZE))} more milestones</button></div>
  <noscript><p class="callout warning"><strong>JavaScript is off.</strong> The first {min(MILESTONE_PAGE_SIZE, len(result_rows))} milestones are shown here. Open the <a href="milestone-data.json">complete generated milestone ledger</a> for all {len(result_rows)} records.</p></noscript>
</section>

<section id="dependencies">
  <h2>Major theorem dependencies</h2>
  <p>The overview names the shared core; five focused, editable diagrams preserve readable labels for each algorithm family. Module pages list the exact import dependencies for every Lean source file.</p>
  {render_diagram(page_path, 'theorem-dependencies.mmd', 'Overview of the five theorem-dependency routes', extra_class='dependency-diagram dependency-overview')}
  <div class="dependency-atlas">
    {render_diagram(page_path, 'theorem-dependencies-stochastic.mmd', 'Finite stochastic bandit, ETC, and UCB dependencies', extra_class='dependency-diagram')}
    {render_diagram(page_path, 'theorem-dependencies-oful.mmd', 'OFUL confidence, regret, and stopping dependencies', extra_class='dependency-diagram')}
    {render_diagram(page_path, 'theorem-dependencies-thompson.mmd', 'Thompson sampling and Bayesian-regret dependencies', extra_class='dependency-diagram')}
    {render_diagram(page_path, 'theorem-dependencies-adversarial.mmd', 'EXP3 and Tsallis-FTRL dependencies', extra_class='dependency-diagram')}
    {render_diagram(page_path, 'theorem-dependencies-rl.mmd', 'Finite-horizon RL and UCBVI dependencies', extra_class='dependency-diagram')}
  </div>
</section>

<section id="modules">
  <h2>Complete module inventory</h2>
  <p>Every project module is assigned to a teaching chapter. This exhaustive inventory is collapsed by default so that the mathematical milestones remain the primary reading surface.</p>
  <details class="inventory-disclosure"><summary>Open the complete generated module inventory ({len(modules):,} modules)</summary>
  <div class="filter-bar"><div class="filter-field grow"><label for="module-query">Filter modules</label><input id="module-query" data-module-query type="search" placeholder="Module, chapter, or source path"></div></div>
  <p class="result-count" data-module-count></p>
  <div class="table-wrap" data-module-list tabindex="0" role="region" aria-label="Complete Lean module inventory">
    <table>
      <thead><tr><th>Lean module</th><th>Teaching chapter</th><th>Declarations</th><th>Project imports</th><th>Build status</th><th>Source</th></tr></thead>
      <tbody>{''.join(module_rows)}</tbody>
    </table>
  </div>
  </details>
</section>
"""
    toc = [
        ("map", "Implementation map"),
        ("status-key", "Status vocabulary"),
        ("milestones", "Milestones"),
        ("dependencies", "Dependencies"),
        ("modules", "Modules"),
    ]
    write_page(
        output,
        page_path,
        layout(page_path, "Implementation map", body, toc, "map", verified, generated_at),
    )


def build_catalog(
    output: Path,
    declarations: list[dict[str, Any]],
    chapters: list[dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    page_path = "declarations/index.html"
    kinds = sorted({decl["kind"] for decl in declarations})
    rows = []
    catalog_items = []
    for decl in declarations:
        status = (
            "stated"
            if decl["placeholder"] or decl["kind"] == "axiom"
            else ("compiled" if verified else "source")
        )
        search_text = (
            f"{decl['full_name']} {decl['kind']} {decl['module']} {decl['file']} {decl['chapter_title']}".lower()
        )
        search = html.escape(search_text, quote=True)
        declaration_url = declaration_href(page_path, decl)
        declaration_module_url = module_href(page_path, {"slug": decl["module_slug"]})
        declaration_source_url = source_url(decl["file"], decl["line"])
        catalog_items.append(
            {
                "name": decl["full_name"],
                "kind": decl["kind"],
                "kind_label": KIND_LABELS.get(decl["kind"], decl["kind"]),
                "module": decl["module"],
                "module_url": declaration_module_url,
                "chapter": decl["chapter"],
                "chapter_title": decl["chapter_title"],
                "status": status,
                "status_label": STATUS_LABELS[status],
                "url": declaration_url,
                "source_url": declaration_source_url,
                "source_label": f"{decl['file']}:{decl['line']}",
                "search": search_text,
            }
        )
        if len(rows) >= CATALOG_PAGE_SIZE:
            continue
        rows.append(
            f"""
<tr data-catalog-row data-search="{search}" data-kind="{decl['kind']}" data-status="{status}" data-chapter="{decl['chapter']}">
  <td><a href="{declaration_url}"><code>{html.escape(decl['full_name'])}</code></a></td>
  <td>{html.escape(KIND_LABELS.get(decl['kind'], decl['kind']))}</td>
  <td>{html.escape(decl['chapter_title'])}</td>
  <td><a href="{declaration_module_url}"><code>{html.escape(decl['module'])}</code></a></td>
  <td>{status_badge(status)}</td>
  <td><a href="{declaration_source_url}">{html.escape(decl['file'])}:{decl['line']}</a></td>
</tr>"""
        )
    write_text_lf(
        output / "catalog-data.json",
        json.dumps(
            {"page_size": CATALOG_PAGE_SIZE, "items": catalog_items},
            ensure_ascii=False,
            separators=(",", ":"),
        ),
    )
    kind_options = "".join(
        f'<option value="{kind}">{html.escape(KIND_LABELS.get(kind, kind))}</option>' for kind in kinds
    )
    chapter_options = "".join(
        f'<option value="{chapter["slug"]}">{html.escape(chapter["short_title"])}</option>'
        for chapter in chapters
    )
    body = f"""
<section class="hero" id="catalog">
  <p class="eyebrow">Generated from every Lean source module</p>
  <h1 class="page-title">Declaration catalog</h1>
  <p class="lede">{len(declarations):,} indexed public and private declarations. The catalog is exhaustive for the supported declaration kinds; teaching chapters add detailed explanations to the major mathematical interfaces.</p>
</section>

<section id="catalog-map">
  <h2>From a concept to reusable Lean</h2>
  <p>Every search result links to its exact statement, source location, module context, chapter explanation, and recorded dependency neighborhood.</p>
  {render_diagram(page_path, 'library-query.mmd', 'How a BanditRLlib concept search leads to source, dependencies, consumers, and teaching context')}
</section>

<section id="filters">
  <h2>Search and filter</h2>
  <div class="filter-bar">
    <div class="filter-field grow"><label for="catalog-query">Name, module, file, or chapter</label><input id="catalog-query" data-catalog-query type="search" placeholder="e.g. conditional MGF, UCB, pullCount"></div>
    <div class="filter-field"><label for="catalog-kind">Kind</label><select id="catalog-kind" data-catalog-kind><option value="">All kinds</option>{kind_options}</select></div>
    <div class="filter-field"><label for="catalog-status">Status</label><select id="catalog-status" data-catalog-status><option value="">All statuses</option><option value="compiled">Compiled</option><option value="stated">Stated/incomplete</option><option value="source">Source indexed</option></select></div>
    <div class="filter-field"><label for="catalog-chapter">Chapter</label><select id="catalog-chapter" data-catalog-chapter><option value="">All chapters</option>{chapter_options}</select></div>
  </div>
  <p class="result-count" id="catalog-count" data-catalog-count aria-live="polite">Showing the first {min(CATALOG_PAGE_SIZE, len(declarations)):,} of {len(declarations):,} declarations.</p>
</section>

<section id="declaration-table">
  <div class="table-wrap" data-catalog tabindex="0" role="region" aria-label="Lean declaration catalog" aria-describedby="catalog-count">
    <table>
      <thead><tr><th>Declaration</th><th>Kind</th><th>Chapter</th><th>Module</th><th>Status</th><th>Source</th></tr></thead>
      <tbody data-catalog-body>{''.join(rows)}</tbody>
    </table>
  </div>
  <div class="catalog-actions"><button class="button compact" type="button" data-catalog-more hidden>Show {min(CATALOG_PAGE_SIZE, max(0, len(declarations) - CATALOG_PAGE_SIZE)):,} more declarations</button></div>
  <noscript><p class="callout warning"><strong>JavaScript is off.</strong> The first {min(CATALOG_PAGE_SIZE, len(declarations)):,} declarations are shown here. Open the <a href="{href_from(page_path, 'catalog-data.json')}">complete JSON catalog</a> or browse the <a href="{href_from(page_path, 'implementation-map/index.html')}">module-level implementation map</a>.</p></noscript>
</section>
"""
    toc = [
        ("catalog", "Declaration catalog"),
        ("catalog-map", "How to read it"),
        ("filters", "Search and filter"),
        ("declaration-table", "All declarations"),
    ]
    write_page(
        output,
        page_path,
        layout(page_path, "Declaration catalog", body, toc, "catalog", verified, generated_at),
    )


def build_chapters(
    output: Path,
    modules: list[dict[str, Any]],
    chapters: list[dict[str, Any]],
    highlights: list[dict[str, Any]],
    results: list[dict[str, Any]],
    decl_by_name: dict[str, dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    modules_by_chapter: dict[str, list[dict[str, Any]]] = defaultdict(list)
    highlights_by_chapter: dict[str, list[dict[str, Any]]] = defaultdict(list)
    results_by_chapter: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for module in modules:
        modules_by_chapter[module["chapter"]].append(module)
    for highlight in highlights:
        highlights_by_chapter[highlight["chapter"]].append(highlight)
    for result in results:
        results_by_chapter[result["chapter"]].append(result)

    for chapter_index, chapter in enumerate(chapters):
        page_path = f"chapters/{chapter['slug']}/index.html"
        goals = render_list(chapter["learning_goals"])
        reading = SITE_READINGS[chapter["slug"]]
        chapter_compass = render_chapter_compass(page_path, chapter, reading)
        reading_guide = render_reading_guide(page_path, chapter, reading)
        completion_contract = ""
        if chapter.get("completion_definition"):
            completion_contract = f"""
<section id="completion-contract">
  <h2>Maintainer contract</h2>
  <details class="maintainer-contract"><summary>Open the canonical completion definition and blockers</summary><div>
    <p>{html.escape(chapter['completion_definition'])}</p>
    <h3>Remaining blockers</h3>
    {render_list(chapter.get('completion_blockers', []))}
  </div></details>
</section>
"""
        chapter_highlights = sorted(
            highlights_by_chapter[chapter["slug"]],
            key=lambda item: int(item.get("teaching_order", 10_000)),
        )
        if len(chapter_highlights) > TEACHING_PREVIEW_COUNT:
            featured_highlights = [item for item in chapter_highlights if item.get("featured") is True]
            if not featured_highlights or len(featured_highlights) > TEACHING_PREVIEW_COUNT:
                raise SystemExit(
                    f"chapter {chapter['slug']} needs between one and {TEACHING_PREVIEW_COUNT} "
                    "explicit featured highlights before extended notes can be collapsed"
                )
        else:
            featured_highlights = chapter_highlights
        visible_highlights = [
            item for item in featured_highlights if item.get("source_match") != "extension"
        ]
        extended_highlights = [
            item for item in chapter_highlights if item not in visible_highlights
        ]
        teaching = "".join(
            render_highlight(page_path, item, decl_by_name[item["full_name"]], verified)
            for item in visible_highlights
        )
        teaching_scope = ""
        if extended_highlights:
            remaining_teaching = "".join(
                render_highlight(page_path, item, decl_by_name[item["full_name"]], verified)
                for item in extended_highlights
            )
            remaining_count = len(extended_highlights)
            teaching_scope = (
                '<p class="section-intro">A curated route through definitions, key bridges, and canonical terminals stays visible. '
                f'{remaining_count} additional dependency, extension, or research-frontier notes are grouped below.</p>'
            )
            teaching += (
                '<details class="inventory-disclosure teaching-disclosure">'
                f'<summary>Explore {remaining_count} additional Lean teaching notes</summary>'
                f'<div>{remaining_teaching}</div></details>'
            )
        if not teaching:
            teaching = '<p class="empty">No extended teaching note is registered for this chapter yet; the full module catalog remains available below.</p>'
        result_rows = []
        for result in results_by_chapter[chapter["slug"]]:
            links = [
                f'<a href="{declaration_href(page_path, decl_by_name[name])}"><code>{html.escape(name)}</code></a>'
                for name in result["declarations"]
            ]
            if len(links) > 3:
                declaration_cell = (
                    '<div class="chapter-milestone-declarations">'
                    + "".join(links[:3])
                    + '<details class="chapter-milestone-more"><summary>'
                    + f'Open {len(links) - 3} more declarations'
                    + '</summary><div>'
                    + "".join(links[3:])
                    + '</div></details></div>'
                )
            else:
                declaration_cell = (
                    '<div class="chapter-milestone-declarations">'
                    + ("".join(links) if links else "No local declaration yet")
                    + '</div>'
                )
            result_rows.append(
                f"<tr><td data-label=\"Milestone\">{html.escape(result['title'])}</td>"
                f"<td data-label=\"Status\">{status_badge(result['status'])}</td>"
                f"<td data-label=\"Lean evidence\">{declaration_cell}</td>"
                f"<td data-label=\"Remaining gap\">{'<br>'.join(html.escape(item) for item in result['missing']) or '—'}</td></tr>"
            )
        module_rows = "".join(
            f"<tr><td><a href=\"{module_href(page_path, module)}\"><code>{html.escape(module['name'])}</code></a></td>"
            f"<td>{len(module['declarations']):,}</td><td>{len(module['imports']):,}</td>"
            f"<td>{status_badge('stated' if module['placeholder_count'] else ('compiled' if verified else 'source'))}</td></tr>"
            for module in modules_by_chapter[chapter["slug"]]
        )
        previous_chapter = chapters[chapter_index - 1] if chapter_index else None
        next_chapter = chapters[chapter_index + 1] if chapter_index + 1 < len(chapters) else None
        chapter_pager = render_sequence_pager(
            page_path,
            sequence_label="BanditRLlib Book Map",
            index=chapter_index,
            total=len(chapters),
            landing_path="learning/index.html",
            previous=(
                f"chapters/{previous_chapter['slug']}/index.html",
                previous_chapter["title"],
            ) if previous_chapter else None,
            next_item=(
                f"chapters/{next_chapter['slug']}/index.html",
                next_chapter["title"],
            ) if next_chapter else None,
        )
        body = f"""
<section class="hero" id="chapter">
  <p class="eyebrow">Teaching chapter {chapter_index + 1:02d} of {len(chapters):02d} · canonical scope {status_badge(chapter['status'])}</p>
  <h1 class="page-title">{html.escape(chapter['title'])}</h1>
  <p class="lede">{html.escape(chapter['summary'])}</p>
</section>

{chapter_compass}

<section id="orientation">
  <h2>Orientation</h2>
  <p><strong>Who should read this.</strong> {html.escape(chapter['audience'])}</p>
  <h3>Learning goals</h3>
  {goals}
</section>

{reading_guide}

<section id="teaching-notes">
  <h2>Natural-language and Lean side by side</h2>
  <p>The mathematical readings are explanatory summaries. The exact generated Lean statement and its source link remain authoritative for hypotheses, types, constants, and indexing.</p>
  {teaching_scope}
  {teaching}
</section>

{completion_contract}

<section id="milestones">
  <h2>Chapter implementation status</h2>
  <p class="section-intro">Each row shows three representative declarations. Open the disclosure for the complete, source-linked list.</p>
  <div class="table-wrap chapter-milestone-table" tabindex="0" role="region" aria-label="Chapter implementation milestones"><table><thead><tr><th>Milestone</th><th>Status</th><th>Lean declaration</th><th>Remaining gap</th></tr></thead><tbody>{''.join(result_rows)}</tbody></table></div>
</section>

<section id="open-gaps">
  <h2>Open boundaries</h2>
  {render_list(chapter['open_gaps'])}
</section>

<section id="module-list">
  <h2>All Lean modules in this chapter</h2>
  <details class="inventory-disclosure"><summary>Open the complete module list ({len(modules_by_chapter[chapter['slug']]):,} modules)</summary><div class="table-wrap" tabindex="0" role="region" aria-label="Lean modules in this chapter"><table><thead><tr><th>Module</th><th>Declarations</th><th>Project imports</th><th>Status</th></tr></thead><tbody>{module_rows}</tbody></table></div></details>
</section>

{chapter_pager}
"""
        toc = [
            ("chapter", "Chapter"),
            ("orientation", "Orientation"),
            ("source-guide", "Sources"),
            ("notation", "Notation"),
            ("algorithm", "Algorithm flow"),
            ("teaching-notes", "Lean teaching notes"),
        ]
        if completion_contract:
            toc.append(("completion-contract", "Maintainer contract"))
        toc.extend([
            ("milestones", "Status"),
            ("open-gaps", "Open boundaries"),
            ("module-list", "Modules"),
            ("continue-reading", "Continue reading"),
        ])
        write_page(
            output,
            page_path,
            layout(page_path, chapter["title"], body, toc, chapter["slug"], verified, generated_at),
        )


def build_module_pages(
    output: Path,
    modules: list[dict[str, Any]],
    module_by_name: dict[str, dict[str, Any]],
    chapter_by_slug: dict[str, dict[str, Any]],
    highlights_by_name: dict[str, dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    reverse: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for module in modules:
        for imported in module["imports"]:
            if imported in module_by_name:
                reverse[imported].append(module)

    for module in modules:
        page_path = f"modules/{module['slug']}/index.html"
        chapter = chapter_by_slug[module["chapter"]]
        imports = [
            f'<a href="{module_href(page_path, module_by_name[name])}"><code>{html.escape(name)}</code></a>'
            if name in module_by_name
            else f"<code>{html.escape(name)}</code>"
            for name in module["imports"]
        ]
        reverse_links = [
            f'<a href="{module_href(page_path, dependent)}"><code>{html.escape(dependent["name"])}</code></a>'
            for dependent in reverse[module["name"]]
        ]
        declarations_html = []
        for declaration in module["declarations"]:
            status = (
                "stated"
                if declaration["placeholder"] or declaration["kind"] == "axiom"
                else ("compiled" if verified else "source")
            )
            teaching_link = ""
            if declaration["full_name"] in highlights_by_name:
                teaching = highlights_by_name[declaration["full_name"]]
                teaching_target = (
                    f"chapters/{teaching['chapter']}/index.html#"
                    f"{declaration['anchor']}-teaching"
                )
                teaching_link = (
                    f'<a href="{href_from(page_path, teaching_target)}">'
                    "Open teaching explanation</a>"
                )
            docstring = (
                f'<p class="docstring">{html.escape(declaration["docstring"])}</p>'
                if declaration["docstring"]
                else '<p class="empty">No declaration docstring is present; use the chapter context and exact statement below.</p>'
            )
            private = '<span class="status source">Internal helper</span>' if declaration["private"] else ""
            declarations_html.append(
                f"""
<details class="declaration" id="{declaration['anchor']}">
  <summary>
    <span class="kind">{html.escape(declaration['kind'])}</span>
    <code>{html.escape(declaration['full_name'])}</code>
    <span>{status_badge(status)} {private}</span>
  </summary>
  <div class="declaration-content">
    {docstring}
    <pre class="lean-code"><code>{highlight_lean(declaration['statement'])}</code></pre>
    <div class="source-links">
      <a href="{source_url(declaration['file'], declaration['line'])}">Source line {declaration['line']}</a>
      {teaching_link}
      <a href="{href_from(page_path, f"chapters/{chapter['slug']}/index.html")}">Chapter context: {html.escape(chapter['short_title'])}</a>
    </div>
  </div>
</details>"""
            )
        body = f"""
<section class="hero" id="module">
  <p class="eyebrow">Lean module · {html.escape(chapter['short_title'])}</p>
  <h1 class="page-title identifier-title">{breakable_identifier(module['name'])}</h1>
  <p class="lede">{html.escape(module['summary']) if module['summary'] else 'Generated source map for this Lean module.'}</p>
</section>

<section id="metadata">
  <h2>Module map</h2>
  <dl class="module-meta">
    <div><dt>Source</dt><dd><a href="{source_url(module['file'])}"><code>{html.escape(module['file'])}</code></a></dd></div>
    <div><dt>Teaching chapter</dt><dd><a href="{href_from(page_path, f"chapters/{chapter['slug']}/index.html")}">{html.escape(chapter['title'])}</a></dd></div>
    <div><dt>Declarations</dt><dd>{len(module['declarations']):,}</dd></div>
    <div><dt>Placeholders</dt><dd>{module['placeholder_count']:,}</dd></div>
  </dl>
  <h3>Imports</h3>
  <p>{', '.join(imports) if imports else '<span class="empty">No project-local imports.</span>'}</p>
  <h3>Imported by</h3>
  <p>{', '.join(reverse_links) if reverse_links else '<span class="empty">No project-local reverse dependency.</span>'}</p>
</section>

<section id="declarations">
  <h2>Declarations</h2>
  <p>Open an item to read its exact compact statement and source link. Detailed teaching notes are linked when registered.</p>
  <div class="declaration-list">{''.join(declarations_html) if declarations_html else '<p class="empty">This aggregator module contains imports but no indexed declaration.</p>'}</div>
</section>
"""
        toc = [("module", "Module"), ("metadata", "Module map"), ("declarations", "Declarations")]
        write_page(
            output,
            page_path,
            layout(page_path, module["name"], body, toc, "catalog", verified, generated_at),
        )


def build_learning(
    output: Path,
    chapters: list[dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    page_path = "learning/index.html"
    cards = render_book_map(page_path, chapters, detailed=True)
    learning_routes = render_learning_routes(page_path)
    textbook_spine_map = render_textbook_spine_map(page_path, SITE_TEXTBOOK_SPINE, verified)
    primary_textbook = render_primary_textbook_banner()
    body = f"""
<section class="hero" id="learning">
  <p class="eyebrow">A student-first route</p>
  <h1 class="page-title">How to read the formalization</h1>
  <p class="lede">You do not need to read thousands of declarations in source order. Begin with the deterministic language, learn the probability interfaces, then follow one algorithm route from assumptions to a compiled endpoint.</p>
  {primary_textbook}
</section>

<section id="path">
  <h2>Choose a route before choosing a chapter</h2>
  <p class="section-intro">The same finite-sum and probability leaves recur across algorithms. Pick a question, follow its short dependency route, and return to the complete map when you need a neighboring technique.</p>
  {learning_routes}
  <div class="callout"><strong>Reading rule.</strong> Read the plain-English statement first, then the mathematical reading, then the exact Lean signature. Save tactic details for the second pass.</div>
</section>

<section id="lean-translation">
  <h2>Four Lean ideas to recognize</h2>
  <div class="card-grid">
    <div class="info-card"><h3>Structures</h3><p>Bundle mathematical data with invariant proofs, such as a finite model and its best-arm certificate.</p></div>
    <div class="info-card"><h3>Typeclasses</h3><p>Supply ambient facts such as measurable spaces, finite types, probability measures, and nonempty action sets.</p></div>
    <div class="info-card"><h3>Almost everywhere</h3><p>Conditional distributions and kernel identities are usually equal almost everywhere, not pointwise.</p></div>
    <div class="info-card"><h3>Thin wrappers</h3><p>Algorithm-specific theorems should reuse general finite-sum, measure, concentration, and optimization leaves.</p></div>
  </div>
</section>

<section id="book-map">
  <p class="eyebrow">Formalized textbook map</p>
  <h2>Book map</h2>
  <p class="section-intro">The main spine is Lattimore and Szepesvári's <em>Bandit Algorithms</em>. OFUL, Tsallis-INF, and UCBVI add their original papers. Online-edition pages are shown on every chapter card; the source pages themselves explain the exact algorithms and full assumptions.</p>
  {cards}
</section>

<section id="textbook-spine">
  <p class="eyebrow">Canonical source sequence</p>
  <h2>Part IV: Lower Bounds</h2>
  <p class="section-intro">Use this separate spine when you want the exact textbook order and page mapping for Chapters 13–17. Status is per chapter and per Lean declaration.</p>
  {textbook_spine_map}
</section>
"""
    toc = [("learning", "Reading guide"), ("primary-textbook", "Primary textbook"), ("path", "Recommended path"), ("lean-translation", "Lean ideas"), ("book-map", "Book map"), ("textbook-spine", "Part IV spine")]
    write_page(
        output,
        page_path,
        layout(page_path, "Learning path", body, toc, "learning", verified, generated_at),
    )


def build_contributors(
    output: Path,
    authors: list[dict[str, Any]],
    community_contributors: list[dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    page_path = "contributors/index.html"
    author_cards = render_contributor_cards(page_path, authors, include_invitation=False)
    community_cards = render_contributor_cards(page_path, community_contributors)
    body = f"""
<section class="hero" id="contributors">
  <p class="eyebrow">Authors and community</p>
  <h1 class="page-title">People behind ABRL and BanditRLlib</h1>
  <p class="lede">Project authorship and community contribution are different records. The six paper authors are listed in paper-author order; future community contributors appear separately with their accepted work and preferred credit.</p>
</section>

<section id="authors">
  <h2>Authors</h2>
  {author_cards}
</section>

<section id="community-contributors">
  <h2>Community Contributors</h2>
  <p>A community contributor is added after a real teaching, formalization, review, or library contribution is accepted. Git commit activity is not automatically treated as paper authorship.</p>
  {community_cards}
</section>

<section id="credit-policy">
  <h2>How contribution credit works</h2>
  <div class="card-grid">
    <article class="info-card"><h3>Code and proof credit</h3><p>Lean declarations, proof repairs, tests, and module-level refactors are credited through Git history and the merged pull request.</p></article>
    <article class="info-card"><h3>Mathematical provenance</h3><p>Book, paper, and original-result sources stay attached to a lemma packet. Citing an author does not make that author an ABRL contributor or endorser.</p></article>
    <article class="info-card"><h3>Teaching and review credit</h3><p>Substantive explanations, counterexamples, assumption audits, dependency maps, and formal review are valid contributions even when they do not add a theorem.</p></article>
  </div>
  {render_diagram(page_path, 'contributors-loop.mmd', 'How authorship, lemma credit, review, and community contribution remain distinct')}
</section>

<section id="join">
  <h2>Join the contributor list</h2>
  <p>Begin with one well-scoped result or documentation improvement. Your preferred name and credit travel with the proposal, review, and eventual integrated declaration.</p>
  <div class="hero-actions"><a class="button primary" href="{href_from(page_path, 'community/index.html')}">How to contribute</a><a class="button" href="{PUBLIC_SITE_REPO}/issues/new?template=lemma-proposal.yml">Propose a lemma</a></div>
</section>
"""
    toc = [
        ("contributors", "Contributors"),
        ("authors", "Authors"),
        ("community-contributors", "Community contributors"),
        ("credit-policy", "Credit policy"),
        ("join", "Join the project"),
    ]
    write_page(
        output,
        page_path,
        layout(page_path, "Contributors", body, toc, "contributors", verified, generated_at),
    )


def build_installation(output: Path, verified: bool, generated_at: str) -> None:
    page_path = "installation/index.html"
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    body = f"""
<section class="hero" id="installation">
  <p class="eyebrow">Clone · compile · explore</p>
  <h1 class="page-title">Installation</h1>
  <p class="lede">The repository pins its Lean and Mathlib versions, so Elan and Lake can reproduce the same environment used by the formalization website and GitHub Actions.</p>
</section>

<section id="installation-path">
  <h2>Reproducible path</h2>
  {render_diagram(page_path, 'installation-path.mmd', 'Reproducible setup path for BanditRLlib, its website, and the local formalization service')}
</section>

<section id="prerequisites">
  <h2>1. Install the prerequisites</h2>
  <div class="card-grid">
    <article class="info-card"><h3>Git</h3><p>Lake uses Git to fetch Mathlib, and contributors use Git branches and pull requests for review.</p></article>
    <article class="info-card"><h3>Lean through Elan</h3><p>Follow the <a href="https://lean-lang.org/install/">official Lean installation guide</a>. Elan reads <code>lean-toolchain</code> and selects <code>{html.escape(toolchain)}</code> automatically.</p></article>
    <article class="info-card"><h3>Python 3</h3><p>The ABRL proof gate, site generator, integrity checks, and local preview helpers use Python 3 and only the standard library.</p></article>
  </div>
</section>

<section id="clone">
  <h2>2. Clone the project</h2>
  <pre class="command-block" tabindex="0" role="region" aria-label="Repository clone and dependency commands"><code>git clone {GITHUB_REPO}.git
cd Auto-Bandit-RL-Proof-In-Sleep
lake update</code></pre>
  <p><code>lake update</code> fetches the pinned Mathlib dependency from <code>lakefile.lean</code>. The first run may take several minutes.</p>
</section>

<section id="verify">
  <h2>3. Run the mandatory Lean gate</h2>
  <pre class="command-block" tabindex="0" role="region" aria-label="Mandatory Lean proof gate command"><code>python3 tools/bandit.py check</code></pre>
  <p>On Windows, <code>py -3 tools/bandit.py check</code> is equivalent when the Python launcher is installed. The gate runs <code>lake build</code>, builds <code>Tests</code>, and scans local Lean files for forbidden placeholders.</p>
  <p><strong>Successful result.</strong> The command exits with status 0 after both Lean build targets and repository integrity checks pass. A first build may be slow while Lake downloads and compiles pinned dependencies.</p>
  <div class="callout warning"><strong>Do not skip this step.</strong> A theorem is marked compiled on the website only after the project gate passes for the source snapshot being published.</div>
</section>

<section id="website">
  <h2>4. Build and preview the literate site</h2>
  <pre class="command-block" tabindex="0" role="region" aria-label="Website build and local preview commands"><code>python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
python3 -m http.server 8000 --directory website/_site</code></pre>
  <p>Open <code>http://localhost:8000/</code>. The static Research IDE is at <code>/ide/</code>; local Lean compilation requires the loopback-only companion server documented on that page.</p>
  <div class="callout"><strong>If dependency downloads fail.</strong> A transient GitHub or Mathlib CDN error is external to the proof tree. Preserve the pinned toolchain, retry after connectivity recovers, and only edit repository configuration when the failure is reproducible.</div>
</section>

<section id="first-steps">
  <h2>5. Choose your first route</h2>
  <div class="hero-actions"><a class="button primary" href="{href_from(page_path, 'learning/index.html')}">Open the book map</a><a class="button" href="{href_from(page_path, 'declarations/index.html')}">Search Lean declarations</a><a class="button" href="{href_from(page_path, 'community/index.html')}">How to contribute</a></div>
</section>
"""
    toc = [
        ("installation", "Installation"),
        ("installation-path", "Reproducible path"),
        ("prerequisites", "Prerequisites"),
        ("clone", "Clone"),
        ("verify", "Verify Lean"),
        ("website", "Build the site"),
        ("first-steps", "First route"),
    ]
    write_page(
        output,
        page_path,
        layout(page_path, "Installation", body, toc, "installation", verified, generated_at),
    )


def build_community(output: Path, verified: bool, generated_at: str) -> None:
    page_path = "community/index.html"
    body = f"""
<section class="hero" id="community">
  <p class="eyebrow">Contribute to BanditRLlib</p>
  <h1 class="page-title">Bring one theorem. Leave a reusable Lean lemma.</h1>
  <p class="lede">BanditRLlib welcomes sourced mathematics from bandits, reinforcement learning, probability, optimization, statistics, and adjacent fields. Every proposal enters the existing ABRL hierarchy, keeping provenance, meaning, Lean text, dependencies, obligations, and verification status together.</p>
  <div class="hero-actions">
    <a class="button primary" href="{PUBLIC_SITE_REPO}/issues/new?template=lemma-proposal.yml">Propose a lemma</a>
    <a class="button" href="{PUBLIC_SITE_REPO}/blob/main/CONTRIBUTING.md">Read the contribution guide</a>
    <a class="button" href="{href_from(page_path, 'ide/index.html')}">Draft in the local experimental workspace</a>
  </div>
</section>

<section id="four-steps">
  <h2>Four steps to a reviewed contribution</h2>
  <ol class="contribution-steps">
    <li><strong>Source the mathematics.</strong><span>Name the paper, book, formal proof gap, or original result and state every assumption.</span></li>
    <li><strong>Open a proposal.</strong><span>Agree on the target statement, namespace, module, and dependencies before a large implementation.</span></li>
    <li><strong>Compile and document.</strong><span>Submit Lean code, tests, plain-English meaning, mathematical notation, and proof correspondence.</span></li>
    <li><strong>Pass review and integration.</strong><span>Only the full project gate and maintainer review can mark the declaration integrated and compiled.</span></li>
  </ol>
</section>

<section id="who-can-contribute">
  <h2>Three useful contribution sizes</h2>
  <div class="card-grid contribution-levels">
    <article class="info-card"><span class="level-label">Level A</span><h3>Explain or connect</h3><p>Improve a teaching note, add a literature pointer, identify a missing assumption, or connect an existing declaration to a textbook theorem.</p></article>
    <article class="info-card"><span class="level-label">Level B</span><h3>Propose a lemma packet</h3><p>Supply a sourced mathematical statement, LaTeX, a Lean draft or signature, expected imports, and dependencies. A draft is visibly marked <em>proposed</em>.</p></article>
    <article class="info-card"><span class="level-label">Level C</span><h3>Submit a checked formalization</h3><p>Contribute a compiling Lean implementation with tests and teaching prose. Maintainers still review API placement, assumptions, attribution, and integration.</p></article>
  </div>
</section>

<section id="review-loop">
  <h2>How a lemma joins the library</h2>
  <p>A GitHub issue is enough to begin. Large formalizations should agree on scope and module ownership before substantial proof work. No proposal is displayed as compiled merely because it contains Lean-looking text.</p>
  {render_diagram(page_path, 'community-contribution-loop.mmd', 'Community contribution loop from sourced mathematics to an integrated Lean declaration')}
  <div class="status-legend community-statuses">
    <div>{status_badge('planned')}<span><strong>Proposed</strong> — sourced mathematics and a review packet exist.</span></div>
    <div>{status_badge('partial')}<span><strong>In review</strong> — statement, assumptions, namespace, or proof is being checked.</span></div>
    <div>{status_badge('compiled')}<span><strong>Lean checked</strong> — the submitted snippet compiles in the declared environment.</span></div>
    <div>{status_badge('integrated')}<span><strong>Integrated</strong> — reviewer-approved, merged into BanditRLlib on <code>main</code>, and included in a verified snapshot.</span></div>
  </div>
</section>

<section id="machine-contract">
  <h2>A stable contract for the future compiler</h2>
  <p>The community unit is a versioned JSON <strong>lemma packet</strong>. Live Formalization exports it today, including BanditRLlib reuse, Mathlib/LML candidates, semantic status, compiler status, and unresolved obligations. The packet becomes an ABRL task rather than a second proof system.</p>
  <div class="contract-grid">
    <div class="contract-copy">
      <h3>Required evidence</h3>
      <ul><li>stable contribution ID and mathematical domain;</li><li>source paper, book, or original-result provenance;</li><li>plain-English and LaTeX statements;</li><li>Lean imports, declaration text, and named dependencies;</li><li>verification status and compiler evidence;</li><li>contributor identity, preferred credit, and license agreement.</li></ul>
      <p><a href="{href_from(page_path, 'community/contribution.schema.json')}">Open the JSON Schema</a> · <a href="{href_from(page_path, 'community/registry.json')}">Open the machine-readable registry</a></p>
    </div>
    <pre class="contract-example" tabindex="0" role="region" aria-label="Example lemma packet JSON"><code>{{
  "schema_version": "1.1",
  "id": "domain-short-lemma-name",
  "status": "proposed",
  "mathematics": {{ "plain": "...", "latex": "..." }},
  "lean": {{ "imports": ["BanditRLProof"], "code": "...", "banditrl_reused": [] }},
  "provenance": {{ "source": "DOI, arXiv, book, or original" }},
  "contributor": {{ "name": "...", "credit": "..." }},
  "unresolved_proof_obligations": ["semantic review"]
}}</code></pre>
  </div>
  <div class="callout warning"><strong>Trust boundary.</strong> GitHub Pages does not execute untrusted Lean code or call a model API. Local verified mode uses a loopback-only server; only semantic review, maintainer approval, and a passed full gate can move a proposal to BanditRLlib's integrated status.</div>
</section>

<section id="community-registry" data-community-registry data-registry-url="{href_from(page_path, 'community/registry.json')}">
  <h2>Community contribution registry</h2>
  <p data-community-summary>Loading the public registry…</p>
  <div class="community-entry-grid" data-community-entries></div>
</section>

<section id="governance">
  <h2>Credit, review, and governance</h2>
  <div class="card-grid">
    <article class="info-card"><h3>Credit travels with the lemma</h3><p>Contributor name, preferred credit, source provenance, and review history remain in the packet and the eventual teaching note.</p></article>
    <article class="info-card"><h3>Assumptions stay visible</h3><p>Review may strengthen implementation details, but it must not silently weaken the mathematical target or hide a missing proof behind a theorem card.</p></article>
    <article class="info-card"><h3>Maintainers decide integration</h3><p>Public proposals are open; core-library integration follows mathematical review, namespace and API review, license checks, and the repository's Lean gate.</p></article>
  </div>
  <p><a href="{PUBLIC_SITE_REPO}/blob/main/GOVERNANCE.md">Governance</a> · <a href="{PUBLIC_SITE_REPO}/blob/main/CODE_OF_CONDUCT.md">Code of Conduct</a> · <a href="{PUBLIC_SITE_REPO}/issues">Open proposals</a></p>
</section>
"""
    toc = [
        ("community", "Community"),
        ("four-steps", "Four steps"),
        ("who-can-contribute", "Ways to contribute"),
        ("review-loop", "Review loop"),
        ("machine-contract", "Compiler contract"),
        ("community-registry", "Registry"),
        ("governance", "Governance"),
    ]
    write_page(
        output,
        page_path,
        layout(
            page_path,
            "How to contribute",
            body,
            toc,
            "community",
            verified,
            generated_at,
            extra_scripts=("static/community.js?v=20260810",),
        ),
    )


def build_source_access(output: Path, verified: bool, generated_at: str) -> None:
    page_path = "source-access/index.html"
    body = f"""
<section class="hero" id="source-access">
  <p class="eyebrow">Canonical source</p>
  <h1 class="page-title">Lean source access</h1>
  <p class="lede">BanditRLlib is built from the public canonical ABRL repository. Declaration links are pinned to source snapshot <code>{html.escape(SOURCE_BRANCH[:12])}</code>; <a href="{GITHUB_REPO}/tree/main">current <code>main</code></a> remains available separately.</p>
</section>
<section id="available">
  <h2>What is public</h2>
  <ul><li>the Lean source and exact declaration signatures;</li><li>the searchable BanditRLlib catalog and implementation map;</li><li>student-facing mathematical explanations and honest route status;</li><li>contribution issues, lemma packets, governance, and review history;</li><li>the static workspace and source code for the loopback-only local verified-mode server.</li></ul>
</section>
<section id="boundary">
  <h2>Verification and credential boundary</h2>
  <p>API keys, local editor requests, temporary compilation files, ignored build caches, and regenerable private working artifacts are never embedded in the static Pages output. GitHub Pages does not execute Lean and provides no remote compile or formalize service; the verified-mode server is a local experimental tool bound to loopback. A proposal becomes integrated only after reviewer approval and the full repository gate on <code>main</code>.</p>
  <div class="hero-actions"><a class="button primary" href="{GITHUB_REPO}">Open the canonical repository</a><a class="button" href="{href_from(page_path, 'community/index.html')}">Contribute a lemma</a></div>
</section>
"""
    write_page(
        output,
        page_path,
        layout(
            page_path,
            "Source access",
            body,
            [("source-access", "Source access"), ("available", "Public material"), ("boundary", "Security boundary")],
            "community",
            verified,
            generated_at,
        ),
    )


def build_research_ide(
    output: Path,
    highlights: list[dict[str, Any]],
    decl_by_name: dict[str, dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    page_path = "ide/index.html"
    payload = []
    for item in highlights:
        declaration = decl_by_name[item["full_name"]]
        dependencies = []
        for name in item.get("dependencies", []):
            dependency = decl_by_name[name]
            dependencies.append(
                {
                    "name": name,
                    "url": f"../modules/{dependency['module_slug']}/index.html#{dependency['anchor']}",
                }
            )
        payload.append(
            {
                "name": declaration["full_name"],
                "kind": declaration["kind"],
                "chapter": declaration["chapter_title"],
                "plain": item["plain"],
                "latex": item["math"],
                "statement": declaration["statement"],
                "module": declaration["module"],
                "file": declaration["file"],
                "line": declaration["line"],
                "url": f"../modules/{declaration['module_slug']}/index.html#{declaration['anchor']}",
                "source_url": source_url(declaration["file"], declaration["line"]),
                "dependencies": dependencies,
                "compile_source": (
                    f"import {declaration['module']}\n\n"
                    "-- Lean elaborates the declaration and prints its authoritative type.\n"
                    f"#check {declaration['full_name']}\n"
                ),
            }
        )
    write_text_lf(
        output / "ide-data.json",
        json.dumps({"items": payload}, ensure_ascii=False, separators=(",", ":")),
    )

    body = f"""
<section class="hero" id="research-ide">
  <p class="eyebrow">BanditRLlib Live Formalization</p>
  <h1 class="page-title">LaTeX, retrieval, candidate Lean, and the compiler in one workspace.</h1>
  <p class="lede">Study reviewed mappings or enter a new bandit/RL claim. Local verified mode retrieves compiled BanditRLlib declarations and Mathlib/LML cards before an optional server-side model generates candidate Lean, then sends the exact candidate to the pinned compiler.</p>
  <div class="hero-actions">
    <a class="button primary" href="#workspace">Open the workspace</a>
    <a class="button" href="{href_from(page_path, 'workflow/index.html')}">Read the verification workflow</a>
  </div>
</section>

<section id="mode-boundary">
  <h2>Two honest execution modes</h2>
  <div class="card-grid">
    <div class="info-card"><h3>Static BanditRLlib site</h3><p>LaTeX preview, reviewed math↔Lean mappings, source navigation, retrieval examples, dependency trees, and packet export work in any browser. Arbitrary code and model APIs do not run.</p></div>
    <div class="info-card"><h3>Local verified mode</h3><p><code>ide_server.py</code> binds to loopback, keeps API credentials server-side, retrieves the current library, and invokes <code>lake env lean</code> on temporary files without repository writes.</p></div>
    <div class="info-card"><h3>Honest statuses</h3><p>Candidate Translation, Lean-Compiling, Semantically Reviewed, Proof Verified, and Integrated into BanditRLlib are separate states. A compiling candidate is not automatically a faithful translation.</p></div>
  </div>
  <div class="callout warning"><strong>Security boundary.</strong> The compile endpoint is intentionally local-only. Do not forward the IDE server through a public or temporary tunnel; use the existing static sharing server for reviewers.</div>
</section>

<section id="workspace">
  <h2>Live formalization workspace</h2>
  <div class="ide-mode-banner" data-ide-mode>
    <span class="mode-dot" aria-hidden="true"></span>
    <strong data-ide-mode-title>Checking local Lean service…</strong>
    <span data-ide-mode-detail>The editor remains useful in static mode.</span>
  </div>
  <div class="ide-toolbar">
    <label class="ide-field ide-field-grow">Reviewed declaration
      <select data-ide-declaration><option value="">Loading mapped declarations…</option></select>
    </label>
    <button class="button" type="button" data-ide-load>Load verified mapping</button>
    <button class="button primary" type="button" data-ide-formalize>Formalize with BanditRLlib</button>
    <button class="button" type="button" data-ide-scaffold>Make safe draft scaffold</button>
    <button class="button" type="button" data-ide-export>Export lemma packet</button>
    <label class="ide-toggle"><input type="checkbox" data-ide-auto> Auto-compile after edits (opt-in)</label>
  </div>
  <div class="ide-grid" data-ide-app data-ide-data="{href_from(page_path, 'ide-data.json')}" data-community-url="{href_from(page_path, 'community/index.html#machine-contract')}">
    <article class="ide-pane">
      <header><div><span class="ide-step">01</span><h3>Mathematical statement</h3></div><span class="status source" data-translation-status>Reviewed mapping</span></header>
      <label for="ide-natural-language">Natural-language statement</label>
      <textarea id="ide-natural-language" data-ide-natural-language spellcheck="true" aria-label="Natural-language theorem statement"></textarea>
      <label for="ide-latex">LaTeX</label>
      <textarea id="ide-latex" data-ide-latex spellcheck="false" aria-label="Editable LaTeX statement"></textarea>
      <h4>Live rendering</h4>
      <div class="ide-math-preview" data-ide-math-preview>Choose a declaration to begin.</div>
      <p class="ide-explanation" data-ide-plain></p>
    </article>
    <article class="ide-pane">
      <header><div><span class="ide-step">02</span><h3>Lean source</h3></div><button class="button primary" type="button" data-ide-compile>Compile with Lean</button></header>
      <label for="ide-lean">Editable snippet</label>
      <textarea id="ide-lean" class="lean-editor" data-ide-lean spellcheck="false" aria-label="Editable Lean source"></textarea>
      <div class="ide-source-actions">
        <a data-ide-declaration-link href="#">Open declaration page</a>
        <a data-ide-source-link href="#">Open source line</a>
      </div>
    </article>
  </div>
  <div class="ide-output-grid">
    <article class="ide-pane diagnostics-pane">
      <header><div><span class="ide-step">03</span><h3>Compiler diagnostics</h3></div><span data-ide-duration></span></header>
      <pre class="ide-diagnostics" data-ide-diagnostics aria-live="polite">Local Lean service has not been contacted yet.</pre>
    </article>
    <article class="ide-pane dependency-pane">
      <header><div><span class="ide-step">04</span><h3>Lean dependency tree</h3></div><span data-ide-tree-summary></span></header>
      <div class="ide-tree" data-ide-tree><p class="empty">Choose a reviewed declaration to draw its teaching dependencies.</p></div>
    </article>
  </div>
  <article class="ide-pane formalization-result-pane" id="candidate-result">
    <header><div><span class="ide-step">05</span><h3>Candidate formalization record</h3></div><span data-candidate-statuses>translation: candidate · Lean: not checked · proof: unproved · library: proposed</span></header>
    <div class="formalization-result-grid">
      <section><h4>Candidate interpretation</h4><p data-candidate-interpretation>No new candidate requested.</p><h4>Candidate Lean statement</h4><pre data-candidate-statement>No new candidate requested.</pre><h4>Assumptions</h4><ul data-candidate-assumptions><li>None returned.</li></ul></section>
      <section><h4>Reused BanditRLlib declarations</h4><ul data-candidate-banditrl><li>Run local formalization to retrieve the current library.</li></ul><h4>Mathlib candidates</h4><ul data-candidate-mathlib><li>None returned.</li></ul><h4>LML candidates</h4><ul data-candidate-lml><li>None returned.</li></ul></section>
      <section><h4>Unresolved proof obligations</h4><ul data-candidate-obligations><li>Semantic review and repository integration remain required.</li></ul></section>
    </div>
  </article>
  <div class="callout contribution-export-note" data-ide-export-note><strong>Community handoff.</strong> Export produces a local JSON draft; it does not upload code or claim verification. Review the packet, add source and contributor details, then follow the <a href="{href_from(page_path, 'community/index.html')}">community contribution guide</a>.</div>
</section>

<section id="architecture">
  <h2>A narrow certificate boundary for a researcher IDE</h2>
  <p>The browser edits and visualizes; the loopback companion alone may retrieve repository evidence, call an optional provider through environment-only credentials, compile temporary Lean, and return diagnostics. The server never writes repository source. The exported packet is the integration seam into the ABRL reviewer pipeline.</p>
  {render_diagram(page_path, 'research-ide-loop.mmd', 'BanditRLlib Live Formalization: grounded candidate generation, local compilation, review obligations, and ABRL intake')}
  <div class="card-grid">
    <div class="info-card"><h3>Next: proof states</h3><p>Attach a persistent Lean language-server session so cursor position can reveal goals, hypotheses, and tactic state without recompiling a whole snippet.</p></div>
    <div class="info-card"><h3>Available: grounded candidates</h3><p>The provider-independent adapter retrieves BanditRLlib, Mathlib, and LML evidence before generation. With no provider configured, it clearly reports that formalization is unavailable.</p></div>
    <div class="info-card"><h3>Next: community submission</h3><p>Let an authenticated compiler validate a lemma packet, open a public proposal or branch, attach diagnostics, and preserve contributor credit through review.</p></div>
  </div>
</section>
"""
    toc = [
        ("research-ide", "Live Formalization"),
        ("mode-boundary", "Execution modes"),
        ("workspace", "Workspace"),
        ("candidate-result", "Candidate record"),
        ("architecture", "Architecture and next steps"),
    ]
    write_page(
        output,
        page_path,
        layout(
            page_path,
            "Live Formalization",
            body,
            toc,
            "ide",
            verified,
            generated_at,
            extra_scripts=("static/ide.js?v=20260812",),
        ),
    )


def wiki_badge(kind: str, status: str) -> str:
    label_maps = {
        "literature": WIKI_LITERATURE_STATUS_LABELS,
        "lean": WIKI_LEAN_STATUS_LABELS,
        "source": WIKI_SOURCE_STATUS_LABELS,
    }
    label = label_maps[kind].get(status, status.replace("-", " ").title())
    return (
        f'<span class="wiki-badge {html.escape(kind)} {html.escape(status)}" '
        f'data-wiki-{html.escape(kind)}-status="{html.escape(status)}">'
        f'{html.escape(label)}</span>'
    )


def wiki_case_route(case: dict[str, Any]) -> str:
    return f"banditrlwiki/cases/{case['id']}/index.html"


def validate_banditrlwiki(
    wiki: dict[str, Any],
    decl_by_name: dict[str, dict[str, Any]],
    results: list[dict[str, Any]],
) -> None:
    families = wiki.get("families", [])
    cases = wiki.get("cases", [])
    if not families or not cases:
        raise ValueError("BanditRLwiki requires nonempty families and cases")
    family_ids = [family.get("id") for family in families]
    case_ids = [case.get("id") for case in cases]
    if len(family_ids) != len(set(family_ids)):
        raise ValueError("BanditRLwiki family ids must be unique")
    if len(case_ids) != len(set(case_ids)):
        raise ValueError("BanditRLwiki case ids must be unique")
    result_ids = {result["id"] for result in results}
    leaf_ids_seen: set[str] = set()
    paper_titles_by_url: dict[str, str] = {}
    for family in families:
        if not family.get("title") or not family.get("comparison_signature"):
            raise ValueError(f"BanditRLwiki family {family.get('id')} lacks title/signature")
    for case in cases:
        case_id = case.get("id", "<missing>")
        if case.get("family") not in family_ids:
            raise ValueError(f"BanditRLwiki case {case_id} has unknown family")
        comparison = case.get("comparison", {})
        literature_status = comparison.get("status")
        if literature_status not in WIKI_LITERATURE_STATUS_LABELS:
            raise ValueError(f"BanditRLwiki case {case_id} has unknown literature status")
        lean = case.get("lean", {})
        if lean.get("status") not in WIKI_LEAN_STATUS_LABELS:
            raise ValueError(f"BanditRLwiki case {case_id} has unknown Lean status")
        if case.get("source_status") not in WIKI_SOURCE_STATUS_LABELS:
            raise ValueError(f"BanditRLwiki case {case_id} has unknown source status")
        if not case.get("signature") or not case.get("summary"):
            raise ValueError(f"BanditRLwiki case {case_id} lacks signature/summary")
        if literature_status in {"minimax-matched", "near-minimax", "asymptotic-matched"}:
            if not case.get("upper") or not case.get("lower"):
                raise ValueError(f"BanditRLwiki matched case {case_id} needs upper and lower evidence")
        frontier = case.get("frontier", {})
        if literature_status == "literature-open" and not frontier.get("literature_open"):
            raise ValueError(f"BanditRLwiki literature-open case {case_id} lacks explicit frontier flag")
        leaf_ids = frontier.get("leaf_ids", [])
        if frontier.get("formalization_open") and not leaf_ids:
            raise ValueError(f"BanditRLwiki formalization-open case {case_id} needs named leaf ids")
        for leaf_id in leaf_ids:
            if not re.fullmatch(r"[A-Z0-9][A-Z0-9-]*", leaf_id):
                raise ValueError(f"BanditRLwiki case {case_id} has malformed leaf id {leaf_id}")
            if leaf_id in leaf_ids_seen:
                raise ValueError(f"BanditRLwiki leaf id {leaf_id} is duplicated")
            leaf_ids_seen.add(leaf_id)
        for side in ("upper", "lower"):
            for result in case.get(side, []):
                required = ("paper_title", "result_title", "url", "theorem", "math", "plain")
                if not all(result.get(key) for key in required):
                    raise ValueError(f"BanditRLwiki case {case_id} has incomplete {side} evidence")
                if "title" in result:
                    raise ValueError(
                        f"BanditRLwiki case {case_id} must separate paper_title from result_title"
                    )
                if not result["url"].startswith("https://"):
                    raise ValueError(f"BanditRLwiki case {case_id} has non-HTTPS source URL")
                known_title = paper_titles_by_url.setdefault(result["url"], result["paper_title"])
                if known_title != result["paper_title"]:
                    raise ValueError(
                        f"BanditRLwiki source {result['url']} has inconsistent paper titles"
                    )
                if case.get("source_status") == "exact-source-theorem":
                    locator = result["theorem"]
                    if not re.search(r"\b(?:Theorem|Lemma|Corollary)\s+[0-9]", locator):
                        raise ValueError(
                            f"BanditRLwiki exact-source case {case_id} lacks a numbered theorem locator"
                        )
        for name in lean.get("declarations", []):
            if name not in decl_by_name:
                raise ValueError(f"BanditRLwiki case {case_id} references missing Lean declaration {name}")
        for milestone in lean.get("milestones", []):
            if milestone not in result_ids:
                raise ValueError(f"BanditRLwiki case {case_id} references missing milestone {milestone}")
        if lean.get("status") == "compiled" and not lean.get("declarations"):
            raise ValueError(f"BanditRLwiki compiled case {case_id} needs declaration evidence")


def render_wiki_bound(
    page_path: str,
    side: str,
    records: list[dict[str, Any]],
) -> str:
    if not records:
        return (
            f'<article class="wiki-bound empty-bound"><p class="panel-kicker">{html.escape(side)}</p>'
            '<h3>No source theorem claimed</h3><p>The source audit has not registered a compatible '
            'theorem for this side of the comparison.</p></article>'
        )
    rendered = []
    for record in records:
        source_meta = " · ".join(
            part for part in (
                record.get("authors", ""),
                str(record.get("year", "")),
                record.get("theorem", ""),
            )
            if part
        )
        rendered.append(
            f"""
<article class="wiki-bound">
  <p class="panel-kicker">{html.escape(side)}</p>
  <h3>{html.escape(record['result_title'])}</h3>
  <p class="wiki-paper-title">{html.escape(record['paper_title'])}</p>
  <p class="wiki-source-meta">{html.escape(source_meta)}</p>
  {render_math_statement(f"{side} guarantee", record['math'], record['plain'])}
  <p>{html.escape(record.get('scope', ''))}</p>
  <a href="{html.escape(record['url'], quote=True)}">Open primary source <span aria-hidden="true">↗</span></a>
</article>"""
        )
    return "".join(rendered)


def render_wiki_case_card(
    page_path: str,
    case: dict[str, Any],
    family: dict[str, Any],
    decl_by_name: dict[str, dict[str, Any]],
    verified: bool,
    *,
    expanded: bool = False,
) -> str:
    comparison = case["comparison"]
    lean = case["lean"]
    effective_lean = effective_evidence_status(lean["status"], verified)
    if effective_lean == "source":
        lean_badge = (
            '<span class="wiki-badge lean source" data-wiki-lean-status="source">'
            'Source only · Lean gate not run</span>'
        )
    else:
        lean_badge = wiki_badge("lean", effective_lean)
    signature = "".join(
        f'<div><dt>{html.escape(label)}</dt><dd>{html.escape(value)}</dd></div>'
        for label, value in case["signature"].items()
    )
    declarations = "".join(
        f'<li><a href="{declaration_href(page_path, decl_by_name[name])}"><code>{breakable_identifier(name)}</code></a></li>'
        for name in lean.get("declarations", [])
    )
    if not declarations:
        declarations = "<li>No local declaration is claimed for this target.</li>"
    missing = render_list(lean.get("missing", []))
    frontier = case.get("frontier", {})
    frontier_items = list(frontier.get("missing", []))
    frontier_items.extend(
        f"Named formalization leaf: {leaf}" for leaf in frontier.get("leaf_ids", [])
    )
    frontier_html = ""
    if frontier.get("literature_open") or frontier.get("formalization_open"):
        frontier_kinds = []
        if frontier.get("literature_open"):
            frontier_kinds.append("literature")
        if frontier.get("formalization_open"):
            frontier_kinds.append("formalization")
        frontier_html = f"""
<section class="wiki-frontier-note">
  <p class="panel-kicker">{html.escape(' + '.join(frontier_kinds))} frontier</p>
  <h3>{html.escape(frontier.get('question', 'Open comparison leaf'))}</h3>
  <p>{html.escape(frontier.get('closest', ''))}</p>
  {render_list(frontier_items)}
</section>"""
    case_href = href_from(page_path, wiki_case_route(case))
    open_attr = " open" if expanded else ""
    tags = "".join(f"<span>{html.escape(tag)}</span>" for tag in case.get("tags", []))
    search = " ".join(
        [
            case["id"],
            case["title"],
            case["summary"],
            family["title"],
            " ".join(case.get("tags", [])),
            comparison.get("gap", ""),
            lean.get("scope", ""),
        ]
    ).lower()
    return f"""
<details class="wiki-case-card" id="{html.escape(case['id'])}" data-wiki-case
  data-family="{html.escape(case['family'])}"
  data-literature="{html.escape(comparison['status'])}"
  data-lean="{html.escape(lean['status'])}"
  data-frontier="{str(bool(frontier.get('literature_open') or frontier.get('formalization_open'))).lower()}"
  data-search="{html.escape(search, quote=True)}"{open_attr}>
  <summary>
    <span class="wiki-case-id">{html.escape(case['id'])}</span>
    <span class="wiki-case-summary-copy"><strong>{html.escape(case['title'])}</strong><span>{html.escape(case['summary'])}</span></span>
    <span class="wiki-case-statuses">{wiki_badge('literature', comparison['status'])}{lean_badge}</span>
  </summary>
  <div class="wiki-case-body">
    <div class="wiki-case-actions"><a href="{case_href}">Open stable case page →</a><span>{wiki_badge('source', case['source_status'])}</span></div>
    <div class="wiki-tags">{tags}</div>
    <dl class="wiki-signature">{signature}</dl>
    <section class="wiki-comparison">
      <div><p class="panel-kicker">Comparison judgment</p><h3>{html.escape(WIKI_LITERATURE_STATUS_LABELS[comparison['status']])}</h3><p>{html.escape(comparison['note'])}</p><p><strong>Known gap.</strong> {html.escape(comparison.get('gap', 'No gap recorded.'))}</p></div>
      <div><p class="panel-kicker">Local Lean boundary</p><h3>{html.escape(WIKI_LEAN_STATUS_LABELS[lean['status']])}</h3><p>{html.escape(lean['scope'])}</p></div>
    </section>
    <div class="wiki-bound-grid">
      {render_wiki_bound(page_path, 'Upper bound', case.get('upper', []))}
      {render_wiki_bound(page_path, 'Lower bound', case.get('lower', []))}
    </div>
    <section class="wiki-lean-evidence">
      <div><p class="panel-kicker">Local Lean evidence</p><h3>Exact declarations</h3><ul>{declarations}</ul></div>
      <div><p class="panel-kicker">Not yet proved here</p><h3>Missing steps</h3>{missing}</div>
    </section>
    {frontier_html}
  </div>
</details>"""


def build_banditrlwiki(
    output: Path,
    wiki: dict[str, Any],
    decl_by_name: dict[str, dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> dict[str, int]:
    families = wiki["families"]
    cases = wiki["cases"]
    active_source_audits = wiki.get("active_source_audits", [])
    family_by_id = {family["id"]: family for family in families}
    cases_by_family: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for case in cases:
        cases_by_family[case["family"]].append(case)
    literature_counts = Counter(case["comparison"]["status"] for case in cases)
    lean_counts = Counter(case["lean"]["status"] for case in cases)
    literature_open = sum(1 for case in cases if case.get("frontier", {}).get("literature_open"))
    formalization_open_cases = sum(
        1 for case in cases if case.get("frontier", {}).get("formalization_open")
    )
    formalization_leaf_count = sum(
        len(case.get("frontier", {}).get("leaf_ids", []))
        for case in cases
        if case.get("frontier", {}).get("formalization_open")
    )
    exact_audits = sum(
        1 for case in cases
        if case["source_status"] in {"exact-source-theorem", "faithful-restatement"}
    )

    def render_active_source_audits(page: str) -> str:
        cards = []
        for audit in active_source_audits:
            declaration_links = "".join(
                f'<li><a href="{declaration_href(page, decl_by_name[name])}">'
                f'<code>{breakable_identifier(name)}</code></a></li>'
                for name in audit.get("representative_declarations", [])
            )
            cards.append(
                f"""
<article class="wiki-source-port-card" data-wiki-source-port id="source-port-{html.escape(audit['id'])}">
  <div class="wiki-source-port-heading"><div><p class="panel-kicker">Source-frozen external audit</p><h3>{html.escape(audit['title'])}</h3></div>{status_badge(audit['lean_status'])}</div>
  <p class="wiki-paper-title">{html.escape(audit['paper_title'])}</p>
  <p class="wiki-source-meta">{html.escape(audit['authors'])} · {html.escape(str(audit['year']))}</p>
  <p class="wiki-source-port-count"><strong>{int(audit['compiled_declaration_count'])}</strong> named declarations compile in the current library.</p>
  <p>{html.escape(audit['scope'])}</p>
  <div class="callout warning"><strong>Boundary.</strong> {html.escape(audit['boundary'])}</div>
  <details><summary>Representative Lean declarations</summary><ul>{declaration_links}</ul></details>
  <a href="{html.escape(audit['url'], quote=True)}">Open official proceedings source ↗</a>
</article>"""
            )
        return "".join(cards)

    page_path = "banditrlwiki/index.html"
    family_cards = "".join(
        f"""
<a class="wiki-family-card" href="{href_from(page_path, f"banditrlwiki/settings/{family['id']}/index.html")}">
  <span class="wiki-family-count">{len(cases_by_family[family['id']])} {'case' if len(cases_by_family[family['id']]) == 1 else 'cases'}</span>
  <h3>{html.escape(family['title'])}</h3>
  <p>{html.escape(family['summary'])}</p>
  <span>Open setting →</span>
</a>"""
        for family in families
    )
    family_options = "".join(
        f'<option value="{html.escape(family["id"])}">{html.escape(family["title"])}</option>'
        for family in families
    )
    literature_options = "".join(
        f'<option value="{status}">{html.escape(label)}</option>'
        for status, label in WIKI_LITERATURE_STATUS_LABELS.items()
    )
    lean_options = "".join(
        f'<option value="{status}">{html.escape(label)}</option>'
        for status, label in WIKI_LEAN_STATUS_LABELS.items()
    )
    case_cards = "".join(
        render_wiki_case_card(page_path, case, family_by_id[case["family"]], decl_by_name, verified)
        for case in cases
    )
    source_port_cards = render_active_source_audits(page_path)
    body = f"""
<section class="hero wiki-hero" id="overview">
  <p class="eyebrow">Assumption-indexed research atlas</p>
  <h1>BanditRLwiki</h1>
  <p class="lede">Compare published upper and lower bounds only under compatible assumptions, then inspect what BanditRLlib has—and has not—compiled for the same route.</p>
  <p><strong>Published optimality, theorem-level source audit, and local Lean compilation are separate ledgers.</strong></p>
  <div class="hero-actions"><a class="button primary" href="{href_from(page_path, 'banditrlwiki/frontier/index.html')}">Open frontier leaves</a><a class="button" href="{href_from(page_path, 'banditrlwiki/papers/index.html')}">Browse paper index</a><a class="button" href="{href_from(page_path, 'banditrlwiki/progress/index.html')}">Audit progress</a></div>
  <div class="stats-grid wiki-stats">
    <div class="stat"><span class="stat-value">{len(families)}</span><span class="stat-label">assumption families</span></div>
    <div class="stat"><span class="stat-value">{len(cases)}</span><span class="stat-label">comparison cases</span></div>
    <div class="stat"><span class="stat-value">{exact_audits}</span><span class="stat-label">exact or faithful source audits</span></div>
    <div class="stat"><span class="stat-value">{literature_open}</span><span class="stat-label">explicit literature-open leaves</span></div>
    <div class="stat"><span class="stat-value">{len(active_source_audits)}</span><span class="stat-label">active source-frozen ports outside the comparison atlas</span></div>
  </div>
</section>
<section id="reading-contract">
  <h2>Read three statuses, never one blended badge</h2>
  <div class="wiki-status-contract">
    <article><p class="panel-kicker">Literature</p><h3>Is the rate matched?</h3><p>Upper and lower results are compared only after fixing problem class, feedback, horizon, regret notion, probability mode, and salient parameters.</p></article>
    <article><p class="panel-kicker">Source audit</p><h3>How precisely was it checked?</h3><p>An exact theorem audit is different from a normalized rate comparison or a primary reference that still needs theorem-level review.</p></article>
    <article><p class="panel-kicker">Lean</p><h3>What compiles locally?</h3><p>A compiled dependency or algorithm route is not automatically the paper theorem or a minimax terminal.</p></article>
  </div>
  <div class="callout warning"><strong>Open does not mean missing from this list.</strong> “Literature open” appears only after an explicit source audit. “Source audit pending” and “Lean blocked” are separate states.</div>
</section>
<section id="settings">
  <p class="eyebrow">Start from assumptions</p><h2>Setting atlas</h2>
  <div class="wiki-family-grid">{family_cards}</div>
</section>
<section id="source-ports">
  <p class="eyebrow">Latest repository progress</p><h2>Active source ports awaiting a matched-bound case</h2>
  <p>These audits expose real compiled progress, but they are not counted among the 13 upper/lower comparison cases until a theorem-level rate contract and a compatible comparison partner are frozen.</p>
  <div class="wiki-source-port-grid">{source_port_cards}</div>
</section>
<section id="cases" data-wiki>
  <p class="eyebrow">Upper · lower · Lean</p><h2>All comparison cases</h2>
  <div class="wiki-filter-bar">
    <div class="filter-field grow"><label for="wiki-query">Algorithm, paper, assumption, or case</label><input id="wiki-query" data-wiki-query type="search" placeholder="e.g. KL-UCB, high probability, Chapter 16"></div>
    <div class="filter-field"><label for="wiki-family">Family</label><select id="wiki-family" data-wiki-family><option value="">All families</option>{family_options}</select></div>
    <div class="filter-field"><label for="wiki-literature">Literature</label><select id="wiki-literature" data-wiki-literature><option value="">All literature states</option>{literature_options}</select></div>
    <div class="filter-field"><label for="wiki-lean">Lean</label><select id="wiki-lean" data-wiki-lean><option value="">All Lean states</option>{lean_options}</select></div>
    <label class="wiki-check"><input type="checkbox" data-wiki-frontier> Frontier only</label>
  </div>
  <div class="wiki-filter-status"><span data-wiki-count>{len(cases)} matching cases</span><span><button type="button" data-wiki-expand>Expand visible</button><button type="button" data-wiki-collapse>Collapse all</button></span></div>
  <div class="wiki-case-list">{case_cards}</div>
</section>"""
    toc = [("overview", "Overview"), ("reading-contract", "Status contract"), ("settings", "Settings"), ("source-ports", "Source ports"), ("cases", "Cases")]
    write_page(
        output,
        page_path,
        layout(
            page_path, "BanditRLwiki", body, toc, "banditrlwiki", verified, generated_at,
            extra_scripts=("static/banditrlwiki.js",), wide=True,
        ),
    )

    for family in families:
        family_page = f"banditrlwiki/settings/{family['id']}/index.html"
        signature = "".join(
            f"<li><strong>{html.escape(item['label'])}.</strong> {html.escape(item['value'])}</li>"
            for item in family["comparison_signature"]
        )
        cards = "".join(
            render_wiki_case_card(family_page, case, family, decl_by_name, verified, expanded=True)
            for case in cases_by_family[family["id"]]
        )
        family_body = f"""
<section class="hero wiki-hero" id="setting"><p class="eyebrow">BanditRLwiki setting</p><h1>{html.escape(family['title'])}</h1><p class="lede">{html.escape(family['summary'])}</p><p><a href="{href_from(family_page, 'banditrlwiki/index.html')}">← All settings</a></p></section>
<section id="signature"><h2>Comparison signature</h2><ul class="wiki-signature-list">{signature}</ul><div class="callout"><strong>Matching rule.</strong> A rate is called matched only when the upper and lower theorem contracts agree on the fields above; every remaining mismatch is named in the case.</div></section>
<section id="setting-cases"><h2>{len(cases_by_family[family['id']])} cases</h2><div class="wiki-case-list">{cards}</div></section>"""
        write_page(
            output,
            family_page,
            layout(family_page, family["title"], family_body, [("setting", "Setting"), ("signature", "Signature"), ("setting-cases", "Cases")], "banditrlwiki", verified, generated_at),
        )

    for case in cases:
        case_page = wiki_case_route(case)
        family = family_by_id[case["family"]]
        body = f"""
<section class="hero wiki-case-hero" id="case"><p class="eyebrow">BanditRLwiki case · {html.escape(case['id'])}</p><h1>{html.escape(case['title'])}</h1><p class="lede">{html.escape(case['summary'])}</p><p><a href="{href_from(case_page, f"banditrlwiki/settings/{family['id']}/index.html")}">← {html.escape(family['title'])}</a></p></section>
<section id="comparison"><h2>Audited comparison</h2>{render_wiki_case_card(case_page, case, family, decl_by_name, verified, expanded=True)}</section>
<section id="contribute"><h2>Improve this case</h2><p>Corrections should preserve the comparison signature and cite a primary theorem, theorem number, source edition, and exact gap being closed. Lean contributions should target one named missing leaf without weakening the mathematical contract.</p><a class="button" href="{GITHUB_REPO}/issues/new?template=lemma-proposal.yml">Propose a sourced update</a></section>"""
        write_page(
            output,
            case_page,
            layout(case_page, case["title"], body, [("case", "Case"), ("comparison", "Comparison"), ("contribute", "Contribute")], "banditrlwiki", verified, generated_at),
        )

    frontier_page = "banditrlwiki/frontier/index.html"
    literature_frontier = [case for case in cases if case.get("frontier", {}).get("literature_open")]
    source_audit_queue = [
        case for case in cases if case["comparison"]["status"] == "source-audit-pending"
    ]
    formalization_frontier = [case for case in cases if case.get("frontier", {}).get("formalization_open")]

    def frontier_leaf_ids(case: dict[str, Any], kind: str) -> str:
        rendered = []
        for leaf_id in case["frontier"].get("leaf_ids", []):
            canonical_id = f"leaf-{slugify(leaf_id)}"
            if kind == "formalization":
                rendered.append(
                    f'<li class="frontier-named-leaf" data-frontier-leaf '
                    f'id="{html.escape(canonical_id)}"><code>{html.escape(leaf_id)}</code></li>'
                )
            elif case["frontier"].get("formalization_open"):
                rendered.append(
                    f'<li class="frontier-related-leaf"><a href="#{html.escape(canonical_id)}">'
                    f'<code>{html.escape(leaf_id)}</code></a></li>'
                )
            else:
                rendered.append(
                    f'<li class="frontier-related-leaf"><code>{html.escape(leaf_id)}</code></li>'
                )
        if not rendered:
            return '<p class="empty">No named leaf id is registered for this case.</p>'
        label = "Named formalization leaves" if kind == "formalization" else "Related named obligations"
        return (
            f'<p class="frontier-leaf-label">{html.escape(label)}</p>'
            f'<ul class="frontier-leaf-id-list">{"".join(rendered)}</ul>'
        )

    def frontier_cards(frontier_cases: list[dict[str, Any]], kind: str) -> str:
        if not frontier_cases:
            return '<p class="empty">No explicitly audited open leaf is registered.</p>'
        return "".join(
            f"""
<details class="frontier-case-card" data-frontier-case id="{html.escape(kind + '-' + case['id'])}">
  <summary><span>{html.escape(case['id'])}</span><strong>{html.escape(case['frontier']['question'])}</strong>{wiki_badge('literature' if kind == 'literature' else 'lean', case['comparison']['status'] if kind == 'literature' else case['lean']['status'])}</summary>
  <div><p>{html.escape(case['frontier'].get('closest', ''))}</p>{frontier_leaf_ids(case, kind)}{render_list(case['frontier'].get('missing', []))}<p><a href="{href_from(frontier_page, wiki_case_route(case))}">Inspect upper, lower, assumptions, and Lean evidence →</a></p></div>
</details>"""
            for case in frontier_cases
        )
    frontier_body = f"""
<section class="hero wiki-hero" id="frontier"><p class="eyebrow">Unclosed leaves, with the reason visible</p><h1>BanditRLwiki Frontier</h1><p class="lede">A mathematical literature gap is not the same as a missing source audit or a local Lean proof gap. This page keeps all three boundaries explicit.</p><div class="stats-grid wiki-stats"><div class="stat"><span class="stat-value">{len(literature_frontier)}</span><span class="stat-label">literature-open cases</span></div><div class="stat"><span class="stat-value">{formalization_leaf_count}</span><span class="stat-label">named formalization leaves</span></div><div class="stat"><span class="stat-value">{len(source_audit_queue)}</span><span class="stat-label">source-audit cases</span></div><div class="stat"><span class="stat-value">{len(formalization_frontier)}</span><span class="stat-label">formalization-open cases</span></div></div></section>
<section id="literature-frontier"><h2>Literature-open cases</h2><p>These are explicit negative findings from the scoped primary-source audit. A missing database entry is never enough to place a case here.</p>{frontier_cards(literature_frontier, 'literature')}</section>
<section id="source-audit-queue"><h2>Source-audit queue</h2><p>These cases have a strong closest result, but a compatible primary upper/lower theorem pair has not yet been frozen. They are not labeled literature-open.</p>{frontier_cards(source_audit_queue, 'literature')}</section>
<section id="formalization-frontier"><h2>Formalization frontier</h2><p>The mathematics may already be known, but the exact paper theorem or its required semantic bridge is not compiled in BanditRLlib.</p>{frontier_cards(formalization_frontier, 'formalization')}</section>
<section id="active-source-ports"><h2>Active source ports outside the comparison atlas</h2><p>These two NeurIPS 2025 ports record current compiled progress and exact nonclaims. One now contains a narrowly scoped compiled paper endpoint, while both remain partial audits and remain outside the minimax ledger until their remaining contracts and compatible comparison partners are frozen.</p><div class="wiki-source-port-grid">{render_active_source_audits(frontier_page)}</div></section>
<section id="rules"><h2>How a leaf closes</h2><ol class="contribution-steps"><li><strong>Freeze the contract.</strong><span>Fix assumptions, regret notion, quantifiers, constants, and source location.</span></li><li><strong>Audit primary evidence.</strong><span>Record the closest compatible upper and lower theorem; name every mismatch.</span></li><li><strong>Compile the exact bridge.</strong><span>Close one named proof obligation without adding an unadvertised assumption.</span></li><li><strong>Pass independent gates.</strong><span>Lean, tests, website links, source review, and deployment evidence must agree before status promotion.</span></li></ol></section>"""
    write_page(
        output,
        frontier_page,
        layout(
            frontier_page,
            "BanditRLwiki Frontier",
            frontier_body,
            [("frontier", "Overview"), ("literature-frontier", "Literature"), ("source-audit-queue", "Audit queue"), ("formalization-frontier", "Formalization"), ("active-source-ports", "Source ports"), ("rules", "Closure rule")],
            "banditrlwiki-frontier",
            verified,
            generated_at,
            extra_scripts=("static/banditrlwiki.js",),
        ),
    )

    paper_page = "banditrlwiki/papers/index.html"
    papers: dict[str, dict[str, Any]] = {}
    theorem_surface_count = 0
    paper_case_pairs: set[tuple[str, str]] = set()
    for case in cases:
        for side in ("upper", "lower"):
            for record in case.get(side, []):
                key = record["url"]
                paper = papers.setdefault(
                    key,
                    {
                        "paper_title": record["paper_title"],
                        "authors": record.get("authors", ""),
                        "year": record.get("year", ""),
                        "records": [],
                        "cases": {},
                    },
                )
                paper["records"].append(
                    {
                        "side": side,
                        "result_title": record["result_title"],
                        "theorem": record["theorem"],
                        "case_id": case["id"],
                    }
                )
                paper["cases"][case["id"]] = case
                theorem_surface_count += 1
                paper_case_pairs.add((key, case["id"]))
    paper_cards = "".join(
        f"""
<article class="wiki-paper-card" data-wiki-paper>
  <p class="panel-kicker">Primary paper · {len(paper['records'])} theorem {'surface' if len(paper['records']) == 1 else 'surfaces'}</p>
  <h3>{html.escape(paper['paper_title'])}</h3>
  <p>{html.escape(paper.get('authors', ''))} · {html.escape(str(paper.get('year', '')))}</p>
  <h4>Theorem surfaces</h4>
  <ul class="wiki-theorem-surface-list">{''.join(f'<li class="wiki-theorem-surface" data-wiki-theorem-surface><span>{html.escape(record["side"].title())}</span><strong>{html.escape(record["result_title"])}</strong><small>{html.escape(record["theorem"])} · <code>{html.escape(record["case_id"])}</code></small></li>' for record in paper['records'])}</ul>
  <h4>Indexed cases</h4>
  <ul class="wiki-paper-case-list">{''.join(f'<li><a class="wiki-paper-case-link" data-wiki-paper-case-link href="{href_from(paper_page, wiki_case_route(case))}">{html.escape(case["title"])}</a></li>' for case in paper['cases'].values())}</ul>
  <a href="{html.escape(url, quote=True)}">Primary source ↗</a>
</article>"""
        for url, paper in sorted(
            papers.items(), key=lambda item: (str(item[1].get("year", "")), item[1]["paper_title"])
        )
    )
    paper_body = f"""
<section class="hero wiki-hero" id="papers"><p class="eyebrow">Primary-source theorem index</p><h1>BanditRLwiki Papers</h1><p class="lede">{len(papers)} primary papers expose {theorem_surface_count} indexed theorem surfaces across {len(cases)} assumption-compatible comparison cases.</p></section>
<section id="audit-boundary"><h2>Audit boundary</h2><p>Links point to primary papers, proceedings pages, DOIs, or the author-hosted textbook. Rate summaries are independently written comparison statements; source prose, templates, and data are not copied.</p></section>
<section id="paper-index"><h2>Sources and indexed cases</h2><div class="wiki-paper-grid">{paper_cards}</div></section>"""
    write_page(
        output,
        paper_page,
        layout(paper_page, "BanditRLwiki Papers", paper_body, [("papers", "Overview"), ("audit-boundary", "Audit boundary"), ("paper-index", "Paper index")], "banditrlwiki-papers", verified, generated_at),
    )

    progress_page = "banditrlwiki/progress/index.html"
    progress_groups = "".join(
        f"""
<details class="wiki-progress-family"><summary><strong>{html.escape(family['title'])}</strong><span>{len(cases_by_family[family['id']])} cases</span></summary>
  <div>{''.join(f'<p><a href="{href_from(progress_page, wiki_case_route(case))}">{html.escape(case["id"])}</a> {wiki_badge("literature", case["comparison"]["status"])} {wiki_badge("lean", case["lean"]["status"])}</p>' for case in cases_by_family[family['id']])}</div>
</details>"""
        for family in families
    )
    progress_body = f"""
<section class="hero wiki-hero" id="progress"><p class="eyebrow">Two independent ledgers</p><h1>BanditRLwiki Progress</h1><p class="lede">Source coverage and Lean completion are counted separately; neither percentage estimates how much of all bandit or reinforcement-learning theory is complete.</p></section>
<section id="literature-progress"><h2>Literature comparison ledger</h2><div class="wiki-ledger-grid">{''.join(f'<article><strong>{count}</strong><span>{html.escape(WIKI_LITERATURE_STATUS_LABELS[status])}</span></article>' for status, count in literature_counts.items())}</div></section>
<section id="lean-progress"><h2>Local Lean evidence ledger</h2><div class="wiki-ledger-grid">{''.join(f'<article><strong>{count}</strong><span>{html.escape(WIKI_LEAN_STATUS_LABELS[status])}</span></article>' for status, count in lean_counts.items())}</div></section>
<section id="family-progress"><h2>By assumption family</h2>{progress_groups}</section>"""
    write_page(
        output,
        progress_page,
        layout(progress_page, "BanditRLwiki Progress", progress_body, [("progress", "Overview"), ("literature-progress", "Literature"), ("lean-progress", "Lean"), ("family-progress", "Families")], "banditrlwiki-progress", verified, generated_at),
    )
    return {
        "family_count": len(families),
        "case_count": len(cases),
        "paper_count": len(papers),
        "theorem_surface_count": theorem_surface_count,
        "paper_case_link_count": len(paper_case_pairs),
        "exact_source_audit_count": exact_audits,
        "literature_open_count": literature_open,
        "formalization_open_case_count": formalization_open_cases,
        "formalization_leaf_count": formalization_leaf_count,
        "active_source_audit_count": len(active_source_audits),
    }


def build_roadmap(
    output: Path,
    results: list[dict[str, Any]],
    roadmap: dict[str, Any],
    decl_by_name: dict[str, dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    page_path = "roadmap/index.html"
    status_counts = Counter(result["status"] for result in results)
    ledger = []
    for status in ("compiled", "partial", "stated", "planned", "blocked"):
        for result in (item for item in results if item["status"] == status):
            links = [
                f'<a href="{declaration_href(page_path, decl_by_name[name])}"><code>{html.escape(name)}</code></a>'
                for name in result["declarations"]
            ]
            ledger.append(
                f"""
<article class="status-entry {status}" id="{slugify(result['id'])}">
  {status_badge(status)}
  <h3>{html.escape(result['title'])}</h3>
  <p>{html.escape(result['informal'])}</p>
  <p><strong>Lean:</strong> {' · '.join(links) if links else 'No local declaration yet.'}</p>
  <p><strong>Remaining:</strong> {html.escape(' '.join(result['missing'])) if result['missing'] else 'No missing step recorded for this milestone.'}</p>
  <p><strong>Evidence:</strong> <code>{html.escape(result['evidence'])}</code></p>
</article>"""
            )
    route_rows = []
    for route in roadmap.get("routes", []):
        route_rows.append(
            f"""
<tr>
  <td><code>{html.escape(route['id'])}</code><br>{html.escape(route['title'])}</td>
  <td>{html.escape(route['priority'])}</td>
  <td>{html.escape(' · '.join(route.get('compiled_local_core', [])))}</td>
  <td>{html.escape(' · '.join(route.get('next_mathlib_ready_leaves', [])))}</td>
</tr>"""
        )
    body = f"""
<section class="hero" id="roadmap">
  <p class="eyebrow">Compiled endpoints and named gaps</p>
  <h1 class="page-title">Progress and roadmap</h1>
  <p class="lede">Progress means a declaration compiled under its exact hypotheses. Route completion means the advertised mathematical target is reached. These are tracked separately.</p>
</section>

<section id="progress">
  <h2>Mapped milestone status</h2>
  {render_diagram(page_path, 'progress.mmd', 'Status counts for the explicit website milestones', status_counts)}
  <p>The count is auditable in <code>website/content/results.json</code>. It is not an estimate of the percentage of the field completed.</p>
</section>

<section id="ledger">
  <h2>Milestone ledger</h2>
  <div class="status-ledger">{''.join(ledger)}</div>
</section>

<section id="route-registry">
  <h2>Machine route registry</h2>
  <div class="callout warning"><strong>Historical planning layer.</strong> The machine route registry is displayed as planning evidence. Some narrative <em>compiled_local_core</em> fields lag newer Lean files; the generated declaration catalog and milestone ledger above take precedence for current local code.</div>
  <div class="table-wrap"><table><thead><tr><th>Route</th><th>Priority</th><th>Registry's compiled core summary</th><th>Next registered leaves</th></tr></thead><tbody>{''.join(route_rows)}</tbody></table></div>
</section>
"""
    toc = [("roadmap", "Roadmap"), ("progress", "Progress"), ("ledger", "Milestone ledger"), ("route-registry", "Route registry")]
    write_page(
        output,
        page_path,
        layout(page_path, "Progress and roadmap", body, toc, "roadmap", verified, generated_at),
    )


def build_lean_graph(
    output: Path,
    modules: list[dict[str, Any]],
    declarations: list[dict[str, Any]],
    chapters: list[dict[str, Any]],
    highlights: list[dict[str, Any]],
    results: list[dict[str, Any]],
    textbook_spine: dict[str, Any],
    proof_graph_report: dict[str, Any],
    novelty_audit: dict[str, Any],
    verified: bool,
    generated_at: str,
) -> dict[str, int]:
    """Build a progressive-disclosure navigation graph from current site evidence.

    This browser graph intentionally does not serialize the frozen environment
    graph's hundreds of thousands of direct constant-occurrence edges.  It
    combines exhaustive source containment and module imports with reviewed
    teaching, milestone, and textbook-spine relations.  Exact environment
    observations remain on the separate Proof Graph Laboratory page.
    """

    page_path = "lean-graph/index.html"
    nodes: dict[str, dict[str, Any]] = {}
    edges: list[dict[str, str]] = []
    edge_keys: set[tuple[str, str, str]] = set()

    def compact(value: str, limit: int = 420) -> str:
        value = re.sub(r"\s+", " ", value or "").strip()
        return value if len(value) <= limit else value[: limit - 1].rstrip() + "…"

    def add_node(
        node_id: str,
        label: str,
        kind: str,
        status: str,
        *,
        subtitle: str = "",
        description: str = "",
        url: str = "",
        parent: str = "",
        order: int = 0,
        meta: list[list[str]] | None = None,
        statement: str = "",
        missing: list[str] | None = None,
    ) -> None:
        nodes[node_id] = {
            "id": node_id,
            "label": label,
            "kind": kind,
            "status": status,
            "subtitle": subtitle,
            "description": compact(description),
            "url": url,
            "parent": parent,
            "order": order,
            "meta": meta or [],
            "statement": compact(statement, 900),
            "missing": missing or [],
            "search": compact(f"{label} {subtitle} {description} {kind} {status}", 1400).lower(),
        }

    def add_edge(source: str, target: str, relation: str) -> None:
        key = (source, target, relation)
        if source == target or key in edge_keys or source not in nodes or target not in nodes:
            return
        edge_keys.add(key)
        edges.append({"source": source, "target": target, "relation": relation})

    module_counts = Counter(module["chapter"] for module in modules)
    declaration_counts = Counter(decl["chapter"] for decl in declarations)
    result_counts = Counter(result["chapter"] for result in results)
    status_counts = Counter(result["status"] for result in results)
    benchmark_counts = proof_graph_report["graph"]["counts"]

    root_id = "library:banditrl"
    book_group = "group:book-map"
    spine_group = "group:textbook-spine"
    milestone_group = "group:milestones"
    laboratory_group = "group:proof-laboratory"
    add_node(
        root_id,
        LIBRARY_NAME,
        "library",
        "compiled" if verified else "source",
        subtitle="Lean 4 library for bandit and reinforcement-learning theory",
        description=(
            "The public, searchable library produced by ABRL. Expand one branch at a time "
            "to move from teaching chapters to modules, exact declarations, and reviewed routes."
        ),
        url="../index.html",
        meta=[
            ["Lean modules", f"{len(modules):,}"],
            ["Indexed declarations", f"{len(declarations):,}"],
            ["Mapped milestones", f"{len(results):,}"],
        ],
    )
    add_node(
        book_group,
        "Book Map",
        "curriculum",
        "partial",
        subtitle=f"{len(chapters)} teaching chapters",
        description="The student-facing route from foundations and concentration to bandit algorithms and finite-horizon RL.",
        url="../learning/index.html",
        parent=root_id,
        order=1,
        meta=[["Chapters", str(len(chapters))], ["Mapped declarations", f"{len(declarations):,}"]],
    )
    add_node(
        spine_group,
        "Part IV lower-bound spine",
        "textbook spine",
        "partial",
        subtitle=f"Chapters 13–17 · {len(textbook_spine['chapters'])} source chapters",
        description="A separate, source-faithful lower-bound spine. Whole-chapter status remains partial even when a named source terminal compiles.",
        url="../textbook-spine/index.html",
        parent=root_id,
        order=2,
        meta=[["Source chapters", str(len(textbook_spine["chapters"]))]],
    )
    add_node(
        milestone_group,
        "Implementation milestones",
        "milestone map",
        "partial",
        subtitle=f"{len(results)} exact route contracts",
        description="Reviewed mathematical routes with independent compiled, partial, planned, and blocked status.",
        url="../implementation-map/index.html",
        parent=root_id,
        order=3,
        meta=[
            ["Compiled", str(status_counts.get("compiled", 0))],
            ["Partial", str(status_counts.get("partial", 0))],
            ["Blocked", str(status_counts.get("blocked", 0))],
            ["Planned", str(status_counts.get("planned", 0))],
        ],
    )
    add_node(
        laboratory_group,
        "Proof Graph Laboratory",
        "research laboratory",
        "prototype",
        subtitle="Frozen environment graph and proof-structure prototypes",
        description=(
            "A separate evidence page for compiled-environment dependency counts, fixed benchmark supports, "
            "ZDD/hypergraph prototypes, and the partial Curvature–Noise–Gap candidate."
        ),
        url="../proof-graph-laboratory/index.html",
        parent=root_id,
        order=4,
        meta=[
            ["Frozen project nodes", f"{benchmark_counts['project_nodes']:,}"],
            ["Frozen direct edges", f"{benchmark_counts['edges']:,}"],
            ["Benchmark roots", str(proof_graph_report["benchmark_contract"]["root_count"])],
            ["CNG status", novelty_audit["cng_candidate"]["status"]],
        ],
    )

    chapter_ids: dict[str, str] = {}
    for index, chapter in enumerate(chapters, start=1):
        node_id = f"chapter:{chapter['slug']}"
        chapter_ids[chapter["slug"]] = node_id
        add_node(
            node_id,
            f"{index:02d} · {chapter['short_title']}",
            "book chapter",
            chapter["status"],
            subtitle=chapter["title"],
            description=chapter["summary"],
            url=f"../chapters/{chapter['slug']}/index.html",
            parent=book_group,
            order=index,
            meta=[
                ["Lean modules", f"{module_counts[chapter['slug']]:,}"],
                ["Declarations", f"{declaration_counts[chapter['slug']]:,}"],
                ["Milestones", f"{result_counts[chapter['slug']]:,}"],
            ],
            missing=chapter.get("open_gaps", []),
        )

    module_ids: dict[str, str] = {}
    for order, module in enumerate(modules):
        node_id = f"module:{module['name']}"
        module_ids[module["name"]] = node_id
        module_status = "stated" if module["placeholder_count"] else ("compiled" if verified else "source")
        short_name = module["name"]
        if short_name.startswith("BanditRLProof."):
            short_name = short_name[len("BanditRLProof.") :]
        add_node(
            node_id,
            short_name,
            "Lean module",
            module_status,
            subtitle=module["name"],
            description=module["summary"] or f"Generated source map for {module['file']}.",
            url=f"../modules/{module['slug']}/index.html",
            parent=chapter_ids[module["chapter"]],
            order=order,
            meta=[
                ["Source", module["file"]],
                ["Declarations", f"{len(module['declarations']):,}"],
                ["Project imports", f"{len(module['imports']):,}"],
                ["Teaching chapter", module["chapter_title"]],
            ],
        )

    declaration_ids: dict[str, str] = {}
    for order, declaration in enumerate(declarations):
        node_id = f"declaration:{declaration['full_name']}"
        declaration_ids[declaration["full_name"]] = node_id
        declaration_status = (
            "stated"
            if declaration["placeholder"] or declaration["kind"] == "axiom"
            else ("compiled" if verified else "source")
        )
        add_node(
            node_id,
            declaration["full_name"].rsplit(".", 1)[-1],
            KIND_LABELS.get(declaration["kind"], declaration["kind"]),
            declaration_status,
            subtitle=declaration["full_name"],
            description=declaration["docstring"] or declaration["statement"],
            url=f"../modules/{declaration['module_slug']}/index.html#{declaration['anchor']}",
            parent=module_ids[declaration["module"]],
            order=order,
            meta=[
                ["Kind", KIND_LABELS.get(declaration["kind"], declaration["kind"])],
                ["Module", declaration["module"]],
                ["Source", f"{declaration['file']}:{declaration['line']}"],
                ["Chapter", declaration["chapter_title"]],
            ],
            statement=declaration["statement"],
        )

    result_ids: dict[str, str] = {}
    for order, result in enumerate(results):
        node_id = f"milestone:{result['id']}"
        result_ids[result["id"]] = node_id
        add_node(
            node_id,
            result["title"],
            "mathematical milestone",
            result["status"],
            subtitle=result["id"],
            description=result["informal"],
            url=f"../implementation-map/index.html#{slugify(result['id'])}",
            parent=milestone_group,
            order=order,
            meta=[
                ["Book Map chapter", result["chapter"]],
                ["Lean declarations", str(len(result["declarations"]))],
                ["Prerequisite milestones", str(len(result.get("depends_on", [])))],
            ],
            missing=result.get("missing", []),
        )

    spine_ids: dict[str, str] = {}
    for order, chapter in enumerate(textbook_spine["chapters"]):
        node_id = f"spine:{chapter['number']}"
        spine_ids[chapter["slug"]] = node_id
        source_theorem = chapter["source_theorem"]
        add_node(
            node_id,
            f"Chapter {chapter['number']} · {chapter['title']}",
            "source chapter",
            chapter["status"],
            subtitle=source_theorem["label"],
            description=chapter["status_note"],
            url=f"../textbook-spine/{chapter['slug']}/index.html",
            parent=spine_group,
            order=order,
            meta=[
                ["Whole-chapter status", chapter["status"]],
                ["Source theorem", source_theorem["status"]],
                ["Lean correspondences", str(len(chapter["lean_correspondence"]))],
                ["Open gaps", str(len(chapter["gaps"]))],
            ],
            missing=chapter["gaps"],
        )

    # Containment edges power progressive expansion and are intentionally
    # distinct from prerequisite-to-consumer proof and import edges.
    for node in nodes.values():
        if node["parent"]:
            add_edge(node["parent"], node["id"], "contains")

    for previous, current in zip(chapters, chapters[1:]):
        add_edge(chapter_ids[previous["slug"]], chapter_ids[current["slug"]], "teaching order")
    spine_chapters = textbook_spine["chapters"]
    for previous, current in zip(spine_chapters, spine_chapters[1:]):
        add_edge(spine_ids[previous["slug"]], spine_ids[current["slug"]], "source order")

    for module in modules:
        consumer = module_ids[module["name"]]
        for imported in module["imports"]:
            prerequisite = module_ids.get(imported)
            if prerequisite:
                add_edge(prerequisite, consumer, "imports")

    for highlight in highlights:
        consumer = declaration_ids.get(highlight["full_name"])
        if not consumer:
            continue
        for dependency in highlight.get("dependencies", []):
            prerequisite = declaration_ids.get(dependency)
            if prerequisite:
                add_edge(prerequisite, consumer, "teaching prerequisite")

    for result in results:
        result_node = result_ids[result["id"]]
        for declaration_name in result["declarations"]:
            declaration_node = declaration_ids.get(declaration_name)
            if declaration_node:
                add_edge(declaration_node, result_node, "certifies")
        for dependency in result.get("depends_on", []):
            prerequisite = result_ids.get(dependency)
            if prerequisite:
                add_edge(prerequisite, result_node, "milestone prerequisite")

    for chapter in spine_chapters:
        spine_node = spine_ids[chapter["slug"]]
        for correspondence in chapter["lean_correspondence"]:
            declaration_node = declaration_ids.get(correspondence["name"])
            if declaration_node:
                add_edge(declaration_node, spine_node, "maps to source")

    for benchmark in proof_graph_report["benchmarks"]:
        root_node = declaration_ids.get(benchmark["root"])
        if root_node:
            add_edge(root_node, laboratory_group, "benchmarked in")
    for declaration_name in novelty_audit["cng_candidate"].get("compiled_leaves", []):
        declaration_node = declaration_ids.get(declaration_name)
        if declaration_node:
            add_edge(declaration_node, laboratory_group, "audited in")

    payload = {
        "schema_version": 1,
        "generated_at": generated_at,
        "edge_direction": "Prerequisite to consumer for proof/import/order edges; parent to child for contains edges.",
        "evidence_boundary": (
            "This is a generated navigation graph over source containment, module imports, reviewed teaching dependencies, "
            "milestone evidence, and textbook mappings. It is not a kernel trace or the frozen exact environment graph."
        ),
        "root": root_id,
        "views": {
            "overview": [root_id, book_group, spine_group, milestone_group, laboratory_group],
            "book": [root_id, book_group] + [chapter_ids[item["slug"]] for item in chapters],
            "spine": [root_id, spine_group] + [spine_ids[item["slug"]] for item in spine_chapters],
            "milestones": [root_id, milestone_group],
            "modules": [root_id, book_group] + [chapter_ids[item["slug"]] for item in chapters],
        },
        "nodes": list(nodes.values()),
        "edges": edges,
    }
    graph_dir = output / "lean-graph"
    graph_dir.mkdir(parents=True, exist_ok=True)
    write_text_lf(
        graph_dir / "graph.json",
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")),
    )

    body = f"""
<section class="hero lean-graph-hero" id="lean-graph">
  <p class="eyebrow">Generated library topology · progressive disclosure</p>
  <h1 class="page-title">Underlying Lean Graph of BanditRLlib</h1>
  <p class="lede">Start with the library trunk, then open one curriculum, source chapter, module, milestone, or declaration branch at a time. Search can jump directly to any of the {len(declarations):,} indexed Lean declarations without drawing the whole library at once.</p>
  <div class="stats-grid lean-graph-stats">
    <div class="stat"><span class="stat-value">{len(chapters)}</span><span class="stat-label">Book Map chapters</span></div>
    <div class="stat"><span class="stat-value">{len(spine_chapters)}</span><span class="stat-label">Part IV source chapters</span></div>
    <div class="stat"><span class="stat-value">{len(modules):,}</span><span class="stat-label">Lean modules</span></div>
    <div class="stat"><span class="stat-value">{len(declarations):,}</span><span class="stat-label">indexed declarations</span></div>
  </div>
  <div class="callout"><strong>Reading rule.</strong> Labeled proof, import, and order edges point from prerequisite to consumer. Dashed <em>contains</em> edges describe navigation. Whole-chapter status and individual compiled declarations remain separate.</div>
</section>

<section id="explorer">
  <div class="lean-graph-app" data-lean-graph data-graph-source="graph.json">
    <header class="lean-graph-toolbar">
      <div class="lean-graph-views" role="group" aria-label="Lean Graph view">
        <button type="button" data-graph-view="overview" aria-pressed="true">Overview</button>
        <button type="button" data-graph-view="book" aria-pressed="false">Book Map</button>
        <button type="button" data-graph-view="spine" aria-pressed="false">Part IV</button>
        <button type="button" data-graph-view="milestones" aria-pressed="false">Milestones</button>
        <button type="button" data-graph-view="modules" aria-pressed="false">Lean branches</button>
      </div>
      <div class="lean-graph-search-shell">
        <label for="lean-graph-search">Search theorem, module, milestone, or chapter</label>
        <input id="lean-graph-search" type="search" data-graph-search placeholder="e.g. GaussianMinimax, UCBVI, pullCount" autocomplete="off" role="combobox" aria-autocomplete="list" aria-controls="lean-graph-suggestions" aria-expanded="false">
        <ul id="lean-graph-suggestions" data-graph-suggestions role="listbox" hidden></ul>
      </div>
      <div class="lean-graph-actions">
        <label for="lean-graph-branch-size">Branch size</label>
        <select id="lean-graph-branch-size" data-graph-branch-size><option value="12">12</option><option value="24">24</option><option value="48">48</option></select>
        <button type="button" data-graph-fit>Fit</button>
        <button type="button" data-graph-reset>Reset</button>
        <span data-graph-count aria-live="polite">Loading graph…</span>
      </div>
    </header>
    <div class="lean-graph-stage">
      <div class="lean-graph-canvas" data-graph-canvas tabindex="0" aria-label="Interactive Lean graph canvas. Drag to pan and use the mouse wheel to zoom.">
        <svg data-graph-svg role="img" aria-label="Interactive BanditRLlib Lean graph"></svg>
        <p class="lean-graph-empty" data-graph-empty hidden>No matching branch is visible.</p>
        <small>Click or press Enter on a node to inspect and expand it · drag to pan · wheel to zoom</small>
      </div>
      <aside class="lean-graph-detail" data-graph-detail aria-live="polite">
        <div class="lean-graph-placeholder"><span>Branch inspector</span><h2>Select a node</h2><p>Status, exact source links, branch children, immediate prerequisites, and consumers will appear here.</p></div>
      </aside>
    </div>
  </div>
</section>

<section id="semantics">
  <h2>Three graph layers, three meanings</h2>
  <div class="card-grid lean-graph-explainers">
    <article class="info-card"><span class="level-label">Learn</span><h3>Curriculum topology</h3><p>Book Map and Part IV nodes connect mathematical reading order to the modules and declarations that currently support each chapter.</p></article>
    <article class="info-card"><span class="level-label">Reuse</span><h3>Lean library topology</h3><p>Module-import and reviewed teaching edges expose reusable prerequisites. Search reveals an exact declaration together with its parent module and recorded neighbors.</p></article>
    <article class="info-card"><span class="level-label">Audit</span><h3>Proof-structure evidence</h3><p>The <a href="../proof-graph-laboratory/index.html">Proof Graph Laboratory</a> separately reports the frozen compiled-environment observation and experimental support-compression metrics.</p></article>
  </div>
  <div class="callout warning"><strong>Evidence boundary.</strong> The browser graph is a generated navigation index, not a kernel trace, elaborator trace, or proof certificate. Exact Lean statements and the verified build gate remain authoritative.</div>
</section>

<section id="contribute-graph">
  <h2>What a contribution changes</h2>
  <ol class="contribution-steps">
    <li><strong>Reuse an existing branch.</strong><span>A new theorem points to the exact modules and declarations it consumes instead of duplicating them.</span></li>
    <li><strong>Close a named leaf.</strong><span>A partial or blocked milestone gains compiled evidence while its broader chapter boundary stays honest.</span></li>
    <li><strong>Add a cross-branch bridge.</strong><span>A reviewed dependency edge records a reusable connection between algorithm families or mathematical layers.</span></li>
    <li><strong>Expose an unresolved interface.</strong><span>A missing history law, concentration bridge, or source theorem remains visible rather than appearing as proved.</span></li>
  </ol>
  <p class="reference-note">The independent interaction design is informed by Samplinglib's public <a href="https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/lean-foundations.html">Underlying Lean Graph of Libraries</a>. No Samplinglib source, stylesheet, template, or graph data is copied.</p>
</section>
"""
    toc: list[tuple[str, str]] = []
    write_page(
        output,
        page_path,
        layout(
            page_path,
            "Underlying Lean Graph",
            body,
            toc,
            "lean-graph",
            verified,
            generated_at,
            extra_scripts=("static/lean-graph.js",),
            wide=True,
        ),
    )
    return {"node_count": len(nodes), "edge_count": len(edges)}


def build_proof_graph_laboratory(
    output: Path,
    report: dict[str, Any],
    novelty: dict[str, Any],
    candidate_evaluation: dict[str, Any],
    decl_by_name: dict[str, dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    """Render only versioned proof-graph observations; no analysis runs in Pages."""

    page_path = "proof-graph-laboratory/index.html"
    graph = report["graph"]
    counts = graph["counts"]
    shared = report["shared_library"]
    zdd = report["zdd"]
    hypergraph = report["hypergraph"]
    benchmark_cards = []
    for benchmark in report["benchmarks"]:
        cost = benchmark["proof_cost_vector"]
        dag = cost["semantic_dag"]
        reuse = cost["reuse_coverage"]
        check_time = cost["lean_check_time"]
        benchmark_cards.append(
            f"""
<article class="info-card">
  <span class="level-label">{html.escape(benchmark['algorithm'])} · compiled root</span>
  <h3>{html.escape(benchmark['id'])}</h3>
  <p>{html.escape(benchmark['target_contract'])}</p>
  <dl class="teaching-grid">
    <div><dt>Project support</dt><dd>{reuse['support_declarations']:,} declarations</dd></div>
    <div><dt>Shared support</dt><dd>{reuse['shared_declarations']:,} ({reuse['ratio']:.1%})</dd></div>
    <div><dt>Semantic DAG</dt><dd>{dag['components']:,} components · depth {dag['depth']}</dd></div>
    <div><dt>Proof-term proxy</dt><dd>{cost['proof_term_object_proxy_sum']:,} shared objects</dd></div>
    <div><dt>Local Lean check</dt><dd>{check_time['seconds']:.6f} seconds · one warm-dependency run</dd></div>
  </dl>
</article>"""
        )

    zdd_rows = "".join(
        "<tr>"
        f"<td>{html.escape(order['order'])}</td>"
        f"<td>{order['nonterminal_nodes']:,}</td>"
        f"<td>{order['serialized_proxy_bytes']:,}</td>"
        f"<td>{order['tracemalloc_peak_bytes']:,}</td>"
        "</tr>"
        for order in zdd["orders"]
    )
    cng = novelty["cng_candidate"]
    candidate_proxy = candidate_evaluation["fixed_canonicalization_proxy"]
    candidate_vector = candidate_evaluation["novelty_vector_current_evidence"]
    cng_links = []
    for full_name in cng.get("compiled_leaves", []):
        declaration = decl_by_name.get(full_name)
        if declaration is None:
            cng_links.append(f"<code>{html.escape(full_name)}</code>")
        else:
            cng_links.append(
                f'<a href="{declaration_href(page_path, declaration)}"><code>{html.escape(full_name)}</code></a>'
            )
    cng_list = "".join(f"<li>{item}</li>" for item in cng_links)
    neutral_grades = "".join(
        f"<li><code>{html.escape(label)}</code></li>"
        for label in novelty["evaluation_design"]["neutral_grades"]
    )
    body = f"""
<section class="hero" id="proof-graph-laboratory">
  <p class="eyebrow">Auditable proof structure · local prototypes</p>
  <h1 class="page-title">Proof Graph Laboratory / Mathematical Motifs</h1>
  <p class="lede">Treat the verified library as an instrument for asking whether a target-faithful proof is a coverage extension, a library consolidation, or evidence of irreducible reusable proof structure.</p>
  <div class="callout warning"><strong>Evidence boundary.</strong> The graph is environment-extracted from compiled declaration types and values; it is not a kernel trace or an elaborator trace. Proof-cost, ZDD, hypergraph/MIP, and novelty operations are prototypes, not Lean theorems or validated scientific scores.</div>
  <p class="hero-actions"><a class="button primary" href="../lean-graph/index.html">Explore the interactive Lean Graph</a><span>Use the graph for progressive chapter → module → declaration navigation; use this laboratory for frozen proof-structure evidence.</span></p>
</section>

<section id="frozen-graph">
  <h2>Frozen exact-dependency observation</h2>
  <p>The baseline is <code>{html.escape(novelty['freeze_library_at_t']['git_commit'])}</code>; the deterministic graph artifact has SHA-256 <code>{html.escape(graph['sha256'])}</code>. Project ownership comes from the loaded Lean environment, with signature/type and value/proof dependencies kept separate.</p>
  <div class="stats-grid">
    <div class="stat"><span class="stat-value">{counts['project_nodes']:,}</span><span class="stat-label">project-owned declarations</span></div>
    <div class="stat"><span class="stat-value">{counts['external_boundary_nodes']:,}</span><span class="stat-label">direct external boundary declarations</span></div>
    <div class="stat"><span class="stat-value">{counts['edges']:,}</span><span class="stat-label">direct type/value edges</span></div>
    <div class="stat"><span class="stat-value">{counts['module_imports']:,}</span><span class="stat-label">module import records</span></div>
  </div>
</section>

<section id="benchmark">
  <h2>Fixed compiled benchmark</h2>
  <p>These terminals are unchanged observations, not claims that each complete algorithm family is formalized. The union charges each compiled declaration once: {shared['standalone_fixed_charge_sum']:,} standalone support memberships compress to {shared['union_fixed_charge']:,} union declarations, with {shared['shared_declaration_count']:,} declarations shared by at least two routes.</p>
  <div class="info-grid">{"".join(benchmark_cards)}</div>
</section>

<section id="support-compression">
  <h2>ZDD support families and hypergraph lower bounds</h2>
  <p>The ZDD contains only minimal support sets over a fixed declaration universe. Metavariables, tactics, unification constraints, and other dependent proof state remain outside. Local time and <code>tracemalloc</code> values are implementation observations, not universal complexity claims.</p>
  <div class="table-wrap"><table><thead><tr><th>Variable order</th><th>ZDD nodes</th><th>Serialized proxy bytes</th><th>Local peak bytes</th></tr></thead><tbody>{zdd_rows}</tbody></table></div>
  <p>The unit-charge hypergraph exact optimum is {hypergraph['unit_fixed_charge_exact_optimum']:,}; both reported admissible lower bounds are {hypergraph['admissible_lower_bounds']['max_single_obligation_min_bundle']:,} on this benchmark. Every concrete completion is tested to map to the relaxation. Pruning is called safe only under the explicit contract <code>LB(s) &lt;= OPT_remaining(s)</code>. The MIP is a library planner/scheduler, not a Lean elaborator.</p>
</section>

<section id="novelty-vector">
  <h2>Non-scalar proof-structural novelty audit</h2>
  <p>Raw new-node count is excluded: helper names and proof splitting can manipulate it. The fixed vector keeps five questions separate: conditional residual signatures with separately audited irreducibility; backward compression; proof-cost Pareto-frontier shift; held-out transfer; and target novelty versus proof novelty.</p>
  <ol class="contribution-steps">
    <li><strong>Freeze the library at t.</strong><span>Freeze statements, assumptions, canonicalization, compression, and benchmark roots before comparison.</span></li>
    <li><strong>Audit residual structure.</strong><span>Compare canonical lemma motifs, support hyperedges, obligation types, and composition constraints—not declaration names.</span></li>
    <li><strong>Test backward compression and Pareto movement.</strong><span>Report every declared cost dimension, including check time and open obligations, without scalarizing reuse into an unbounded reward.</span></li>
    <li><strong>Transfer to held-out theorems.</strong><span>Do not use the held-out family to design the abstraction; disclose failures and unlocked obligations.</span></li>
    <li><strong>Review interpretability.</strong><span>Run ordering/compression ablations and blind human review before assigning a neutral grade.</span></li>
  </ol>
  <p>Neutral audit grades:</p><ul>{neutral_grades}</ul>
</section>

<section id="cng-candidate">
  <div class="theorem-header"><div><p class="eyebrow">Candidate reusable abstraction</p><h2>Curvature–Noise–Gap finite geometry</h2></div>{status_badge('partial')}</div>
  <p>{html.escape(cng['current_evidence'])}</p>
  <p><strong>Current falsification result.</strong> The fixed two-round name-independent proxy finds {candidate_proxy['color_signatures_absent_from_frozen_library']} new neighborhood-color signatures and {candidate_proxy['direct_support_signatures_absent_from_frozen_library']} new direct-support signatures, but explicitly does not establish irreducibility. All frozen benchmark closures are unchanged; there are {candidate_vector['backward_compression_gain']['existing_to_candidate_dependency_edges']} existing-to-CNG dependency edges and {candidate_vector['heldout_transfer_gain']['candidate_declarations_in_heldout_support']} CNG declarations in the held-out OFUL support. Structural discovery remains false.</p>
  <ul>{cng_list}</ul>
  <div class="callout"><strong>Falsifiable upgrade rule.</strong> CNG becomes structural-discovery evidence only if it replaces multiple audited route-specific subgraphs, improves the declared cost vector with a reported Pareto relation, and helps a theorem family held out from design or unlocks a blocked obligation. Merely restating a Tsallis-INF derivation does not qualify.</div>
</section>

<section id="execution-boundary">
  <h2>Local execution and static Pages boundary</h2>
  <p>This page renders versioned JSON summaries. Static GitHub Pages does not load a Lean environment, regenerate the graph, execute the ZDD/hypergraph prototype, solve a MIP, or certify novelty. Reproduce those observations locally after the Lean gate:</p>
  <pre class="lean-code"><code>lake build BanditRLProof
lake env lean --run tools/ProofGraphExport.lean --compact proof-graph.json
python tools/proof_graph_lab.py validate-export --graph proof-graph.json
python tools/proof_graph_lab.py benchmark --graph proof-graph.json --config research-wiki/proof-graph/benchmark_roots.json --measurements research-wiki/proof-graph/benchmark_measurements.json --output benchmark-report.json</code></pre>
  <p>The laboratory explicitly excludes Chapters 13–17, finite-arm lower bounds, Bernoulli-KL/change-of-measure/minimax/asymptotic lower-bound declarations, their cards/pages, and the lower-bound task's active frontier.</p>
</section>
"""
    toc = [
        ("proof-graph-laboratory", "Laboratory"),
        ("frozen-graph", "Frozen graph"),
        ("benchmark", "Benchmark"),
        ("support-compression", "ZDD and hypergraph"),
        ("novelty-vector", "Novelty vector"),
        ("cng-candidate", "CNG candidate"),
        ("execution-boundary", "Execution boundary"),
    ]
    write_page(
        output,
        page_path,
        layout(page_path, "Proof Graph Laboratory", body, toc, "proof-lab", verified, generated_at),
    )


def render_harness_comparison_ledger(page_path: str, comparison: dict[str, Any]) -> str:
    matched = comparison["matched_evidence"]
    rows = []
    for harness in ("hierarchical", "master-worker"):
        arm = matched[harness]
        rows.append(
            "<tr>"
            f"<th scope=\"row\">{html.escape(harness)}</th>"
            f"<td>{int(arm.get('runs', 0))}</td>"
            f"<td>{int(arm.get('attempts', 0))}</td>"
            f"<td>{int(arm.get('reviewed_attempts', 0))}</td>"
            f"<td>{int(arm.get('substantive_attempts', 0))}</td>"
            f"<td>{html.escape(str(arm.get('substantive_score', 0)))}</td>"
            f"<td>{html.escape(str(arm.get('critical_path_seconds', 0.0)))}</td>"
            "</tr>"
        )
    decision = comparison["decision"]
    matched_count = len(comparison["matched_experiments"])
    minimum_count = int(comparison["minimum_matched_experiments"])
    status = str(decision.get("status", "unrecorded")).replace("-", " ")
    recommended = str(decision.get("recommended_default", "unrecorded"))
    next_harness = str(decision.get("next_experiment_harness", "unrecorded"))
    reason = str(decision.get("reason", "No deterministic reason recorded."))
    source_href = source_url("runs/harness-comparison/latest.json")
    prompt_href = source_url("runs/harness-comparison/latest.prompt.md")
    method_href = source_url("docs/harness_self_comparison.md")
    return f"""
<section id="comparison-evidence">
  <p class="eyebrow">Generated from structured run logs</p>
  <div class="snapshot-heading"><div><h2>Current harness-comparison evidence</h2><p class="section-intro">The table reports only matched, reviewer-classified attempts on the same frozen target. Historical activity without the comparison contract is excluded.</p></div>{status_badge('prototype')}</div>
  <div class="comparison-decision" role="status" aria-label="Current harness comparison decision">
    <div><span class="level-label">Decision status</span><strong>{html.escape(status.title())}</strong></div>
    <div><span class="level-label">Matched evidence</span><strong>{matched_count} of {minimum_count} required</strong></div>
    <div><span class="level-label">Recommended default</span><strong>{html.escape(recommended)}</strong></div>
    <div><span class="level-label">Next matched arm</span><strong>{html.escape(next_harness)}</strong></div>
  </div>
  <div class="table-wrap comparison-table" tabindex="0" role="region" aria-label="Matched hierarchical and master-worker evidence">
    <table>
      <thead><tr><th>Harness</th><th>Runs</th><th>Attempts</th><th>Reviewed</th><th>Substantive</th><th>Score</th><th>Critical seconds</th></tr></thead>
      <tbody>{''.join(rows)}</tbody>
    </table>
  </div>
  <div class="callout warning"><strong>Why no winner is shown.</strong> {html.escape(reason)} GPT receives this deterministic report and a bounded review packet; it may interpret bottlenecks and propose the next matched experiment, but it cannot promote unreviewed output or override this evidence boundary.</div>
  <div class="source-links"><a href="{source_href}">Open the deterministic JSON</a><a href="{prompt_href}">Open the GPT review packet</a><a href="{method_href}">Read the comparison method</a></div>
</section>
"""


def build_workflow(output: Path, verified: bool, generated_at: str) -> None:
    page_path = "workflow/index.html"
    comparison = load_harness_comparison()
    comparison_ledger = render_harness_comparison_ledger(page_path, comparison)
    decision = comparison["decision"]
    decision_status = str(decision.get("status", "unrecorded"))
    if decision_status == "insufficient-evidence":
        current_decision = (
            "The structured log ledger does not yet justify declaring either harness "
            "universally better, so the hierarchical loop remains the default."
        )
    else:
        current_decision = (
            "The deterministic matched-evidence ledger currently recommends "
            f"{decision.get('recommended_default', 'no recorded default')}."
        )
    body = f"""
<section class="hero" id="workflow">
  <p class="eyebrow">From theorem target to compiled certificate</p>
  <h1 class="page-title">The ABRL proof workflow</h1>
  <p class="lede">Automation proposes and attempts proof leaves, but target fidelity, explicit assumptions, local compilation, and reviewer gates determine whether a result is achieved.</p>
</section>

<section id="contract">
  <h2>The repository contract</h2>
  <pre class="lean-code"><code>literature theorem or new bandit/RL target
→ theorem card and assumption ledger
→ exact Lean statement and proof-DAG leaves
→ compiled Lean certificate
→ synchronized explanation and implementation map
→ reusable retrieval memory</code></pre>
  <p>A theorem card is evidence for a route. It is never displayed as a local proof unless the corresponding declaration is imported or proved and the Lean gate succeeds.</p>
</section>

<section id="roles">
  <p class="eyebrow">Adaptive orchestration, one evidence standard</p>
  <h2>Compare proof routes by mathematical progress</h2>
  <p>The scheduler can run the established hierarchical director–planner–worker loop or a bounded master–worker trial in which several workers explore independent proof routes. Both receive the same frozen target, budget, source packet, and deterministic gates.</p>
  <p><strong>Current decision.</strong> {html.escape(current_decision)} The master–worker route is experimental and is enabled only when parallel alternatives are genuinely independent. A trial wins only by delivering a stronger checked certificate, a smaller named blocker, or a reusable lemma—not by producing more messages or attempts.</p>
  {render_diagram(page_path, 'automation-workflow.mmd', 'Evidence-aware scheduler comparing a hierarchical loop and a bounded master-worker trial before a common Lean and reviewer gate')}
</section>

{comparison_ledger}

<section id="commands">
  <h2>Reproducible gates</h2>
  <pre class="lean-code"><code>python3 tools/bandit.py blueprint-refresh &lt;task-id&gt;
python3 tools/bandit.py harness-compare --task &lt;task-id&gt;
python3 tools/bandit.py reference-index
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
python3 website/scripts/ide_server.py</code></pre>
  <p>The website build scans Lean source directly, including declarations whose keyword and name span separate lines. A new declaration therefore enters the catalog without a hand-edited index; major results still need a reviewed teaching note and milestone entry. The IDE server is a separate loopback-only development command and is never part of the public Pages deployment.</p>
</section>

<section id="failure-policy">
  <h2>Failure is recorded, not hidden</h2>
  <ul>
    <li>If a proof attempt repeatedly fails, audit the statement, hypotheses, and possible counterexamples before broad tactic search.</li>
    <li>If a route lacks a trajectory law, measurability proof, or integrability contract, name that interface as the blocker.</li>
    <li>If prose is stronger than Lean, weaken the prose or add the missing theorem; never promote a plan to compiled status.</li>
    <li>If a general lemma belongs in Mathlib, keep the project wrapper thin and record the candidate route.</li>
  </ul>
</section>
"""
    toc = [("workflow", "Workflow"), ("contract", "Contract"), ("roles", "Roles"), ("comparison-evidence", "Comparison evidence"), ("commands", "Gates"), ("failure-policy", "Failure policy")]
    write_page(
        output,
        page_path,
        layout(page_path, "ABRL workflow", body, toc, "workflow", verified, generated_at),
    )


def build_attribution(output: Path, verified: bool, generated_at: str) -> None:
    page_path = "attribution/index.html"
    body = f"""
<section class="hero" id="attribution">
  <p class="eyebrow">Design provenance and license boundary</p>
  <h1 class="page-title">Attribution</h1>
  <p class="lede">This site's organization is inspired by Sho Sonoda's Lean-Ridgelet Blueprint, especially its readable implementation map from mathematics to Lean.</p>
</section>

<section id="lean-ridgelet">
  <h2>Lean-Ridgelet inspiration</h2>
  <p><a href="https://github.com/shosonoda/lean-ridgelet">Lean-Ridgelet</a> is a Lean formalization project by <strong>Sho Sonoda</strong>. Its <a href="https://shosonoda.github.io/lean-ridgelet/">Blueprint website</a> demonstrates how publication-order mathematical exposition can link to verified declarations.</p>
  <p>The upstream repository license was checked before implementation and is Apache License 2.0. ABRL uses an independently written Python generator, HTML structure, CSS, JavaScript, Mermaid diagrams, and prose. No Lean-Ridgelet source file, template, stylesheet, or configuration file is copied into this repository.</p>
  <div class="callout warning">This attribution records inspiration only. It does not imply that Sho Sonoda participated in, reviewed, endorsed, or maintains Auto-Bandit-RL-Proof-In-Sleep.</div>
</section>

<section id="statsmllib">
  <h2>StatsMLlib community inspiration</h2>
  <p><a href="https://statsmllib.github.io/">StatsMLlib</a> and its <a href="https://github.com/Lean-MoDS/StatsMLlib">public repository</a> demonstrate an effective community-facing organization around a book map, selected theorems, contributor credit, installation, and a visible contribution guide.</p>
  <p>StatsMLlib is Apache-2.0 licensed. ABRL independently implements its three-purpose learning, browsing, and contribution interface, its lemma-packet schema, governance documents, generator, HTML, CSS, JavaScript, and diagrams. No StatsMLlib template, stylesheet, prose, or source file is copied here.</p>
  <div class="callout warning">This reference records organizational inspiration only. It does not imply that StatsMLlib, Lean-MoDS, its organizers, or its contributors participate in, endorse, review, or maintain ABRL.</div>
</section>

<section id="samplinglib">
  <h2>Samplinglib graph and frontier inspiration</h2>
  <p>The progressive graph explorer is informed by the public <a href="https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/lean-foundations.html">Underlying Lean Graph of Libraries</a> in <a href="https://github.com/DakeBU/Auto-Sampling-Theory-In-Sleep">Auto-Sampling-Theory-In-Sleep / Samplinglib</a>. BanditRLwiki's setting → case → frontier information architecture is also informed by its public <a href="https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki.html">SampleWiki</a> and <a href="https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki/frontier.html">Sampling Frontier</a>.</p>
  <p>The Samplinglib default branch did not expose a repository license file when this design audit was performed on 2026-08-22. BanditRLlib therefore treats these pages as design inspiration only and independently implements its graph model, assumption atlas, theorem data, generated HTML, CSS, JavaScript, filters, status semantics, and accessibility behavior. No Samplinglib source file, graph or theorem data, template, stylesheet, or prose is copied into this repository.</p>
  <div class="callout warning">This reference records design inspiration only. It does not imply shared verification status, shared maintainers, endorsement, review, or responsibility for BanditRLlib.</div>
</section>

<section id="other-sources">
  <h2>Mathematical and software sources</h2>
  <p>The repository's full literature, Mathlib, LML, automation, and proof-system attribution ledger is maintained in <a href="{source_url('docs/attribution.md')}"><code>docs/attribution.md</code></a> and <a href="{source_url('NOTICE.md')}"><code>NOTICE.md</code></a>.</p>
  <p>Theorem cards summarize external results for retrieval. They do not transfer authorship and do not become local proof certificates until an import or local proof compiles.</p>
</section>
"""
    toc = [("attribution", "Attribution"), ("lean-ridgelet", "Lean-Ridgelet"), ("statsmllib", "StatsMLlib"), ("samplinglib", "Samplinglib inspiration"), ("other-sources", "Other sources")]
    write_page(
        output,
        page_path,
        layout(page_path, "Attribution", body, toc, "attribution", verified, generated_at),
    )


def validate_content(
    declarations: list[dict[str, Any]],
    highlights: list[dict[str, Any]],
    results: list[dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    by_name: dict[str, dict[str, Any]] = {}
    duplicates = []
    for declaration in declarations:
        name = declaration["full_name"]
        if name in by_name:
            duplicates.append(name)
        by_name[name] = declaration
    if duplicates:
        raise SystemExit(f"duplicate Lean declaration names in scanner: {sorted(set(duplicates))[:10]}")
    missing_highlights = [item["full_name"] for item in highlights if item["full_name"] not in by_name]
    missing_results = [
        name
        for result in results
        for name in result["declarations"] + result.get("depends_on", [])
        if name not in by_name
    ]
    missing_dependencies = [
        name
        for item in highlights
        for name in item.get("dependencies", [])
        if name not in by_name
    ]
    if missing_highlights or missing_results or missing_dependencies:
        message = {
            "missing_highlights": sorted(set(missing_highlights)),
            "missing_result_references": sorted(set(missing_results)),
            "missing_highlight_dependencies": sorted(set(missing_dependencies)),
        }
        raise SystemExit("content references unknown Lean declarations:\n" + json.dumps(message, indent=2))
    return by_name


def validate_readings(chapters: list[dict[str, Any]], readings: list[dict[str, Any]]) -> None:
    chapter_slugs = {chapter["slug"] for chapter in chapters}
    reading_slugs = [reading.get("slug") for reading in readings]
    if len(reading_slugs) != len(set(reading_slugs)):
        raise SystemExit("readings.json contains duplicate chapter slugs")
    if set(reading_slugs) != chapter_slugs:
        raise SystemExit(
            "readings.json must cover exactly the Book Map chapters:\n"
            + json.dumps(
                {
                    "missing": sorted(chapter_slugs - set(reading_slugs)),
                    "extra": sorted(set(reading_slugs) - chapter_slugs),
                },
                indent=2,
            )
        )
    for reading in readings:
        if not reading.get("primary", {}).get("url"):
            raise SystemExit(f"reading {reading['slug']} lacks a primary source URL")
        companions = ([reading["companion"]] if reading.get("companion") else []) + reading.get("companions", [])
        if any(not source.get("url") for source in companions):
            raise SystemExit(f"reading {reading['slug']} has a companion without a source URL")
        if not reading.get("algorithm", {}).get("steps"):
            raise SystemExit(f"reading {reading['slug']} lacks an algorithm or proof flow")
        theorems = ([reading["source_theorem"]] if reading.get("source_theorem") else []) + reading.get("source_theorems", [])
        if theorems:
            for theorem in theorems:
                normalized = normalize_math_source(theorem.get("math", ""))
                if normalized.count(r"\(") != normalized.count(r"\)") or normalized.count(r"\[") != normalized.count(r"\]"):
                    raise SystemExit(f"reading {reading['slug']} has unbalanced mathematical delimiters")
        elif not reading.get("source_boundary"):
            raise SystemExit(f"reading {reading['slug']} needs a source theorem or explicit boundary")


def build_search_index(output: Path, declarations: list[dict[str, Any]]) -> None:
    payload = [
        {
            "name": decl["full_name"],
            "kind": decl["kind"],
            "module": decl["module"],
            "chapter": decl["chapter_title"],
            "url": f"modules/{decl['module_slug']}/index.html#{decl['anchor']}",
        }
        for decl in declarations
    ]
    write_text_lf(
        output / "search-index.json",
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")),
    )


def git_source_state() -> tuple[str, bool]:
    commit = os.environ.get("GITHUB_SHA", "")
    if not commit:
        completed = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode == 0:
            commit = completed.stdout.strip()
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    return commit, status.returncode == 0 and bool(status.stdout.strip())


def build_public_repository_readme(output: Path, manifest: dict[str, Any]) -> None:
    commit = manifest.get("source_commit") or "unrecorded"
    source_note = (
        f"a Lean-verified working-tree snapshot based on canonical commit `{commit}`; "
        "the manifest records that local changes were present during generation"
        if manifest.get("source_dirty")
        else f"canonical commit `{commit}` after the Lean gate passed"
    )
    readme = f"""# 🌐 BanditRLlib

This generated artifact accompanies the community-facing, textbook-style
BanditRLlib website produced by the ABRL research project.

Website: <{PUBLIC_SITE_URL}/>
Canonical repository: <{GITHUB_REPO}>

## 🧭 Three ways to use BanditRLlib

1. **Learn:** follow a Lean-aligned textbook path through bandit, probability,
   optimization, stopping-time, and finite-horizon RL mathematics.
2. **Browse:** search {manifest['declaration_count']:,} exact Lean definitions,
   theorems, and lemmas across {manifest['module_count']:,} modules.
3. **Contribute:** propose a sourced result through an issue or versioned lemma
   packet; Live Formalization uses the same machine-readable contract.

## 📍 Current snapshot

The generated site was built from {source_note}. Compiled, partial, planned,
blocked, and community-proposal states remain distinct. The public repository
is the source of truth for Lean code, documentation, contribution metadata,
and deployment. Generated site output includes only allowlisted public files.

Start with [CONTRIBUTING.md](CONTRIBUTING.md), the
[community page]({PUBLIC_SITE_URL}/community/), or the
[JSON Schema](community/contribution.schema.json). Public packets are validated
before deployment; only the full upstream project gate can mark a result
integrated.

## 🧬 Attribution

The implementation-map organization is inspired by **Sho Sonoda's**
[Lean-Ridgelet](https://github.com/shosonoda/lean-ridgelet) and its
[Blueprint](https://shosonoda.github.io/lean-ridgelet/). The community landing
page and book-to-library navigation also take organizational inspiration from
[StatsMLlib](https://statsmllib.github.io/) by the
[Lean Models, Decisions, and Statistics community](https://github.com/Lean-MoDS/StatsMLlib).
The progressive Lean Graph is informed by Samplinglib's public
[Underlying Lean Graph of Libraries](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/lean-foundations.html).
BanditRLwiki's assumption-setting and frontier organization is informed by its
[SampleWiki](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki.html)
and [Frontier](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki/frontier.html).
These references are attribution for inspiration only and do not imply
participation, endorsement, or maintenance of BanditRLlib. The graph model,
theorem data, generated HTML, CSS, and JavaScript are independently implemented;
no template, stylesheet, graph data, theorem data, prose, or source file was
copied.

## ⚖️ License

The public website and intentional community contributions are distributed
under the [MIT License](LICENSE).
"""
    write_text_lf(output / "README.md", readme)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--lean-verified",
        action="store_true",
        help="mark non-placeholder local declarations compiled; run only after the Lean gate succeeds",
    )
    parser.add_argument(
        "--public-base-url",
        default="",
        help="build a public snapshot whose private source links use the explicit source-access page",
    )
    parser.add_argument(
        "--public-snapshot-base-url",
        default="",
        help="record public deployment metadata without changing commit-pinned source links",
    )
    args = parser.parse_args()
    global PUBLIC_BASE_URL, PUBLIC_SNAPSHOT_BASE_URL
    global SITE_CHAPTERS, SITE_READINGS, SITE_TEXTBOOK_SPINE, SITE_BANDITRLWIKI, SOURCE_BRANCH
    PUBLIC_BASE_URL = args.public_base_url.rstrip("/")
    PUBLIC_SNAPSHOT_BASE_URL = args.public_snapshot_base_url.rstrip("/")
    if PUBLIC_BASE_URL and PUBLIC_SNAPSHOT_BASE_URL and PUBLIC_BASE_URL != PUBLIC_SNAPSHOT_BASE_URL:
        raise SystemExit("public source-access and snapshot base URLs must agree when both are set")
    source_commit, source_dirty = git_source_state()
    SOURCE_BRANCH = source_commit or "main"
    output = args.output.resolve()
    if output == ROOT.resolve() or ROOT.resolve() not in output.parents:
        raise SystemExit(f"refusing to build outside the repository: {output}")

    chapters = load_json(CONTENT_DIR / "chapters.json")["chapters"]
    people = load_json(CONTENT_DIR / "contributors.json")
    authors = people["authors"]
    community_contributors = people.get("community_contributors", [])
    SITE_CHAPTERS = chapters
    textbook_spine = load_json(CONTENT_DIR / "textbook_spine.json")
    SITE_TEXTBOOK_SPINE = textbook_spine
    banditrlwiki = load_json(CONTENT_DIR / "banditrlwiki.json")
    SITE_BANDITRLWIKI = banditrlwiki
    highlights = load_json(CONTENT_DIR / "highlights.json")["highlights"]
    results = load_json(CONTENT_DIR / "results.json")["results"]
    readings_payload = load_json(CONTENT_DIR / "readings.json")
    readings = readings_payload["readings"]
    validate_readings(chapters, readings)
    SITE_READINGS = {reading["slug"]: reading for reading in readings}
    milestone_counts_by_chapter: dict[str, Counter[str]] = defaultdict(Counter)
    for result in results:
        milestone_counts_by_chapter[result["chapter"]][result["status"]] += 1
    for chapter in chapters:
        chapter["milestone_counts"] = dict(milestone_counts_by_chapter[chapter["slug"]])
    roadmap = load_json(ROOT / "research-wiki" / "theory-tree" / "lean-route-roadmap.json")
    proof_graph_report = load_json(ROOT / "research-wiki" / "proof-graph" / "benchmark_report.json")
    novelty_audit = load_json(ROOT / "research-wiki" / "proof-graph" / "novelty_audit.json")
    cng_candidate_evaluation = load_json(
        ROOT / "research-wiki" / "proof-graph" / "cng_candidate_evaluation.json"
    )

    modules = scan_lean_tree()
    assign_chapters(modules, chapters)
    declarations = [decl for module in modules for decl in module["declarations"]]
    decl_by_name = validate_content(declarations, highlights, results)
    validate_textbook_spine(textbook_spine, decl_by_name)
    validate_banditrlwiki(banditrlwiki, decl_by_name, results)
    module_by_name = {module["name"]: module for module in modules}
    chapter_by_slug = {chapter["slug"]: chapter for chapter in chapters}
    highlights_by_name = {item["full_name"]: item for item in highlights}
    generated_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()

    if output.exists():
        shutil.rmtree(output)
    output.mkdir(parents=True)
    shutil.copytree(STATIC_DIR, output / "static")
    shutil.copytree(DIAGRAM_DIR, output / "diagrams")
    shutil.copytree(COMMUNITY_DIR, output / "community")
    shutil.copytree(PUBLIC_REPO_DIR, output, dirs_exist_ok=True)
    shutil.copy2(ROOT / "LICENSE", output / "LICENSE")
    shutil.copy2(ROOT / "NOTICE.md", output / "NOTICE.md")
    write_text_lf(
        output / "community" / "registry.json",
        json.dumps({"schema_version": "1.1", "entry_count": 0, "entries": []}, indent=2) + "\n",
    )
    (output / ".nojekyll").write_text("", encoding="utf-8")

    build_index(
        output,
        modules,
        declarations,
        chapters,
        authors,
        results,
        args.lean_verified,
        generated_at,
    )
    build_implementation_map(
        output,
        modules,
        decl_by_name,
        chapter_by_slug,
        results,
        args.lean_verified,
        generated_at,
    )
    build_catalog(output, declarations, chapters, args.lean_verified, generated_at)
    build_chapters(
        output,
        modules,
        chapters,
        highlights,
        results,
        decl_by_name,
        args.lean_verified,
        generated_at,
    )
    build_textbook_spine(
        output,
        textbook_spine,
        decl_by_name,
        args.lean_verified,
        generated_at,
    )
    build_module_pages(
        output,
        modules,
        module_by_name,
        chapter_by_slug,
        highlights_by_name,
        args.lean_verified,
        generated_at,
    )
    build_learning(output, chapters, args.lean_verified, generated_at)
    build_contributors(output, authors, community_contributors, args.lean_verified, generated_at)
    build_installation(output, args.lean_verified, generated_at)
    build_community(output, args.lean_verified, generated_at)
    build_research_ide(output, highlights, decl_by_name, args.lean_verified, generated_at)
    banditrlwiki_counts = build_banditrlwiki(
        output, banditrlwiki, decl_by_name, args.lean_verified, generated_at
    )
    build_roadmap(output, results, roadmap, decl_by_name, args.lean_verified, generated_at)
    lean_graph_counts = build_lean_graph(
        output,
        modules,
        declarations,
        chapters,
        highlights,
        results,
        textbook_spine,
        proof_graph_report,
        novelty_audit,
        args.lean_verified,
        generated_at,
    )
    build_proof_graph_laboratory(
        output,
        proof_graph_report,
        novelty_audit,
        cng_candidate_evaluation,
        decl_by_name,
        args.lean_verified,
        generated_at,
    )
    build_workflow(output, args.lean_verified, generated_at)
    build_attribution(output, args.lean_verified, generated_at)
    build_source_access(output, args.lean_verified, generated_at)
    build_search_index(output, declarations)

    manifest = {
        "generated_at": generated_at,
        "lean_verified": args.lean_verified,
        "module_count": len(modules),
        "declaration_count": len(declarations),
        "public_declaration_count": sum(1 for decl in declarations if not decl["private"]),
        "private_declaration_count": sum(1 for decl in declarations if decl["private"]),
        "placeholder_count": sum(1 for decl in declarations if decl["placeholder"]),
        "kind_counts": dict(sorted(Counter(decl["kind"] for decl in declarations).items())),
        "chapter_counts": dict(sorted(Counter(decl["chapter"] for decl in declarations).items())),
        "author_count": len(authors),
        "community_contributor_count": len(community_contributors),
        "contributor_count": len(authors) + len(community_contributors),
        "highlight_count": len(highlights),
        "ide_mapping_count": len(highlights),
        "milestone_count": len(results),
        "milestone_status_counts": dict(sorted(Counter(result["status"] for result in results).items())),
        "community_entry_count": 0,
        "reading_count": len(readings),
        "source_theorem_count": sum(
            (1 if reading.get("source_theorem") else 0) + len(reading.get("source_theorems", []))
            for reading in readings
        ),
        "textbook_spine_chapter_count": len(textbook_spine["chapters"]),
        "textbook_spine_status_counts": dict(
            sorted(Counter(chapter["status"] for chapter in textbook_spine["chapters"]).items())
        ),
        "banditrlwiki_family_count": banditrlwiki_counts["family_count"],
        "banditrlwiki_case_count": banditrlwiki_counts["case_count"],
        "banditrlwiki_paper_count": banditrlwiki_counts["paper_count"],
        "banditrlwiki_theorem_surface_count": banditrlwiki_counts["theorem_surface_count"],
        "banditrlwiki_paper_case_link_count": banditrlwiki_counts["paper_case_link_count"],
        "banditrlwiki_exact_source_audit_count": banditrlwiki_counts["exact_source_audit_count"],
        "banditrlwiki_literature_open_count": banditrlwiki_counts["literature_open_count"],
        "banditrlwiki_formalization_open_case_count": banditrlwiki_counts[
            "formalization_open_case_count"
        ],
        "banditrlwiki_formalization_leaf_count": banditrlwiki_counts[
            "formalization_leaf_count"
        ],
        "banditrlwiki_active_source_audit_count": banditrlwiki_counts[
            "active_source_audit_count"
        ],
        "banditrlwiki_literature_status_counts": dict(
            sorted(Counter(case["comparison"]["status"] for case in banditrlwiki["cases"]).items())
        ),
        "banditrlwiki_lean_status_counts": dict(
            sorted(Counter(case["lean"]["status"] for case in banditrlwiki["cases"]).items())
        ),
        "max_module_slug_length": max(len(module["slug"]) for module in modules),
        "public_snapshot": bool(PUBLIC_SNAPSHOT_BASE_URL or PUBLIC_BASE_URL),
        "public_base_url": PUBLIC_SNAPSHOT_BASE_URL or PUBLIC_BASE_URL,
        "source_commit": source_commit,
        "source_dirty": source_dirty,
        "lean_graph_node_count": lean_graph_counts["node_count"],
        "lean_graph_edge_count": lean_graph_counts["edge_count"],
        "proof_graph_benchmark_status": proof_graph_report["status"],
        "proof_graph_root_count": proof_graph_report["benchmark_contract"]["root_count"],
        "cng_candidate_status": novelty_audit["cng_candidate"]["status"],
        "cng_structural_discovery_established": cng_candidate_evaluation[
            "structural_discovery_established"
        ],
    }
    write_text_lf(output / "site-manifest.json", json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
    build_public_repository_readme(output, manifest)
    print(json.dumps(manifest, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
