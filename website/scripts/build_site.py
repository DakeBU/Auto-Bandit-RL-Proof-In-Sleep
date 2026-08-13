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

GITHUB_REPO = "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep"
PUBLIC_SITE_REPO = GITHUB_REPO
PUBLIC_SITE_URL = "https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep"
LIBRARY_NAME = "BanditRLlib"
RESEARCH_PROJECT = "Auto-Bandit-RL-Proof-In-Sleep"
PAPER_TITLE = (
    "ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library "
    "for Bandit and Reinforcement Learning Theory"
)
SOURCE_BRANCH = "main"
PUBLIC_BASE_URL = ""
SITE_CHAPTERS: list[dict[str, Any]] = []

STATUS_LABELS = {
    "compiled": "Compiled",
    "partial": "Partial",
    "planned": "Planned",
    "blocked": "Blocked",
    "stated": "Stated, proof incomplete",
    "source": "Source indexed",
    "integrated": "Integrated",
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

    return {
        "name": module_name(path),
        "file": rel_source(path),
        "slug": slugify(module_name(path)),
        "imports": imports,
        "docstring": module_docstring(text),
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
        for chapter in chapters:
            if any(fnmatch.fnmatch(module["file"], pattern) for pattern in chapter["module_globs"]):
                assigned = chapter
                break
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
) -> str:
    source = diagram_source(filename, status_counts)
    source_href = href_from(page_path, f"diagrams/{filename}")
    return (
        '<figure class="diagram">'
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
) -> str:
    root = page_root(page_path)
    start_items = [
        ("overview", "Overview", "index.html"),
        ("installation", "Installation", "installation/index.html"),
    ]
    library_items = [
        ("catalog", "Lean declarations", "declarations/index.html"),
        ("map", "Implementation map", "implementation-map/index.html"),
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
    formalize_nav = nav_links(formalize_items)
    community_nav = nav_links(community_items)
    def book_link(index: int, chapter: dict[str, Any]) -> str:
        target = f"chapters/{chapter['slug']}/index.html"
        active = ' aria-current="page"' if page_path == target else ""
        return (
            f'<a class="book-nav-link" href="{href_from(page_path, target)}"{active}>'
            f'<span>{index:02d}</span>{html.escape(chapter["short_title"])}</a>'
        )

    book_nav = nav_links([("chapters", "All chapters", "learning/index.html")]) + "".join(
        book_link(index, chapter)
        for index, chapter in enumerate(SITE_CHAPTERS, start=1)
    )
    toc_html = (
        '<aside class="side-nav" aria-label="On this page"><strong>On this page</strong>'
        + "".join(
            f'<a data-toc-link href="#{html.escape(anchor)}">{html.escape(label)}</a>'
            for anchor, label in toc
        )
        + "</aside>"
        if toc
        else ""
    )
    verification_class = "" if verified else " unverified"
    verification = (
        "Lean gate passed before this site build; local proof declarations are shown as compiled."
        if verified
        else "Preview build: run the Lean gate and rebuild with --lean-verified before treating local declarations as compiled."
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
        f'\n  <script src="{root}/{html.escape(script)}"></script>' for script in extra_scripts
    )
    return f"""<!doctype html>
<html lang="en" data-theme="blueprint">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="description" content="BanditRLlib: verified bandit and reinforcement-learning theory in Lean, produced by the ABRL hierarchical autoformalization harness.">
  <meta name="citation_title" content="{html.escape(PAPER_TITLE)}">
  <title>{html.escape(title)} · BanditRLlib</title>
  <link rel="stylesheet" href="{root}/static/site.css?v=20260811">
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
      <a class="brand" href="{href_from(page_path, 'index.html')}">
        <span class="brand-mark" aria-hidden="true">B</span>
        <span><strong>BanditRLlib</strong><small>Verified Lean library</small></span>
      </a>
      <button class="sidebar-close" type="button" data-sidebar-toggle aria-controls="site-sidebar" aria-expanded="false"><span aria-hidden="true">×</span><span class="visually-hidden">Close site navigation</span></button>
    </div>
    <div class="search-shell sidebar-search">
      <label class="nav-group-title" for="global-search">Search the Lean library</label>
      <input id="global-search" class="global-search" data-global-search type="search" placeholder="Declaration or module…" autocomplete="off">
      <ul class="search-results" data-global-results hidden></ul>
    </div>
    <nav class="sidebar-nav" aria-label="Primary">
      <div class="nav-group"><strong class="nav-group-title">Start</strong>{start_nav}</div>
      <div class="nav-group book-map-nav"><strong class="nav-group-title">Learn · Book map</strong>{book_nav}</div>
      <div class="nav-group"><strong class="nav-group-title">Library</strong>{library_nav}</div>
      <div class="nav-group"><strong class="nav-group-title">Formalize</strong>{formalize_nav}</div>
      <div class="nav-group"><strong class="nav-group-title">Community</strong>{community_nav}</div>
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
  <button class="sidebar-scrim" type="button" data-sidebar-scrim aria-label="Close site navigation" tabindex="-1"></button>
  <div class="site-content">
    <div class="verification-strip{verification_class}">{html.escape(verification)}</div>
    <div class="page-shell">
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
  <script src="{root}/static/site.js?v=20260811"></script>{extra_script_tags}
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
    <span class="book-chapter-meta">{status_badge(chapter['status'])}</span>
    <strong>{html.escape(chapter['title'])}</strong>
    <span class="book-summary">{html.escape(chapter['summary'])}</span>
    {audience}
  </div>
  <span class="book-chapter-arrow" aria-hidden="true">→</span>
</a>"""
        )
    return '<div class="book-map-grid">' + "".join(cards) + "</div>"


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
    return f"""
<article class="theorem-panel" id="{declaration['anchor']}-teaching">
  <div class="theorem-header">
    <h3>{html.escape(declaration['full_name'])}</h3>
    {status_badge(status)}
  </div>
  <div class="theorem-body">
    <p><strong>Plain-English statement.</strong> {html.escape(highlight['plain'])}</p>
    <div class="math-statement"><strong>Mathematical reading.</strong> {highlight['math']}</div>
    <dl class="teaching-grid">
      <div><dt>Intuition</dt><dd>{html.escape(highlight['intuition'])}</dd></div>
      <div><dt>Why it is needed</dt><dd>{html.escape(highlight['why'])}</dd></div>
      <div><dt>Place in the proof</dt><dd>{html.escape(highlight['position'])}</dd></div>
      <div><dt>Proof idea</dt><dd>{html.escape(highlight['proof_idea'])}</dd></div>
      <div><dt>Lean reading notes</dt><dd>{html.escape(highlight['lean_notes'])}</dd></div>
      <div><dt>Teaching dependencies</dt><dd>{dependencies}</dd></div>
    </dl>
    <h4>Exact Lean statement</h4>
    <pre class="lean-code"><code>{highlight_lean(declaration['statement'])}</code></pre>
    <div class="source-links">
      <a href="{declaration_href(page_path, declaration)}">Open in the declaration catalog</a>
      <a href="{source_url(declaration['file'], declaration['line'])}">Open source at line {declaration['line']}</a>
    </div>
  </div>
</article>
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
    contributor_cards = render_contributor_cards(page_path, authors, include_invitation=False)
    body = f"""
<section class="hero" id="overview">
  <p class="eyebrow">Verified bandit and reinforcement-learning theory in Lean</p>
  <h1>BanditRLlib</h1>
  <p class="lede">A source-synchronized Lean library, learning interface, live formalization workspace, and open contribution path—built by Auto-Bandit-RL-Proof-In-Sleep (ABRL).</p>
  <p class="paper-title"><strong>Paper.</strong> {html.escape(PAPER_TITLE)}</p>
  <div class="hero-actions">
    <a class="button primary" href="{href_from(page_path, 'declarations/index.html')}">Explore the Library</a>
    <a class="button" href="{href_from(page_path, 'ide/index.html')}">Open Live Formalization</a>
    <a class="button" href="{href_from(page_path, 'learning/index.html')}">Learn Bandit &amp; RL</a>
    <a class="button" href="{href_from(page_path, 'community/index.html')}">Contribute a Lemma</a>
    <a class="button" href="{GITHUB_REPO}">GitHub ↗</a>
  </div>
</section>

<section id="two-systems">
  <p class="eyebrow">Powered by two connected systems</p>
  <h2>One engine produces verified mathematics; one library makes it reusable.</h2>
  <div class="two-system-grid">
    <article class="info-card system-card"><span class="level-label">Research system</span><h3>ABRL Hierarchical Harness</h3><p>Fixed mathematical target → route planning → source grounding → formal proof-DAG decomposition → one-leaf proving → Lean compiler → reviewer-gated memory.</p><a href="{href_from(page_path, 'workflow/index.html')}">Inspect the ABRL harness →</a></article>
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

<section id="book-map">
  <p class="eyebrow">Formalized textbook map</p>
  <h2>Book map: ten routes through bandits and RL</h2>
  <p>Open any chapter to move from textbook intuition and mathematical statements to exact Lean declarations, module dependencies, compiled milestones, and explicitly recorded proof gaps.</p>
  {book_map}
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
    <article><span>02</span><h3>Clone the repository</h3><pre><code>git clone {GITHUB_REPO}.git
cd Auto-Bandit-RL-Proof-In-Sleep</code></pre></article>
    <article><span>03</span><h3>Run the proof gate</h3><pre><code>lake update
python3 tools/bandit.py check</code></pre></article>
  </div>
  <p><a class="button" href="{href_from(page_path, 'installation/index.html')}">Full installation guide</a></p>
</section>

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

<section id="progress">
  <h2>Progress without invented percentages</h2>
  <p>This chart counts the explicit milestones in the website's implementation map. It does not estimate what percentage of all bandit or RL mathematics has been formalized.</p>
  {render_diagram(page_path, 'progress.mmd', 'Status of the explicitly mapped theorem-route milestones', status_counts)}
</section>

<section id="reading-order">
  <h2>Recommended reading order</h2>
  <p>Students can take a short stochastic route through Foundations → Probability → ETC → UCB, a linear route through UCB → OFUL, an adversarial route through EXP3 → Tsallis-FTRL, or continue from Probability and OFUL stopping-time ideas into finite-horizon RL. Thompson sampling branches from posterior kernels.</p>
  {render_diagram(page_path, 'learning-path.mmd', 'Recommended learning path through the formalization')}
</section>

<section id="research-workspace">
  <h2>BanditRLlib and Live Formalization share one contribution language</h2>
  <p>The workspace renders editable LaTeX, loads reviewed LaTeX-to-Lean mappings, visualizes declaration dependencies, and can call the pinned Lean compiler through a loopback-only companion server. It can now export a versioned lemma packet for community review; a future authenticated compiler can submit that same packet directly as a proposed contribution.</p>
  <div class="hero-actions"><a class="button primary" href="{href_from(page_path, 'ide/index.html')}">Open Live Formalization</a><a class="button" href="{href_from(page_path, 'community/index.html#machine-contract')}">Inspect the contribution contract</a></div>
</section>
"""
    toc = [
        ("overview", "Overview"),
        ("two-systems", "ABRL + BanditRLlib"),
        ("three-roles", "Three ways to use BanditRLlib"),
        ("live-inventory", "Live inventory"),
        ("purpose", "Project purpose"),
        ("book-map", "Book map"),
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
    for result in results:
        declaration_links = []
        for name in result["declarations"]:
            decl = decl_by_name[name]
            declaration_links.append(
                f'<a href="{declaration_href(page_path, decl)}"><code>{html.escape(name)}</code></a>'
            )
        dependencies = ", ".join(
            f"<code>{html.escape(name)}</code>" for name in result.get("depends_on", [])
        ) or "—"
        missing = "<br>".join(html.escape(item) for item in result["missing"]) or "—"
        chapter = chapter_by_slug[result["chapter"]]
        result_rows.append(
            f"""
<tr id="{slugify(result['id'])}">
  <td><a href="#{slugify(result['id'])}">{html.escape(result['title'])}</a><br><code>{html.escape(result['id'])}</code></td>
  <td><a href="{href_from(page_path, f"chapters/{chapter['slug']}/index.html")}">{html.escape(chapter['short_title'])}</a></td>
  <td>{html.escape(result['informal'])}</td>
  <td>{"<br>".join(declaration_links) if declaration_links else "No local declaration yet"}</td>
  <td>{dependencies}</td>
  <td>{status_badge(result['status'])}</td>
  <td>{missing}</td>
</tr>"""
        )
    module_rows = []
    for module in modules:
        chapter = chapter_by_slug[module["chapter"]]
        module_status = "stated" if module["placeholder_count"] else ("compiled" if verified else "source")
        module_rows.append(
            f"""
<tr>
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
  <div class="table-wrap">
    <table>
      <thead><tr><th>Result</th><th>Chapter</th><th>Natural-language statement</th><th>Lean declaration</th><th>Dependencies</th><th>Status</th><th>Missing steps</th></tr></thead>
      <tbody>{''.join(result_rows)}</tbody>
    </table>
  </div>
</section>

<section id="dependencies">
  <h2>Major theorem dependencies</h2>
  <p>The graph shows the main teaching spine. Module pages list the exact import dependencies for every Lean source file.</p>
  {render_diagram(page_path, 'theorem-dependencies.mmd', 'Major local declaration and theorem-family dependencies')}
</section>

<section id="modules">
  <h2>Complete module inventory</h2>
  <p>Every project module is assigned to a teaching chapter. Open a module to see every indexed declaration, exact statement, docstring when present, source line, imports, and reverse dependencies.</p>
  <div class="table-wrap">
    <table>
      <thead><tr><th>Lean module</th><th>Teaching chapter</th><th>Declarations</th><th>Project imports</th><th>Build status</th><th>Source</th></tr></thead>
      <tbody>{''.join(module_rows)}</tbody>
    </table>
  </div>
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
    for decl in declarations:
        status = (
            "stated"
            if decl["placeholder"] or decl["kind"] == "axiom"
            else ("compiled" if verified else "source")
        )
        search = html.escape(
            f"{decl['full_name']} {decl['kind']} {decl['module']} {decl['file']} {decl['chapter_title']}".lower(),
            quote=True,
        )
        rows.append(
            f"""
<tr data-catalog-row data-search="{search}" data-kind="{decl['kind']}" data-status="{status}" data-chapter="{decl['chapter']}">
  <td><a href="{declaration_href(page_path, decl)}"><code>{html.escape(decl['full_name'])}</code></a></td>
  <td>{html.escape(KIND_LABELS.get(decl['kind'], decl['kind']))}</td>
  <td>{html.escape(decl['chapter_title'])}</td>
  <td><a href="{module_href(page_path, {'slug': decl['module_slug']})}"><code>{html.escape(decl['module'])}</code></a></td>
  <td>{status_badge(status)}</td>
  <td><a href="{source_url(decl['file'], decl['line'])}">{html.escape(decl['file'])}:{decl['line']}</a></td>
</tr>"""
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
  <p class="result-count" data-catalog-count></p>
</section>

<section id="declaration-table">
  <div class="table-wrap" data-catalog>
    <table>
      <thead><tr><th>Declaration</th><th>Kind</th><th>Chapter</th><th>Module</th><th>Status</th><th>Source</th></tr></thead>
      <tbody>{''.join(rows)}</tbody>
    </table>
  </div>
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

    for chapter in chapters:
        page_path = f"chapters/{chapter['slug']}/index.html"
        goals = render_list(chapter["learning_goals"])
        completion_contract = ""
        if chapter.get("completion_definition"):
            completion_contract = f"""
<section id="completion-contract">
  <h2>Completion contract</h2>
  <p>{html.escape(chapter['completion_definition'])}</p>
  <h3>Remaining blockers</h3>
  {render_list(chapter.get('completion_blockers', []))}
</section>
"""
        teaching = "".join(
            render_highlight(page_path, item, decl_by_name[item["full_name"]], verified)
            for item in highlights_by_chapter[chapter["slug"]]
        )
        if not teaching:
            teaching = '<p class="empty">No extended teaching note is registered for this chapter yet; the full module catalog remains available below.</p>'
        result_rows = []
        for result in results_by_chapter[chapter["slug"]]:
            links = [
                f'<a href="{declaration_href(page_path, decl_by_name[name])}"><code>{html.escape(name)}</code></a>'
                for name in result["declarations"]
            ]
            result_rows.append(
                f"<tr><td>{html.escape(result['title'])}</td><td>{status_badge(result['status'])}</td>"
                f"<td>{'<br>'.join(links) if links else 'No local declaration yet'}</td>"
                f"<td>{'<br>'.join(html.escape(item) for item in result['missing']) or '—'}</td></tr>"
            )
        module_rows = "".join(
            f"<tr><td><a href=\"{module_href(page_path, module)}\"><code>{html.escape(module['name'])}</code></a></td>"
            f"<td>{len(module['declarations']):,}</td><td>{len(module['imports']):,}</td>"
            f"<td>{status_badge('stated' if module['placeholder_count'] else ('compiled' if verified else 'source'))}</td></tr>"
            for module in modules_by_chapter[chapter["slug"]]
        )
        body = f"""
<section class="hero" id="chapter">
  <p class="eyebrow">Teaching chapter · {status_badge(chapter['status'])}</p>
  <h1 class="page-title">{html.escape(chapter['title'])}</h1>
  <p class="lede">{html.escape(chapter['summary'])}</p>
</section>

<section id="orientation">
  <h2>Orientation</h2>
  <p><strong>Who should read this.</strong> {html.escape(chapter['audience'])}</p>
  <h3>Learning goals</h3>
  {goals}
</section>

{completion_contract}

<section id="teaching-notes">
  <h2>Natural-language and Lean side by side</h2>
  <p>The mathematical readings are explanatory summaries. The exact generated Lean statement and its source link remain authoritative for hypotheses, types, constants, and indexing.</p>
  {teaching}
</section>

<section id="milestones">
  <h2>Chapter implementation status</h2>
  <div class="table-wrap"><table><thead><tr><th>Milestone</th><th>Status</th><th>Lean declaration</th><th>Remaining gap</th></tr></thead><tbody>{''.join(result_rows)}</tbody></table></div>
</section>

<section id="open-gaps">
  <h2>Open boundaries</h2>
  {render_list(chapter['open_gaps'])}
</section>

<section id="module-list">
  <h2>All Lean modules in this chapter</h2>
  <div class="table-wrap"><table><thead><tr><th>Module</th><th>Declarations</th><th>Project imports</th><th>Status</th></tr></thead><tbody>{module_rows}</tbody></table></div>
</section>
"""
        toc = [
            ("chapter", "Chapter"),
            ("orientation", "Orientation"),
        ]
        if completion_contract:
            toc.append(("completion-contract", "Completion contract"))
        toc.extend([
            ("teaching-notes", "Teaching notes"),
            ("milestones", "Status"),
            ("open-gaps", "Open boundaries"),
            ("module-list", "Modules"),
        ])
        write_page(
            output,
            page_path,
            layout(page_path, chapter["title"], body, toc, "chapters", verified, generated_at),
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
  <h1 class="page-title">{html.escape(module['name'])}</h1>
  <p class="lede">{html.escape(module['docstring']) if module['docstring'] else 'Generated source map for this Lean module.'}</p>
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
    body = f"""
<section class="hero" id="learning">
  <p class="eyebrow">A student-first route</p>
  <h1 class="page-title">How to read the formalization</h1>
  <p class="lede">You do not need to read thousands of declarations in source order. Begin with the deterministic language, learn the probability interfaces, then follow one algorithm route from assumptions to a compiled endpoint.</p>
</section>

<section id="path">
  <h2>Recommended path</h2>
  {render_diagram(page_path, 'learning-path.mmd', 'Recommended learning path through the chapters')}
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
  <p>Each chapter is a clickable bridge from mathematical exposition to the exact Lean modules and declarations that implement it.</p>
  {cards}
</section>
"""
    toc = [("learning", "Reading guide"), ("path", "Recommended path"), ("lean-translation", "Lean ideas"), ("book-map", "Book map")]
    write_page(
        output,
        page_path,
        layout(page_path, "Learning path", body, toc, "chapters", verified, generated_at),
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
  <p class="lede">Project authorship and community contribution are different records. The six paper authors are listed in the requested order; future community contributors appear separately with their accepted work and preferred credit.</p>
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
  <pre><code>git clone {GITHUB_REPO}.git
cd Auto-Bandit-RL-Proof-In-Sleep
lake update</code></pre>
  <p><code>lake update</code> fetches the pinned Mathlib dependency from <code>lakefile.lean</code>. The first run may take several minutes.</p>
</section>

<section id="verify">
  <h2>3. Run the mandatory Lean gate</h2>
  <pre><code>python3 tools/bandit.py check</code></pre>
  <p>On Windows, <code>py -3 tools/bandit.py check</code> is equivalent when the Python launcher is installed. The gate runs <code>lake build</code>, builds <code>Tests</code>, and scans local Lean files for forbidden placeholders.</p>
  <div class="callout warning"><strong>Do not skip this step.</strong> A theorem is marked compiled on the website only after the project gate passes for the source snapshot being published.</div>
</section>

<section id="website">
  <h2>4. Build and preview the literate site</h2>
  <pre><code>python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
python3 -m http.server 8000 --directory website/_site</code></pre>
  <p>Open <code>http://localhost:8000/</code>. The static Research IDE is at <code>/ide/</code>; local Lean compilation requires the loopback-only companion server documented on that page.</p>
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
    <a class="button" href="{href_from(page_path, 'ide/index.html')}">Draft in Live Formalization</a>
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
    <pre class="contract-example"><code>{{
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
  <p class="lede">BanditRLlib is built from the public canonical ABRL repository. Normal declaration links open the exact source on <code>main</code>; documentation-only mirrors may use this page as an explicit snapshot boundary.</p>
</section>
<section id="available">
  <h2>What is public</h2>
  <ul><li>the Lean source and exact declaration signatures;</li><li>the searchable BanditRLlib catalog and implementation map;</li><li>student-facing mathematical explanations and honest route status;</li><li>contribution issues, lemma packets, governance, and review history;</li><li>the static workspace and local verified-mode server.</li></ul>
</section>
<section id="boundary">
  <h2>Verification and credential boundary</h2>
  <p>API keys, local editor requests, temporary compilation files, ignored build caches, and regenerable private working artifacts are never embedded in the static Pages output. A proposal becomes integrated only after reviewer approval and the full repository gate on <code>main</code>.</p>
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


def build_workflow(output: Path, verified: bool, generated_at: str) -> None:
    page_path = "workflow/index.html"
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
  <h2>Hierarchical loop</h2>
  {render_diagram(page_path, 'automation-workflow.mmd', 'Upper, middle, Lean worker, reviewer, and deterministic-gate sequence')}
</section>

<section id="commands">
  <h2>Reproducible gates</h2>
  <pre class="lean-code"><code>python3 tools/bandit.py blueprint-refresh &lt;task-id&gt;
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
    toc = [("workflow", "Workflow"), ("contract", "Contract"), ("roles", "Roles"), ("commands", "Gates"), ("failure-policy", "Failure policy")]
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

<section id="other-sources">
  <h2>Mathematical and software sources</h2>
  <p>The repository's full literature, Mathlib, LML, automation, and proof-system attribution ledger is maintained in <a href="{source_url('docs/attribution.md')}"><code>docs/attribution.md</code></a> and <a href="{source_url('NOTICE.md')}"><code>NOTICE.md</code></a>.</p>
  <p>Theorem cards summarize external results for retrieval. They do not transfer authorship and do not become local proof certificates until an import or local proof compiles.</p>
</section>
"""
    toc = [("attribution", "Attribution"), ("lean-ridgelet", "Lean-Ridgelet"), ("statsmllib", "StatsMLlib"), ("other-sources", "Other sources")]
    write_page(
        output,
        page_path,
        layout(page_path, "Attribution", body, toc, "overview", verified, generated_at),
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
    readme = f"""# BanditRLlib

This generated artifact accompanies the community-facing, textbook-style
BanditRLlib website produced by the ABRL research project.

Website: <{PUBLIC_SITE_URL}/>
Canonical repository: <{GITHUB_REPO}>

## Three ways to use BanditRLlib

1. **Learn:** follow a Lean-aligned textbook path through bandit, probability,
   optimization, stopping-time, and finite-horizon RL mathematics.
2. **Browse:** search {manifest['declaration_count']:,} exact Lean definitions,
   theorems, and lemmas across {manifest['module_count']:,} modules.
3. **Contribute:** propose a sourced result through an issue or versioned lemma
   packet; Live Formalization uses the same machine-readable contract.

## Current snapshot

The generated site was built from {source_note}. Compiled, partial, planned,
blocked, and community-proposal states remain distinct. The public repository
is the source of truth for Lean code, documentation, contribution metadata,
and deployment. Generated site output includes only allowlisted public files.

Start with [CONTRIBUTING.md](CONTRIBUTING.md), the
[community page]({PUBLIC_SITE_URL}/community/), or the
[JSON Schema](community/contribution.schema.json). Public packets are validated
before deployment; only the full upstream project gate can mark a result
integrated.

## Attribution

The implementation-map organization is inspired by **Sho Sonoda's**
[Lean-Ridgelet](https://github.com/shosonoda/lean-ridgelet) and its
[Blueprint](https://shosonoda.github.io/lean-ridgelet/). The community landing
page and book-to-library navigation also take organizational inspiration from
[StatsMLlib](https://statsmllib.github.io/) by the
[Lean Models, Decisions, and Statistics community](https://github.com/Lean-MoDS/StatsMLlib).
Both references are attribution for inspiration only and do not imply
participation, endorsement, or maintenance of BanditRLlib. No template, stylesheet,
or source file was copied from either project.

## License

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
    args = parser.parse_args()
    global PUBLIC_BASE_URL, SITE_CHAPTERS
    PUBLIC_BASE_URL = args.public_base_url.rstrip("/")
    output = args.output.resolve()
    if output == ROOT.resolve() or ROOT.resolve() not in output.parents:
        raise SystemExit(f"refusing to build outside the repository: {output}")

    chapters = load_json(CONTENT_DIR / "chapters.json")["chapters"]
    people = load_json(CONTENT_DIR / "contributors.json")
    authors = people["authors"]
    community_contributors = people.get("community_contributors", [])
    SITE_CHAPTERS = chapters
    highlights = load_json(CONTENT_DIR / "highlights.json")["highlights"]
    results = load_json(CONTENT_DIR / "results.json")["results"]
    roadmap = load_json(ROOT / "research-wiki" / "theory-tree" / "lean-route-roadmap.json")

    modules = scan_lean_tree()
    assign_chapters(modules, chapters)
    declarations = [decl for module in modules for decl in module["declarations"]]
    decl_by_name = validate_content(declarations, highlights, results)
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
    build_roadmap(output, results, roadmap, decl_by_name, args.lean_verified, generated_at)
    build_workflow(output, args.lean_verified, generated_at)
    build_attribution(output, args.lean_verified, generated_at)
    build_source_access(output, args.lean_verified, generated_at)
    build_search_index(output, declarations)

    source_commit, source_dirty = git_source_state()
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
        "public_snapshot": bool(PUBLIC_BASE_URL),
        "public_base_url": PUBLIC_BASE_URL,
        "source_commit": source_commit,
        "source_dirty": source_dirty,
    }
    write_text_lf(output / "site-manifest.json", json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
    build_public_repository_readme(output, manifest)
    print(json.dumps(manifest, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
