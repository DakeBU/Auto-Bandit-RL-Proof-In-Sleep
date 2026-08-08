#!/usr/bin/env python3
"""Build ABRL's Blueprint-style literate formalization website."""

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
DEFAULT_OUTPUT = SITE_DIR / "_site"

GITHUB_REPO = "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep"
SOURCE_BRANCH = "main"

STATUS_LABELS = {
    "compiled": "Compiled",
    "partial": "Partial",
    "planned": "Planned",
    "blocked": "Blocked",
    "stated": "Stated, proof incomplete",
    "source": "Source indexed",
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
    nav_items = [
        ("overview", "Overview", "index.html"),
        ("map", "Implementation map", "implementation-map/index.html"),
        ("chapters", "Chapters", "learning/index.html"),
        ("catalog", "Declarations", "declarations/index.html"),
        ("ide", "Research IDE", "ide/index.html"),
        ("roadmap", "Roadmap", "roadmap/index.html"),
        ("workflow", "Workflow", "workflow/index.html"),
    ]
    nav = "".join(
        f'<a href="{href_from(page_path, target)}"'
        + (' aria-current="page"' if key == current else "")
        + f">{label}</a>"
        for key, label, target in nav_items
    )
    toc_html = (
        '<aside class="side-nav" aria-label="On this page"><strong>On this page</strong>'
        + "".join(f'<a href="#{html.escape(anchor)}">{html.escape(label)}</a>' for anchor, label in toc)
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
  <meta name="description" content="Literate Lean formalization of bandit and reinforcement-learning proofs in ABRL.">
  <title>{html.escape(title)} · ABRL Formalization</title>
  <link rel="stylesheet" href="{root}/static/site.css?v=20260806">
  {mathjax}
</head>
<body data-site-root="{root}">
  <a class="skip-link" href="#main-content">Skip to content</a>
  <header class="site-header">
    <div class="header-inner">
      <a class="brand" href="{href_from(page_path, 'index.html')}">
        <span class="brand-mark" aria-hidden="true">A</span>
        <span>ABRL Formalization</span>
      </a>
      <nav class="primary-nav" aria-label="Primary">{nav}</nav>
      <div class="search-shell">
        <label class="empty" for="global-search">Search Lean declarations</label>
        <input id="global-search" class="global-search" data-global-search type="search" placeholder="Search declarations…" autocomplete="off">
        <ul class="search-results" data-global-results hidden></ul>
      </div>
      <div class="theme-switcher" aria-label="Site style">
        <button type="button" data-theme-choice="blueprint" aria-pressed="true">Blueprint</button>
        <button type="button" data-theme-choice="modern" aria-pressed="false">Modern</button>
        <button type="button" data-theme-choice="bold" aria-pressed="false">Bold</button>
      </div>
    </div>
  </header>
  <div class="verification-strip{verification_class}">{html.escape(verification)}</div>
  <div class="page-shell">
    <main class="page-main" id="main-content">{body}</main>
    {toc_html}
  </div>
  <footer class="site-footer">
    <div class="footer-inner">
      <p>Generated from the current Lean sources at {html.escape(generated_at)}. The declaration statement and source link are authoritative when prose is abbreviated.</p>
      <p>Organization inspired by <a href="https://github.com/shosonoda/lean-ridgelet">Sho Sonoda's Lean-Ridgelet</a>; no participation or endorsement is implied. <a href="{href_from(page_path, 'attribution/index.html')}">Attribution details</a>.</p>
    </div>
  </footer>
  <script src="{root}/static/site.js?v=20260806"></script>{extra_script_tags}
</body>
</html>
"""


def write_page(output: Path, page_path: str, content: str) -> None:
    target = output / Path(page_path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8", newline="\n")


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
    results: list[dict[str, Any]],
    verified: bool,
    generated_at: str,
) -> None:
    page_path = "index.html"
    counts = Counter(decl["kind"] for decl in declarations)
    status_counts = Counter(result["status"] for result in results)
    placeholder_count = sum(1 for decl in declarations if decl["placeholder"])
    chapter_cards = "".join(
        f"""
<article class="chapter-card">
  {status_badge(chapter['status'])}
  <h3><a href="{href_from(page_path, f"chapters/{chapter['slug']}/index.html")}">{html.escape(chapter['title'])}</a></h3>
  <p>{html.escape(chapter['summary'])}</p>
</article>"""
        for chapter in chapters
    )
    body = f"""
<section class="hero" id="overview">
  <p class="eyebrow">Verified mathematics · readable explanations · honest gaps</p>
  <h1>A map from bandit theory to Lean.</h1>
  <p class="lede">Auto-Bandit-RL-Proof-In-Sleep turns literature targets into explicit assumptions, proof-DAG leaves, compiled Lean declarations, and explanations that a student can read beside the formal statement.</p>
  <div class="hero-actions">
    <a class="button primary" href="{href_from(page_path, 'learning/index.html')}">Start the guided reading path</a>
    <a class="button" href="{href_from(page_path, 'implementation-map/index.html')}">Open the implementation map</a>
    <a class="button" href="{href_from(page_path, 'ide/index.html')}">Try the Research IDE</a>
  </div>
</section>

<section id="live-inventory">
  <h2>Live source inventory</h2>
  <p>The numbers below are generated from the current <code>BanditRLProof/</code> tree at build time. Private proof helpers remain searchable but are identified as internal.</p>
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
  <p>The current tree is no longer only a finite-bandit foundation. It contains concrete ETC, UCB, Thompson, EXP3, and Tsallis endpoints; an OFUL chain reaching self-normalized confidence, one-policy all-time events, expected-average consistency, and random-horizon bounds; and a large finite-horizon RL development from Bellman recursion through adaptive empirical confidence, realized behavior consistency, causal laws, and genuine <code>hittingAfter</code> stopping results. Complete UCB-VI, KL-UCB, full BwK, preference, federated, and several modern routes remain partial, planned, or blocked at named interfaces.</p>
  {render_diagram(page_path, 'system-architecture.mmd', 'The ABRL system from literature evidence to a Lean-gated teaching site')}
</section>

<section id="chapters">
  <h2>{len(chapters)} teaching chapters</h2>
  <p>Each chapter explains major declarations in plain English, shows a mathematical reading, gives the exact Lean statement, and links back to the complete module catalog.</p>
  <div class="chapter-grid">{chapter_cards}</div>
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
  <h2>A first researcher-facing IDE loop</h2>
  <p>The new workspace renders editable LaTeX, loads reviewed LaTeX-to-Lean mappings, visualizes declaration dependencies, and can call the repository's pinned Lean compiler through a loopback-only companion server. Static deployments keep the reading and visualization features but never pretend to execute arbitrary Lean.</p>
  <a class="button primary" href="{href_from(page_path, 'ide/index.html')}">Open the Research IDE prototype</a>
</section>
"""
    toc = [
        ("overview", "Overview"),
        ("live-inventory", "Live inventory"),
        ("purpose", "Project purpose"),
        ("chapters", "Teaching chapters"),
        ("progress", "Progress"),
        ("reading-order", "Reading order"),
        ("research-workspace", "Research IDE"),
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
            ("teaching-notes", "Teaching notes"),
            ("milestones", "Status"),
            ("open-gaps", "Open boundaries"),
            ("module-list", "Modules"),
        ]
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
                teaching_link = (
                    f'<a href="{href_from(page_path, f"chapters/{teaching["chapter"]}/index.html#{declaration["anchor"]}-teaching")}">'
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
    cards = "".join(
        f"""
<article class="chapter-card">
  {status_badge(chapter['status'])}
  <h3><a href="{href_from(page_path, f"chapters/{chapter['slug']}/index.html")}">{html.escape(chapter['title'])}</a></h3>
  <p>{html.escape(chapter['summary'])}</p>
  <p><strong>Audience.</strong> {html.escape(chapter['audience'])}</p>
</article>"""
        for chapter in chapters
    )
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

<section id="chapters">
  <h2>Chapter guide</h2>
  <div class="chapter-grid">{cards}</div>
</section>
"""
    toc = [("learning", "Reading guide"), ("path", "Recommended path"), ("lean-translation", "Lean ideas"), ("chapters", "Chapters")]
    write_page(
        output,
        page_path,
        layout(page_path, "Learning path", body, toc, "chapters", verified, generated_at),
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
    (output / "ide-data.json").write_text(
        json.dumps({"items": payload}, ensure_ascii=False, separators=(",", ":")),
        encoding="utf-8",
        newline="\n",
    )

    body = f"""
<section class="hero" id="research-ide">
  <p class="eyebrow">Research workspace prototype</p>
  <h1 class="page-title">LaTeX and Lean, in one live notebook.</h1>
  <p class="lede">Explore a reviewed mathematical statement beside its exact Lean declaration, render the formula immediately, inspect the proof dependency tree, and—when the local companion server is running—send an editable snippet to the repository's real Lean toolchain.</p>
  <div class="hero-actions">
    <a class="button primary" href="#workspace">Open the workspace</a>
    <a class="button" href="{href_from(page_path, 'workflow/index.html')}">Read the verification workflow</a>
  </div>
</section>

<section id="mode-boundary">
  <h2>Two honest execution modes</h2>
  <div class="card-grid">
    <div class="info-card"><h3>Static / shared site</h3><p>LaTeX preview, curated LaTeX-to-Lean mappings, source navigation, and dependency trees work in any browser. Arbitrary Lean code is not executed.</p></div>
    <div class="info-card"><h3>Local verified mode</h3><p><code>ide_server.py</code> binds to loopback and invokes <code>lake env lean</code> in a temporary directory. Diagnostics are returned to this page without modifying source files.</p></div>
    <div class="info-card"><h3>Future IDE boundary</h3><p>Proof-state streaming, an LSP session, semantic LaTeX synthesis, tactic suggestions, and collaborative persistence remain roadmap work—not features claimed by this prototype.</p></div>
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
    <button class="button" type="button" data-ide-scaffold>Make safe draft scaffold</button>
    <label class="ide-toggle"><input type="checkbox" data-ide-auto> Auto-compile after edits (opt-in)</label>
  </div>
  <div class="ide-grid" data-ide-app data-ide-data="{href_from(page_path, 'ide-data.json')}">
    <article class="ide-pane">
      <header><div><span class="ide-step">01</span><h3>Mathematical statement</h3></div><span class="status source" data-translation-status>Reviewed mapping</span></header>
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
</section>

<section id="architecture">
  <h2>From prototype to a researcher IDE</h2>
  <p>The maintainable design keeps the browser pleasant and the certificate boundary narrow: editing and visualization live in the front end, while only a loopback companion process is allowed to call the repository's pinned Lean toolchain.</p>
  {render_diagram(page_path, 'research-ide-loop.mmd', 'Research IDE loop: reviewed mathematics, local Lean verification, and source-synchronized visualization')}
  <div class="card-grid">
    <div class="info-card"><h3>Next: proof states</h3><p>Attach a persistent Lean language-server session so cursor position can reveal goals, hypotheses, and tactic state without recompiling a whole snippet.</p></div>
    <div class="info-card"><h3>Next: semantic translation</h3><p>Generate candidate Lean from LaTeX with explicit provenance and require compilation plus human review before labeling a mapping verified.</p></div>
    <div class="info-card"><h3>Next: research graph</h3><p>Combine elaborated declaration dependencies, task obligations, paper references, and counterexample records into one navigable graph.</p></div>
  </div>
</section>
"""
    toc = [
        ("research-ide", "Research IDE"),
        ("mode-boundary", "Execution modes"),
        ("workspace", "Workspace"),
        ("architecture", "Architecture and next steps"),
    ]
    write_page(
        output,
        page_path,
        layout(
            page_path,
            "Research IDE",
            body,
            toc,
            "ide",
            verified,
            generated_at,
            extra_scripts=("static/ide.js?v=20260806",),
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
    body = """
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

<section id="other-sources">
  <h2>Mathematical and software sources</h2>
  <p>The repository's full literature, Mathlib, LML, automation, and proof-system attribution ledger is maintained in <a href="https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/main/docs/attribution.md"><code>docs/attribution.md</code></a> and <a href="https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/main/NOTICE.md"><code>NOTICE.md</code></a>.</p>
  <p>Theorem cards summarize external results for retrieval. They do not transfer authorship and do not become local proof certificates until an import or local proof compiles.</p>
</section>
"""
    toc = [("attribution", "Attribution"), ("lean-ridgelet", "Lean-Ridgelet"), ("other-sources", "Other sources")]
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
    (output / "search-index.json").write_text(
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")),
        encoding="utf-8",
        newline="\n",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--lean-verified",
        action="store_true",
        help="mark non-placeholder local declarations compiled; run only after the Lean gate succeeds",
    )
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT.resolve() or ROOT.resolve() not in output.parents:
        raise SystemExit(f"refusing to build outside the repository: {output}")

    chapters = load_json(CONTENT_DIR / "chapters.json")["chapters"]
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
    (output / ".nojekyll").write_text("", encoding="utf-8")

    build_index(output, modules, declarations, chapters, results, args.lean_verified, generated_at)
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
    build_research_ide(output, highlights, decl_by_name, args.lean_verified, generated_at)
    build_roadmap(output, results, roadmap, decl_by_name, args.lean_verified, generated_at)
    build_workflow(output, args.lean_verified, generated_at)
    build_attribution(output, args.lean_verified, generated_at)
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
        "highlight_count": len(highlights),
        "ide_mapping_count": len(highlights),
        "milestone_count": len(results),
        "milestone_status_counts": dict(sorted(Counter(result["status"] for result in results).items())),
        "source_commit": os.environ.get("GITHUB_SHA", ""),
    }
    (output / "site-manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(manifest, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
