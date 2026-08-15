#!/usr/bin/env python3
"""Check the generated BanditRLlib site, ABRL mappings, and publication contract."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit


SCRIPT_DIR = Path(__file__).resolve().parent
SITE_DIR = SCRIPT_DIR.parent
ROOT = SITE_DIR.parent
DEFAULT_OUTPUT = SITE_DIR / "_site"
PAPER_TITLE = (
    "ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library "
    "for Bandit and Reinforcement Learning Theory"
)
EXPECTED_AUTHORS = ["Dake Bu", "Ji Cheng", "Bo Xue", "Atsushi Nitanda", "Hau-San Wong", "Qingfu Zhang"]


class LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.links: list[tuple[str, str]] = []
        self.ids: set[str] = set()
        self.mermaid_count = 0
        self.mathjax_count = 0
        self.source_link_count = 0
        self.site_sidebar_count = 0
        self.book_nav_link_count = 0
        self.book_chapter_card_count = 0
        self.contributor_card_count = 0
        self.theorem_panel_count = 0
        self.math_statement_count = 0
        self.math_fallback_count = 0
        self.math_tex_count = 0
        self.teaching_grid_count = 0
        self.lean_code_count = 0
        self.source_guide_count = 0
        self.algorithm_flow_count = 0
        self.source_theorem_card_count = 0
        self.source_boundary_count = 0
        self.nested_math_errors = 0
        self.math_tex_sources: list[str] = []
        self._stack: list[tuple[str, set[str]]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = {key: value or "" for key, value in attrs}
        if values.get("id"):
            self.ids.add(values["id"])
        classes = set(values.get("class", "").split())
        if "math-statement" in classes:
            self.math_statement_count += 1
        if "math-fallback" in classes:
            self.math_fallback_count += 1
        if "math-tex" in classes:
            self.math_tex_count += 1
            self.math_tex_sources.append("")
        if "theorem-panel" in classes:
            self.theorem_panel_count += 1
        if "teaching-grid" in classes:
            self.teaching_grid_count += 1
        if "lean-code" in classes:
            self.lean_code_count += 1
        if "source-guide" in classes:
            self.source_guide_count += 1
        if "algorithm-flow" in classes:
            self.algorithm_flow_count += 1
        if "source-theorem-card" in classes:
            self.source_theorem_card_count += 1
        if "source-boundary" in classes:
            self.source_boundary_count += 1
        if any("math-statement" in parent_classes for _parent_tag, parent_classes in self._stack):
            if "teaching-grid" in classes or "lean-code" in classes:
                self.nested_math_errors += 1
        if "mermaid" in classes:
            self.mermaid_count += 1
        if "site-sidebar" in classes:
            self.site_sidebar_count += 1
        if "book-nav-link" in classes:
            self.book_nav_link_count += 1
        if "book-chapter-card" in classes:
            self.book_chapter_card_count += 1
        if "contributor-card" in classes:
            self.contributor_card_count += 1
        for attr in ("href", "src"):
            if values.get(attr):
                self.links.append((attr, values[attr]))
        if "cdn.jsdelivr.net/npm/mathjax" in values.get("src", ""):
            self.mathjax_count += 1
        if (
            ("/blob/" in values.get("href", "") and "/BanditRLProof" in values.get("href", ""))
            or "/source-access/" in values.get("href", "")
        ):
            self.source_link_count += 1
        if tag not in {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}:
            self._stack.append((tag, classes))

    def handle_endtag(self, tag: str) -> None:
        for index in range(len(self._stack) - 1, -1, -1):
            if self._stack[index][0] == tag:
                del self._stack[index:]
                break

    def handle_data(self, data: str) -> None:
        if self.math_tex_sources and any("math-tex" in classes for _tag, classes in self._stack):
            self.math_tex_sources[-1] += data


def parse_pages(output: Path) -> dict[Path, LinkCollector]:
    parsed: dict[Path, LinkCollector] = {}
    for path in sorted(output.rglob("*.html")):
        collector = LinkCollector()
        collector.feed(path.read_text(encoding="utf-8"))
        parsed[path.resolve()] = collector
    return parsed


def is_external(value: str) -> bool:
    split = urlsplit(value)
    return split.scheme in {"http", "https", "mailto", "tel", "data", "javascript"} or value.startswith("//")


def check_internal_links(output: Path, pages: dict[Path, LinkCollector]) -> list[str]:
    errors: list[str] = []
    output_resolved = output.resolve()
    for page, collector in pages.items():
        for attr, value in collector.links:
            if is_external(value):
                continue
            split = urlsplit(value)
            raw_path = unquote(split.path)
            if not raw_path:
                target = page
            elif raw_path.startswith("/"):
                target = output_resolved / raw_path.lstrip("/")
            else:
                target = (page.parent / raw_path).resolve()
            if target.is_dir():
                target = target / "index.html"
            try:
                target.relative_to(output_resolved)
            except ValueError:
                errors.append(f"{page.relative_to(output)}: {attr} escapes output root: {value}")
                continue
            if not target.exists():
                errors.append(f"{page.relative_to(output)}: missing {attr} target {value}")
                continue
            if split.fragment and target.suffix.lower() == ".html":
                target_collector = pages.get(target.resolve())
                if target_collector is None:
                    errors.append(f"{page.relative_to(output)}: unparsed HTML target {value}")
                elif unquote(split.fragment) not in target_collector.ids:
                    errors.append(
                        f"{page.relative_to(output)}: missing anchor #{split.fragment} in {target.relative_to(output)}"
                    )
    return errors


def check_markdown_links(path: Path) -> list[str]:
    errors: list[str] = []
    text = path.read_text(encoding="utf-8")
    for match in re.finditer(r"\[[^\]]+\]\(([^)]+)\)", text):
        value = match.group(1).strip()
        if is_external(value) or value.startswith("#"):
            continue
        value = value.split("#", 1)[0]
        if not value:
            continue
        target = (path.parent / value).resolve()
        if not target.exists():
            errors.append(f"{path.relative_to(ROOT)}: missing Markdown target {match.group(1)}")
    return errors


def check_diagram_sources() -> list[str]:
    errors: list[str] = []
    allowed_starts = ("flowchart", "graph", "sequenceDiagram", "pie", "classDiagram", "stateDiagram")
    for path in sorted((SITE_DIR / "diagrams").glob("*.mmd")):
        source = path.read_text(encoding="utf-8").strip()
        if not source.startswith(allowed_starts):
            errors.append(f"{path.relative_to(ROOT)}: unrecognized Mermaid diagram start")
        if "{{" in source and path.name != "progress.mmd":
            errors.append(f"{path.relative_to(ROOT)}: unresolved template marker")
    return errors


def check_workflow() -> list[str]:
    path = ROOT / ".github" / "workflows" / "documentation.yml"
    if not path.exists():
        return ["missing .github/workflows/documentation.yml"]
    text = path.read_text(encoding="utf-8")
    required = [
        "python3 tools/bandit.py check",
        "python3 website/scripts/build_site.py --lean-verified",
        "python3 website/scripts/check_site.py",
        "actions/configure-pages@",
        "actions/upload-pages-artifact@",
        "actions/deploy-pages@",
        "path: website/_site",
    ]
    return [f"documentation workflow missing: {item}" for item in required if item not in text]


def check_ide_server() -> list[str]:
    path = SITE_DIR / "scripts" / "ide_server.py"
    formalizer_path = ROOT / "tools" / "bandit_formalizer.py"
    if not path.exists():
        return ["missing website/scripts/ide_server.py"]
    if not formalizer_path.exists():
        return ["missing tools/bandit_formalizer.py"]
    text = path.read_text(encoding="utf-8") + "\n" + formalizer_path.read_text(encoding="utf-8")
    required = [
        'default="127.0.0.1"',
        '"/api/compile"',
        '"/api/formalize"',
        '"lake", "env", "lean"',
        "TemporaryDirectory",
        "loopback-only",
        "ABRL_FORMALIZER_API_KEY",
    ]
    return [f"IDE server missing safety/compile contract: {item}" for item in required if item not in text]


def check_branding_and_formalizer(output: Path, manifest: dict[str, object]) -> list[str]:
    errors: list[str] = []
    index_path = output / "index.html"
    ide_path = output / "ide" / "index.html"
    combined = "\n".join(
        path.read_text(encoding="utf-8") for path in (index_path, ide_path) if path.exists()
    )
    for required in ("BanditRLlib", PAPER_TITLE, "BanditRLProof"):
        if required not in combined:
            errors.append(f"public identity text missing: {required}")
    if manifest.get("author_count") != len(EXPECTED_AUTHORS):
        errors.append(f"author_count must be {len(EXPECTED_AUTHORS)}")
    contributors = json.loads((SITE_DIR / "content" / "contributors.json").read_text(encoding="utf-8"))
    actual_authors = [entry.get("name") for entry in contributors.get("authors", [])]
    if actual_authors != EXPECTED_AUTHORS:
        errors.append("author order does not match the ABRL paper")
    schema = json.loads((output / "community" / "contribution.schema.json").read_text(encoding="utf-8"))
    properties = schema.get("properties", {})
    lean_properties = properties.get("lean", {}).get("properties", {})
    for field in ("banditrl_reused", "mathlib_candidates", "lml_candidates"):
        if field not in lean_properties:
            errors.append(f"community schema missing formalization field: {field}")
    if "unresolved_proof_obligations" not in properties:
        errors.append("community schema missing formalization field: unresolved_proof_obligations")
    ide_js = (output / "static" / "ide.js").read_text(encoding="utf-8")
    if "ABRL_FORMALIZER_API_KEY" in ide_js or re.search(r"(?:api[_-]?key|authorization)\s*[:=]", ide_js, re.I):
        errors.append("static IDE JavaScript appears to contain a provider credential interface")
    if "data-ide-formalize" not in combined or "data-candidate-obligations" not in combined:
        errors.append("Live Formalization candidate UI is incomplete")
    return errors


def check_community_contract(output: Path, manifest: dict[str, object]) -> list[str]:
    errors: list[str] = []
    schema_path = output / "community" / "contribution.schema.json"
    registry_path = output / "community" / "registry.json"
    validator_path = output / "scripts" / "build_community_registry.py"
    workflow_path = output / ".github" / "workflows" / "community-pages.yml"
    for path in (schema_path, registry_path, validator_path, workflow_path):
        if not path.exists():
            errors.append(f"missing public community artifact: {path.relative_to(output)}")
    if not schema_path.exists() or not registry_path.exists():
        return errors
    try:
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
        registry = json.loads(registry_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        errors.append(f"invalid community JSON: {error}")
        return errors
    if schema.get("properties", {}).get("schema_version", {}).get("const") != "1.1":
        errors.append("community schema does not declare schema_version 1.1")
    entries = registry.get("entries")
    if not isinstance(entries, list):
        errors.append("community registry entries must be an array")
    elif len(entries) != manifest.get("community_entry_count"):
        errors.append(
            f"community registry count {len(entries)} != manifest community_entry_count "
            f"{manifest.get('community_entry_count')}"
        )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--allow-unverified", action="store_true")
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.exists():
        raise SystemExit(f"site output does not exist: {output}")

    errors: list[str] = []
    manifest_path = output / "site-manifest.json"
    if not manifest_path.exists():
        errors.append("missing site-manifest.json")
        manifest = {}
    else:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if not args.allow_unverified and not manifest.get("lean_verified"):
        errors.append("site was not built with --lean-verified")

    pages = parse_pages(output)
    errors.extend(check_internal_links(output, pages))
    errors.extend(check_markdown_links(ROOT / "README.md"))
    errors.extend(check_markdown_links(SITE_DIR / "README.md"))
    errors.extend(check_diagram_sources())
    errors.extend(check_workflow())
    errors.extend(check_ide_server())
    errors.extend(check_community_contract(output, manifest))
    errors.extend(check_branding_and_formalizer(output, manifest))

    expected_pages = {
        output / "index.html",
        output / "implementation-map" / "index.html",
        output / "declarations" / "index.html",
        output / "ide" / "index.html",
        output / "community" / "index.html",
        output / "contributors" / "index.html",
        output / "installation" / "index.html",
        output / "learning" / "index.html",
        output / "roadmap" / "index.html",
        output / "workflow" / "index.html",
        output / "attribution" / "index.html",
        output / "source-access" / "index.html",
    }
    for expected in expected_pages:
        if not expected.exists():
            errors.append(f"missing required page: {expected.relative_to(output)}")

    expected_chapter_count = len(
        json.loads((SITE_DIR / "content" / "chapters.json").read_text(encoding="utf-8"))["chapters"]
    )
    for page, collector in pages.items():
        if collector.site_sidebar_count != 1:
            errors.append(
                f"{page.relative_to(output)}: expected one site sidebar, found {collector.site_sidebar_count}"
            )
        if collector.book_nav_link_count != expected_chapter_count:
            errors.append(
                f"{page.relative_to(output)}: book navigation has {collector.book_nav_link_count} chapter links, "
                f"expected {expected_chapter_count}"
            )

    for relative in (Path("index.html"), Path("learning/index.html")):
        collector = pages.get((output / relative).resolve())
        if collector and collector.book_chapter_card_count != expected_chapter_count:
            errors.append(
                f"{relative}: book map has {collector.book_chapter_card_count} chapter cards, "
                f"expected {expected_chapter_count}"
            )

    contributor_page = pages.get((output / "contributors" / "index.html").resolve())
    expected_contributors = manifest.get("contributor_count", 0)
    if contributor_page and contributor_page.contributor_card_count != expected_contributors + 1:
        errors.append(
            f"contributors/index.html: found {contributor_page.contributor_card_count} contributor cards, "
            f"expected {expected_contributors} contributors plus one invitation card"
        )

    module_pages = list((output / "modules").glob("*/index.html"))
    chapter_pages = list((output / "chapters").glob("*/index.html"))
    if len(module_pages) != manifest.get("module_count"):
        errors.append(
            f"module-page count {len(module_pages)} != manifest module_count {manifest.get('module_count')}"
        )
    if len(chapter_pages) != expected_chapter_count:
        errors.append("chapter-page count does not match chapters.json")
    chapter_source_theorems = 0
    chapter_source_boundaries = 0
    for chapter_page in chapter_pages:
        collector = pages.get(chapter_page.resolve())
        if collector is None:
            continue
        relative = chapter_page.relative_to(output)
        if collector.source_guide_count != 1:
            errors.append(f"{relative}: expected one textbook source guide")
        if collector.algorithm_flow_count != 1:
            errors.append(f"{relative}: expected one algorithm or proof flow")
        if collector.math_statement_count != collector.math_fallback_count or collector.math_statement_count != collector.math_tex_count:
            errors.append(
                f"{relative}: every mathematical statement needs one readable fallback and one escaped MathJax source"
            )
        if collector.nested_math_errors:
            errors.append(f"{relative}: a mathematical statement swallowed teaching or Lean content")
        if collector.theorem_panel_count != collector.teaching_grid_count:
            errors.append(f"{relative}: theorem panel/teaching-grid structure mismatch")
        if collector.lean_code_count < collector.theorem_panel_count:
            errors.append(f"{relative}: theorem panel is missing an exact Lean statement")
        for source in collector.math_tex_sources:
            if not source.strip():
                errors.append(f"{relative}: empty MathJax source")
                continue
            if source.count(r"\(") != source.count(r"\)") or source.count(r"\[") != source.count(r"\]"):
                errors.append(f"{relative}: unbalanced MathJax delimiters in {source[:120]!r}")
            if not (r"\(" in source or r"\[" in source):
                errors.append(f"{relative}: mathematical source lacks explicit delimiters")
        chapter_source_theorems += collector.source_theorem_card_count
        chapter_source_boundaries += collector.source_boundary_count
    if chapter_source_theorems != manifest.get("source_theorem_count"):
        errors.append(
            f"source theorem cards {chapter_source_theorems} != manifest source_theorem_count "
            f"{manifest.get('source_theorem_count')}"
        )
    if chapter_source_theorems + chapter_source_boundaries != expected_chapter_count:
        errors.append("every chapter needs either a source theorem card or an explicit source boundary")
    if manifest.get("reading_count") != expected_chapter_count:
        errors.append("manifest reading_count does not cover all Book Map chapters")
    if manifest.get("max_module_slug_length", 10_000) > 96:
        errors.append("generated module URL exceeds the 96-character slug contract")

    search_path = output / "search-index.json"
    search_items = json.loads(search_path.read_text(encoding="utf-8")) if search_path.exists() else []
    if len(search_items) != manifest.get("declaration_count"):
        errors.append(
            f"search-index count {len(search_items)} != declaration_count {manifest.get('declaration_count')}"
        )
    for item in search_items:
        target_value = item["url"]
        split = urlsplit(target_value)
        target = output / split.path
        if not target.exists():
            errors.append(f"search index points to missing page: {target_value}")
            continue
        collector = pages.get(target.resolve())
        if collector is None or split.fragment not in collector.ids:
            errors.append(f"search index points to missing declaration anchor: {target_value}")

    ide_data_path = output / "ide-data.json"
    ide_items = json.loads(ide_data_path.read_text(encoding="utf-8")).get("items", []) if ide_data_path.exists() else []
    if len(ide_items) != manifest.get("ide_mapping_count"):
        errors.append(
            f"IDE mapping count {len(ide_items)} != ide_mapping_count {manifest.get('ide_mapping_count')}"
        )
    search_names = {item["name"] for item in search_items}
    for item in ide_items:
        if item.get("name") not in search_names:
            errors.append(f"IDE mapping references an unindexed declaration: {item.get('name')}")
        if not item.get("compile_source", "").startswith("import BanditRLProof"):
            errors.append(f"IDE compile source lacks a project import: {item.get('name')}")

    totals = Counter()
    for collector in pages.values():
        totals["mermaid"] += collector.mermaid_count
        totals["mathjax"] += collector.mathjax_count
        totals["source_links"] += collector.source_link_count
    if totals["mermaid"] < 7:
        errors.append(f"expected at least 7 rendered Mermaid blocks, found {totals['mermaid']}")
    if totals["mathjax"] != len(pages):
        errors.append(f"MathJax is not loaded on every HTML page ({totals['mathjax']} of {len(pages)})")
    if totals["source_links"] < manifest.get("declaration_count", 0):
        errors.append(
            f"expected at least one source link per declaration; found {totals['source_links']} for {manifest.get('declaration_count')}"
        )
    if manifest.get("placeholder_count", 0):
        compiled_text = " ".join(
            path.read_text(encoding="utf-8")
            for path in module_pages
            if path.exists()
        )
        if re.search(r'class="status compiled"[^>]*>Compiled</span>.*?(?:sorry|admit)', compiled_text, re.DOTALL):
            errors.append("a placeholder declaration appears to be marked compiled")

    progress_source = (output / "diagrams" / "progress.mmd").read_text(encoding="utf-8")
    if "{{" not in progress_source:
        errors.append("copied progress.mmd should retain editable count placeholders")
    index_text = (output / "index.html").read_text(encoding="utf-8")
    if "{{" in index_text:
        errors.append("generated index contains an unresolved diagram placeholder")

    if errors:
        print("SITE CHECK FAILED")
        for error in errors[:200]:
            print(f"- {error}")
        if len(errors) > 200:
            print(f"- ... {len(errors) - 200} more errors")
        return 1

    print(
        "SITE CHECK PASSED\n"
        f"- HTML pages: {len(pages)}\n"
        f"- modules: {manifest.get('module_count')}\n"
        f"- declarations: {manifest.get('declaration_count')}\n"
        f"- highlights: {manifest.get('highlight_count')}\n"
        f"- milestones: {manifest.get('milestone_count')}\n"
        f"- textbook crosswalks: {manifest.get('reading_count')}\n"
        f"- source theorem restatements: {manifest.get('source_theorem_count')}\n"
        f"- Live Formalization mappings: {manifest.get('ide_mapping_count')}\n"
        f"- Mermaid blocks: {totals['mermaid']}\n"
        f"- Lean source links: {totals['source_links']}\n"
        "- internal links and anchors: valid\n"
        "- README relative links: valid\n"
        "- MathJax loader and readable mathematical fallbacks: valid\n"
        "- GitHub Pages workflow: complete"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
