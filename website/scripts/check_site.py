#!/usr/bin/env python3
"""Check the generated ABRL documentation site and its source mappings."""

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


class LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.links: list[tuple[str, str]] = []
        self.ids: set[str] = set()
        self.mermaid_count = 0
        self.mathjax_count = 0
        self.source_link_count = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = {key: value or "" for key, value in attrs}
        if values.get("id"):
            self.ids.add(values["id"])
        classes = set(values.get("class", "").split())
        if "mermaid" in classes:
            self.mermaid_count += 1
        for attr in ("href", "src"):
            if values.get(attr):
                self.links.append((attr, values[attr]))
        if "cdn.jsdelivr.net/npm/mathjax" in values.get("src", ""):
            self.mathjax_count += 1
        if "/blob/main/BanditRLProof" in values.get("href", ""):
            self.source_link_count += 1


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
    if not path.exists():
        return ["missing website/scripts/ide_server.py"]
    text = path.read_text(encoding="utf-8")
    required = [
        'default="127.0.0.1"',
        '"/api/compile"',
        '"lake", "env", "lean"',
        "TemporaryDirectory",
        "loopback-only",
    ]
    return [f"IDE server missing safety/compile contract: {item}" for item in required if item not in text]


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

    expected_pages = {
        output / "index.html",
        output / "implementation-map" / "index.html",
        output / "declarations" / "index.html",
        output / "ide" / "index.html",
        output / "learning" / "index.html",
        output / "roadmap" / "index.html",
        output / "workflow" / "index.html",
        output / "attribution" / "index.html",
    }
    for expected in expected_pages:
        if not expected.exists():
            errors.append(f"missing required page: {expected.relative_to(output)}")

    module_pages = list((output / "modules").glob("*/index.html"))
    chapter_pages = list((output / "chapters").glob("*/index.html"))
    if len(module_pages) != manifest.get("module_count"):
        errors.append(
            f"module-page count {len(module_pages)} != manifest module_count {manifest.get('module_count')}"
        )
    if len(chapter_pages) != len(json.loads((SITE_DIR / "content" / "chapters.json").read_text(encoding="utf-8"))["chapters"]):
        errors.append("chapter-page count does not match chapters.json")

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
        f"- Research IDE mappings: {manifest.get('ide_mapping_count')}\n"
        f"- Mermaid blocks: {totals['mermaid']}\n"
        f"- Lean source links: {totals['source_links']}\n"
        "- internal links and anchors: valid\n"
        "- README relative links: valid\n"
        "- MathJax loader: present on every page\n"
        "- GitHub Pages workflow: complete"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
