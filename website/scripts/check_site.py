#!/usr/bin/env python3
"""Check the generated BanditRLlib site, ABRL mappings, and publication contract."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
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
PRIMARY_TEXTBOOK_TITLE = "Bandit Algorithms"
PRIMARY_TEXTBOOK_URL = "https://tor-lattimore.com/downloads/book/book.pdf"
GITHUB_REPO = "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep"
PUBLIC_SITE_URL = "https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep"


class LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.links: list[tuple[str, str]] = []
        self.ids: set[str] = set()
        self.id_counts: Counter[str] = Counter()
        self.mermaid_count = 0
        self.diagram_region_count = 0
        self.accessible_diagram_region_count = 0
        self.command_block_count = 0
        self.accessible_command_block_count = 0
        self.mathjax_count = 0
        self.source_link_count = 0
        self.source_links: list[str] = []
        self.site_sidebar_count = 0
        self.nav_group_count = 0
        self.side_nav_count = 0
        self.side_nav_toggle_count = 0
        self.book_nav_link_count = 0
        self.book_chapter_card_count = 0
        self.spine_nav_link_count = 0
        self.spine_chapter_card_count = 0
        self.primary_textbook_banner_count = 0
        self.contributor_card_count = 0
        self.theorem_panel_count = 0
        self.math_statement_count = 0
        self.math_fallback_count = 0
        self.math_fallback_note_count = 0
        self.math_tex_count = 0
        self.teaching_grid_count = 0
        self.lean_code_count = 0
        self.source_guide_count = 0
        self.notation_primer_count = 0
        self.algorithm_flow_count = 0
        self.source_theorem_card_count = 0
        self.source_boundary_count = 0
        self.chapter_compass_count = 0
        self.learning_route_count = 0
        self.wiki_case_count = 0
        self.wiki_family_card_count = 0
        self.wiki_paper_card_count = 0
        self.wiki_source_port_count = 0
        self.wiki_theorem_surface_count = 0
        self.wiki_paper_case_link_count = 0
        self.wiki_literature_badge_count = 0
        self.wiki_source_badge_count = 0
        self.wiki_lean_badge_count = 0
        self.frontier_case_count = 0
        self.frontier_named_leaf_count = 0
        self.snapshot_card_count = 0
        self.canonical_urls: list[str] = []
        self.og_urls: list[str] = []
        self.og_titles: list[str] = []
        self.twitter_titles: list[str] = []
        self.nested_math_errors = 0
        self.math_tex_sources: list[str] = []
        self._stack: list[tuple[str, set[str]]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = {key: value or "" for key, value in attrs}
        if values.get("id"):
            self.ids.add(values["id"])
            self.id_counts[values["id"]] += 1
        classes = set(values.get("class", "").split())
        if "math-statement" in classes:
            self.math_statement_count += 1
        if "math-fallback" in classes:
            self.math_fallback_count += 1
        if "math-fallback-note" in classes:
            self.math_fallback_note_count += 1
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
        if "notation-primer" in classes:
            self.notation_primer_count += 1
        if "algorithm-flow" in classes:
            self.algorithm_flow_count += 1
        if "source-theorem-card" in classes:
            self.source_theorem_card_count += 1
        if "source-boundary" in classes:
            self.source_boundary_count += 1
        if "data-chapter-compass" in values:
            self.chapter_compass_count += 1
        if "data-learning-route" in values:
            self.learning_route_count += 1
        if "wiki-case-card" in classes:
            self.wiki_case_count += 1
        if "wiki-family-card" in classes:
            self.wiki_family_card_count += 1
        if "wiki-paper-card" in classes:
            self.wiki_paper_card_count += 1
        if "wiki-source-port-card" in classes:
            self.wiki_source_port_count += 1
        if "wiki-theorem-surface" in classes:
            self.wiki_theorem_surface_count += 1
        if "wiki-paper-case-link" in classes:
            self.wiki_paper_case_link_count += 1
        if values.get("data-wiki-literature-status"):
            self.wiki_literature_badge_count += 1
        if values.get("data-wiki-source-status"):
            self.wiki_source_badge_count += 1
        if values.get("data-wiki-lean-status"):
            self.wiki_lean_badge_count += 1
        if "frontier-case-card" in classes:
            self.frontier_case_count += 1
        if "frontier-named-leaf" in classes and "data-frontier-leaf" in values:
            self.frontier_named_leaf_count += 1
        if "snapshot-card" in classes:
            self.snapshot_card_count += 1
        if tag == "link" and values.get("rel") == "canonical":
            self.canonical_urls.append(values.get("href", ""))
        if tag == "meta" and values.get("property") == "og:url":
            self.og_urls.append(values.get("content", ""))
        if tag == "meta" and values.get("property") == "og:title":
            self.og_titles.append(values.get("content", ""))
        if tag == "meta" and values.get("name") == "twitter:title":
            self.twitter_titles.append(values.get("content", ""))
        if any("math-statement" in parent_classes for _parent_tag, parent_classes in self._stack):
            if "teaching-grid" in classes or "lean-code" in classes:
                self.nested_math_errors += 1
        if "mermaid" in classes:
            self.mermaid_count += 1
        if "diagram" in classes:
            self.diagram_region_count += 1
            if values.get("tabindex") == "0" and values.get("role") == "region" and values.get("aria-label"):
                self.accessible_diagram_region_count += 1
        if "command-block" in classes:
            self.command_block_count += 1
            if tag == "pre" and values.get("tabindex") == "0" and values.get("role") == "region" and values.get("aria-label"):
                self.accessible_command_block_count += 1
        if "site-sidebar" in classes:
            self.site_sidebar_count += 1
        if "data-nav-group" in values:
            self.nav_group_count += 1
        if "data-page-toc" in values:
            self.side_nav_count += 1
        if "data-toc-toggle" in values:
            self.side_nav_toggle_count += 1
        if "book-nav-link" in classes:
            self.book_nav_link_count += 1
        if "book-chapter-card" in classes:
            self.book_chapter_card_count += 1
        if "spine-nav-link" in classes:
            self.spine_nav_link_count += 1
        if "spine-chapter-card" in classes:
            self.spine_chapter_card_count += 1
        if "primary-textbook-banner" in classes:
            self.primary_textbook_banner_count += 1
        if "contributor-card" in classes:
            self.contributor_card_count += 1
        for attr in ("href", "src"):
            if values.get(attr):
                self.links.append((attr, values[attr]))
        if "cdn.jsdelivr.net/npm/mathjax" in values.get("src", ""):
            self.mathjax_count += 1
        if tag == "a" and (
            ("/blob/" in values.get("href", "") and "/BanditRLProof" in values.get("href", ""))
            or "/source-access/" in values.get("href", "")
        ):
            self.source_link_count += 1
            self.source_links.append(values["href"])
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
    milestone_ids: set[str] = set()
    milestone_data_path = output / "implementation-map" / "milestone-data.json"
    if milestone_data_path.exists():
        milestone_payload = json.loads(milestone_data_path.read_text(encoding="utf-8"))
        milestone_ids = {str(item.get("id", "")) for item in milestone_payload.get("items", [])}
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
                elif (
                    unquote(split.fragment) not in target_collector.ids
                    and not (
                        target.resolve()
                        == (output / "implementation-map" / "index.html").resolve()
                        and unquote(split.fragment) in milestone_ids
                    )
                ):
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


def check_readme_presentation() -> list[str]:
    """Keep the compact, decorated README entry points requested for the project."""
    errors: list[str] = []
    text = (ROOT / "README.md").read_text(encoding="utf-8")
    for line in text.splitlines():
        match = re.match(r"^(#{1,6})\s+(.+)$", line)
        if match and not re.match(r"[^\x00-\x7F]", match.group(2)):
            errors.append(f"README heading lacks a decorative item: {line}")
    collapsed_sections = {
        "## 🌐 BanditRLlib website": "Website features and local build",
        "## 🧪 Live Formalization": "Local experimental workspace and status boundaries",
        "## 🚀 Quick start": "Installation, checks, commands, and repository map",
    }
    for heading, summary in collapsed_sections.items():
        pattern = re.escape(heading) + r"\s+<details>\s+<summary>" + re.escape(summary) + r"</summary>"
        if re.search(pattern, text) is None:
            errors.append(f"README section is not compactly collapsed: {heading}")
    return errors


def expected_canonical_url(output: Path, page: Path) -> str:
    relative = page.relative_to(output).as_posix()
    if relative == "index.html":
        return f"{PUBLIC_SITE_URL}/"
    if relative.endswith("/index.html"):
        return f"{PUBLIC_SITE_URL}/{relative[:-10]}"
    return f"{PUBLIC_SITE_URL}/{relative}"


def check_page_metadata(output: Path, pages: dict[Path, LinkCollector]) -> list[str]:
    errors: list[str] = []
    for page, collector in pages.items():
        expected = expected_canonical_url(output, page)
        if collector.canonical_urls != [expected]:
            errors.append(
                f"{page.relative_to(output)}: canonical URL must be exactly {expected}"
            )
        if collector.og_urls != [expected]:
            errors.append(f"{page.relative_to(output)}: og:url must match its canonical URL")
        if len(collector.og_titles) != 1 or len(collector.twitter_titles) != 1:
            errors.append(f"{page.relative_to(output)}: social title metadata is incomplete")
        elif collector.og_titles != collector.twitter_titles:
            errors.append(f"{page.relative_to(output)}: Open Graph and Twitter titles disagree")
    return errors


def check_current_evidence_surfaces(
    output: Path,
    pages: dict[Path, LinkCollector],
) -> list[str]:
    """Verify that public progress surfaces remain generated from current ledgers."""
    errors: list[str] = []
    comparison_path = ROOT / "runs" / "harness-comparison" / "latest.json"
    if not comparison_path.exists():
        return ["missing runs/harness-comparison/latest.json"]
    comparison = json.loads(comparison_path.read_text(encoding="utf-8"))
    decision = comparison.get("decision", {})
    matched_count = len(comparison.get("matched_experiments", []))
    minimum_count = comparison.get("minimum_matched_experiments")

    index_path = (output / "index.html").resolve()
    index_source = index_path.read_text(encoding="utf-8") if index_path.exists() else ""
    index_collector = pages.get(index_path)
    if index_collector is None or index_collector.snapshot_card_count != 4:
        errors.append("homepage must contain exactly four generated current-evidence cards")
    for required in (
        "Current evidence snapshot",
        f"{matched_count}/{minimum_count}",
        str(decision.get("next_experiment_harness", "")),
        "SGB Theorem-2 follow-on",
    ):
        if required not in index_source:
            errors.append(f"homepage current-evidence snapshot is missing {required!r}")

    workflow_path = output / "workflow" / "index.html"
    workflow_source = workflow_path.read_text(encoding="utf-8") if workflow_path.exists() else ""
    for required in (
        'id="comparison-evidence"',
        str(decision.get("status", "")).replace("-", " ").title(),
        f"{matched_count} of {minimum_count} required",
        str(decision.get("recommended_default", "")),
        str(decision.get("next_experiment_harness", "")),
        "hierarchical",
        "master-worker",
        "latest.json",
        "latest.prompt.md",
        "harness_self_comparison.md",
    ):
        if required not in workflow_source:
            errors.append(f"workflow comparison ledger is missing {required!r}")

    site_css = (output / "static" / "site.css").read_text(encoding="utf-8")
    for required in (
        ".current-snapshot",
        ".comparison-decision",
        ".status.prototype",
        ".declaration-content .lean-code",
        ".code-toolbar",
        ".lean-code.wrap-lines",
        ".lean-code.scroll-lines",
    ):
        if required not in site_css:
            errors.append(f"site.css is missing evidence/overflow support: {required}")

    website_readme = (SITE_DIR / "README.md").read_text(encoding="utf-8")
    for stale in (
        "visible-marginal/native-prefix identification",
        "native visible law\nremain unproved",
    ):
        if stale in website_readme:
            errors.append(f"website README retains stale SGB boundary: {stale}")
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
        "python3 website/scripts/build_site.py",
        "--lean-verified",
        "--public-snapshot-base-url https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep",
        "--expect-public-base-url https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep",
        "python3 website/scripts/check_site.py",
        "actions/configure-pages@",
        "actions/upload-pages-artifact@",
        "actions/deploy-pages@",
        "path: website/_site",
    ]
    errors = [f"documentation workflow missing: {item}" for item in required if item not in text]
    branch_build_guard = 'if [[ "${{ github.ref }}" == "refs/heads/main" ]]'
    branch_publish_guard = (
        "if: github.ref == 'refs/heads/main' && "
        "github.event_name != 'pull_request'"
    )
    if text.count(branch_build_guard) != 2:
        errors.append("documentation workflow must guard public build and check to main")
    if text.count(branch_publish_guard) != 2:
        errors.append("documentation workflow must guard upload and deploy to main")
    return errors


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
    parser.add_argument(
        "--expect-public-base-url",
        default="",
        help="require exact public-deployment metadata and commit-pinned source links",
    )
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
    expected_public_base_url = args.expect_public_base_url.rstrip("/")
    if expected_public_base_url:
        if manifest.get("public_snapshot") is not True:
            errors.append("site manifest is not marked as a public snapshot")
        if manifest.get("public_base_url") != expected_public_base_url:
            errors.append(
                "site manifest public_base_url differs from --expect-public-base-url"
            )
        if manifest.get("source_dirty") is not False:
            errors.append("public snapshot must be built from a clean source tree")
        if re.fullmatch(r"[0-9a-f]{40}", str(manifest.get("source_commit", ""))) is None:
            errors.append("public snapshot source_commit is not a full Git commit")

    pages = parse_pages(output)
    errors.extend(check_internal_links(output, pages))
    errors.extend(check_page_metadata(output, pages))
    errors.extend(check_markdown_links(ROOT / "README.md"))
    errors.extend(check_markdown_links(SITE_DIR / "README.md"))
    errors.extend(check_readme_presentation())
    errors.extend(check_diagram_sources())
    errors.extend(check_workflow())
    errors.extend(check_ide_server())
    errors.extend(check_community_contract(output, manifest))
    errors.extend(check_branding_and_formalizer(output, manifest))
    errors.extend(check_current_evidence_surfaces(output, pages))

    expected_pages = {
        output / "index.html",
        output / "implementation-map" / "index.html",
        output / "declarations" / "index.html",
        output / "ide" / "index.html",
        output / "community" / "index.html",
        output / "contributors" / "index.html",
        output / "installation" / "index.html",
        output / "learning" / "index.html",
        output / "textbook-spine" / "index.html",
        output / "roadmap" / "index.html",
        output / "lean-graph" / "index.html",
        output / "banditrlwiki" / "index.html",
        output / "banditrlwiki" / "frontier" / "index.html",
        output / "banditrlwiki" / "papers" / "index.html",
        output / "banditrlwiki" / "progress" / "index.html",
        output / "proof-graph-laboratory" / "index.html",
        output / "workflow" / "index.html",
        output / "attribution" / "index.html",
        output / "source-access" / "index.html",
    }
    for expected in expected_pages:
        if not expected.exists():
            errors.append(f"missing required page: {expected.relative_to(output)}")

    proof_lab_path = output / "proof-graph-laboratory" / "index.html"
    if proof_lab_path.exists():
        proof_lab = proof_lab_path.read_text(encoding="utf-8")
        required_boundaries = [
            "environment-extracted",
            "not a kernel trace or an elaborator trace",
            "Static GitHub Pages does not load a Lean environment",
            "Raw new-node count is excluded",
            "Merely restating a Tsallis-INF derivation does not qualify",
            "LB(s) &lt;= OPT_remaining(s)",
            "Chapters 13–17",
        ]
        for boundary in required_boundaries:
            if boundary not in proof_lab:
                errors.append(f"proof-graph-laboratory/index.html: missing evidence boundary {boundary!r}")
        if manifest.get("proof_graph_root_count") != 3:
            errors.append("site manifest must record exactly three frozen proof-graph benchmark roots")
        if manifest.get("cng_candidate_status") != "partial":
            errors.append("site manifest must keep the CNG candidate status partial")
        if manifest.get("cng_structural_discovery_established") is not False:
            errors.append("site manifest must not claim CNG structural discovery")

    lean_graph_path = output / "lean-graph" / "index.html"
    lean_graph_data_path = output / "lean-graph" / "graph.json"
    lean_graph_overview_path = output / "lean-graph" / "overview.json"
    lean_graph_script_path = output / "static" / "lean-graph.js"
    for required_path in (lean_graph_data_path, lean_graph_overview_path, lean_graph_script_path):
        if not required_path.exists():
            errors.append(f"missing Lean Graph artifact: {required_path.relative_to(output)}")
    if lean_graph_path.exists():
        lean_graph_html = lean_graph_path.read_text(encoding="utf-8")
        for required_text in (
            "Underlying Lean Graph of BanditRLlib",
            "progressive disclosure",
            "not a kernel trace",
            "Whole-chapter status and individual compiled declarations remain separate",
            "Choose a readable branch first",
            "Open interactive canvas",
            "JavaScript is optional for reading",
            "Auto-Sampling-Theory-In-Sleep/lean-foundations.html",
        ):
            if required_text not in lean_graph_html:
                errors.append(f"lean-graph/index.html: missing graph boundary {required_text!r}")
        if 'data-graph-overview-source="overview.json"' not in lean_graph_html:
            errors.append("lean-graph/index.html: missing the lightweight overview graph source")
    if lean_graph_overview_path.exists():
        try:
            lean_graph_overview = json.loads(lean_graph_overview_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as error:
            errors.append(f"lean-graph/overview.json: invalid JSON: {error}")
            lean_graph_overview = {}
        overview_nodes = lean_graph_overview.get("nodes", [])
        overview_ids = {node.get("id") for node in overview_nodes if isinstance(node, dict)}
        expected_overview_ids = {
            "library:banditrl",
            "group:book-map",
            "group:textbook-spine",
            "group:milestones",
            "group:proof-laboratory",
        }
        if overview_ids != expected_overview_ids:
            errors.append("lean-graph/overview.json: expected exactly the five initial overview nodes")
        if lean_graph_overview_path.stat().st_size >= 500_000:
            errors.append("lean-graph/overview.json: initial graph payload must remain below 500 KB")
        for edge in lean_graph_overview.get("edges", []):
            if edge.get("source") not in overview_ids or edge.get("target") not in overview_ids:
                errors.append("lean-graph/overview.json: edge references a deferred node")
                break
    if lean_graph_data_path.exists():
        try:
            lean_graph = json.loads(lean_graph_data_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as error:
            errors.append(f"lean-graph/graph.json: invalid JSON: {error}")
            lean_graph = {}
        graph_nodes = lean_graph.get("nodes", [])
        graph_edges = lean_graph.get("edges", [])
        graph_node_ids = [node.get("id") for node in graph_nodes if isinstance(node, dict)]
        graph_node_id_set = set(graph_node_ids)
        if len(graph_node_ids) != len(graph_node_id_set):
            errors.append("lean-graph/graph.json: duplicate node ids")
        if lean_graph.get("root") not in graph_node_id_set:
            errors.append("lean-graph/graph.json: root does not name a graph node")
        for required_node in (
            "library:banditrl",
            "group:book-map",
            "group:textbook-spine",
            "group:milestones",
            "group:proof-laboratory",
        ):
            if required_node not in graph_node_id_set:
                errors.append(f"lean-graph/graph.json: missing required node {required_node}")
        for edge in graph_edges:
            if edge.get("source") not in graph_node_id_set or edge.get("target") not in graph_node_id_set:
                errors.append("lean-graph/graph.json: edge references a missing node")
                break
        if manifest.get("lean_graph_node_count") != len(graph_nodes):
            errors.append("manifest lean_graph_node_count does not match lean-graph/graph.json")
        if manifest.get("lean_graph_edge_count") != len(graph_edges):
            errors.append("manifest lean_graph_edge_count does not match lean-graph/graph.json")
        declaration_node_count = sum(
            1 for node in graph_nodes if isinstance(node, dict) and node.get("kind") in {
                "definition", "abbreviation", "structure", "typeclass", "inductive type",
                "theorem", "lemma", "axiom", "opaque declaration"
            }
        )
        if declaration_node_count != manifest.get("declaration_count"):
            errors.append("Lean Graph declaration nodes do not match the generated declaration inventory")

    wiki_source_path = SITE_DIR / "content" / "banditrlwiki.json"
    wiki_script_path = output / "static" / "banditrlwiki.js"
    if not wiki_source_path.exists():
        errors.append("missing website/content/banditrlwiki.json")
        wiki = {"families": [], "cases": []}
    else:
        wiki = json.loads(wiki_source_path.read_text(encoding="utf-8"))
    milestone_source = json.loads(
        (SITE_DIR / "content" / "results.json").read_text(encoding="utf-8")
    )
    milestone_by_id = {
        milestone.get("id"): milestone for milestone in milestone_source.get("results", [])
    }
    if not wiki_script_path.exists():
        errors.append("missing generated BanditRLwiki interaction script")
    wiki_families = wiki.get("families", [])
    wiki_cases = wiki.get("cases", [])
    wiki_active_source_audits = wiki.get("active_source_audits", [])
    family_ids = [family.get("id") for family in wiki_families]
    case_ids = [case.get("id") for case in wiki_cases]
    if len(family_ids) != len(set(family_ids)):
        errors.append("BanditRLwiki family ids are not unique")
    if len(case_ids) != len(set(case_ids)):
        errors.append("BanditRLwiki case ids are not unique")
    if manifest.get("banditrlwiki_family_count") != len(wiki_families):
        errors.append("manifest BanditRLwiki family count does not match source data")
    if manifest.get("banditrlwiki_case_count") != len(wiki_cases):
        errors.append("manifest BanditRLwiki case count does not match source data")
    if manifest.get("banditrlwiki_active_source_audit_count") != len(wiki_active_source_audits):
        errors.append("manifest BanditRLwiki active-source-audit count does not match source data")
    active_source_audit_ids = [audit.get("id") for audit in wiki_active_source_audits]
    if len(active_source_audit_ids) != len(set(active_source_audit_ids)):
        errors.append("BanditRLwiki active source-audit ids are not unique")
    for audit in wiki_active_source_audits:
        required = (
            "id", "title", "paper_title", "authors", "year", "url", "milestone_id", "lean_status",
            "compiled_declaration_count", "scope", "boundary", "representative_declarations",
        )
        if not all(audit.get(key) for key in required):
            errors.append(f"BanditRLwiki active source audit {audit.get('id')} is incomplete")
        if audit.get("lean_status") != "partial":
            errors.append(f"BanditRLwiki active source audit {audit.get('id')} must remain partial")
        if not isinstance(audit.get("compiled_declaration_count"), int) or audit.get("compiled_declaration_count", 0) <= 0:
            errors.append(f"BanditRLwiki active source audit {audit.get('id')} has an invalid declaration count")
        milestone_ids = [audit.get("milestone_id")]
        if audit.get("follow_on_milestone_id"):
            milestone_ids.append(audit["follow_on_milestone_id"])
        milestones = [milestone_by_id.get(milestone_id) for milestone_id in milestone_ids]
        missing_milestones = [
            milestone_id
            for milestone_id, milestone in zip(milestone_ids, milestones)
            if milestone is None
        ]
        if missing_milestones:
            errors.append(
                f"BanditRLwiki active source audit {audit.get('id')} names missing milestones "
                f"{missing_milestones}"
            )
        else:
            milestone_declarations: set[str] = set()
            for milestone in milestones:
                milestone_declarations.update(milestone.get("declarations", []))
                if milestone.get("status") != audit.get("lean_status"):
                    errors.append(
                        f"BanditRLwiki active source audit {audit.get('id')} status drifts from "
                        f"milestone {milestone.get('id')}"
                    )
            if len(milestone_declarations) != audit.get("compiled_declaration_count"):
                errors.append(
                    f"BanditRLwiki active source audit {audit.get('id')} declaration count drifts "
                    "from its milestone set"
                )
            if not set(audit.get("representative_declarations", [])).issubset(milestone_declarations):
                errors.append(
                    f"BanditRLwiki active source audit {audit.get('id')} cites a declaration "
                    "outside its milestone set"
                )
        if "not" not in audit.get("boundary", "").lower() and "remain" not in audit.get("boundary", "").lower():
            errors.append(f"BanditRLwiki active source audit {audit.get('id')} does not state its nonclaim")
        if "�" in json.dumps(audit, ensure_ascii=False):
            errors.append(f"BanditRLwiki active source audit {audit.get('id')} contains a Unicode replacement character")
    literature_status_counts = Counter(
        case.get("comparison", {}).get("status") for case in wiki_cases
    )
    lean_status_counts = Counter(case.get("lean", {}).get("status") for case in wiki_cases)
    if manifest.get("banditrlwiki_literature_status_counts") != dict(sorted(literature_status_counts.items())):
        errors.append("manifest BanditRLwiki literature-status ledger does not match source data")
    if manifest.get("banditrlwiki_lean_status_counts") != dict(sorted(lean_status_counts.items())):
        errors.append("manifest BanditRLwiki Lean-status ledger does not match source data")
    literature_open_cases = [
        case for case in wiki_cases if case.get("frontier", {}).get("literature_open")
    ]
    formalization_open_cases = [
        case for case in wiki_cases if case.get("frontier", {}).get("formalization_open")
    ]
    formalization_leaf_ids = [
        leaf_id
        for case in formalization_open_cases
        for leaf_id in case.get("frontier", {}).get("leaf_ids", [])
    ]
    source_audit_cases = [
        case for case in wiki_cases
        if case.get("comparison", {}).get("status") == "source-audit-pending"
    ]
    paper_urls: set[str] = set()
    paper_case_pairs: set[tuple[str, str]] = set()
    paper_titles_by_url: dict[str, str] = {}
    theorem_surface_count = 0
    for case in wiki_cases:
        for side in ("upper", "lower"):
            for record in case.get(side, []):
                theorem_surface_count += 1
                url = record.get("url", "")
                paper_urls.add(url)
                paper_case_pairs.add((url, case.get("id", "")))
                required = ("paper_title", "result_title", "url", "theorem", "math", "plain")
                if not all(record.get(key) for key in required):
                    errors.append(
                        f"BanditRLwiki case {case.get('id')} has an incomplete {side} theorem surface"
                    )
                if "title" in record:
                    errors.append(
                        f"BanditRLwiki case {case.get('id')} does not separate paper_title/result_title"
                    )
                paper_title = record.get("paper_title", "")
                known_title = paper_titles_by_url.setdefault(url, paper_title)
                if known_title != paper_title:
                    errors.append(f"BanditRLwiki source {url} has inconsistent paper titles")
                if case.get("source_status") == "exact-source-theorem" and not re.search(
                    r"\b(?:Theorem|Lemma|Corollary)\s+[0-9]", record.get("theorem", "")
                ):
                    errors.append(
                        f"BanditRLwiki exact-source case {case.get('id')} lacks a numbered theorem locator"
                    )
    if manifest.get("banditrlwiki_literature_open_count") != len(literature_open_cases):
        errors.append("manifest BanditRLwiki literature-open count does not match source data")
    if manifest.get("banditrlwiki_formalization_open_case_count") != len(formalization_open_cases):
        errors.append("manifest BanditRLwiki formalization-open case count does not match source data")
    if manifest.get("banditrlwiki_formalization_leaf_count") != len(formalization_leaf_ids):
        errors.append("manifest BanditRLwiki named-leaf count does not match source data")
    if manifest.get("banditrlwiki_paper_count") != len(paper_urls):
        errors.append("manifest BanditRLwiki paper count does not match unique primary URLs")
    if manifest.get("banditrlwiki_theorem_surface_count") != theorem_surface_count:
        errors.append("manifest BanditRLwiki theorem-surface count does not match source data")
    if manifest.get("banditrlwiki_paper_case_link_count") != len(paper_case_pairs):
        errors.append("manifest BanditRLwiki paper/case link count does not match source data")
    if len(formalization_leaf_ids) != len(set(formalization_leaf_ids)):
        errors.append("BanditRLwiki named frontier leaf ids are not unique")
    for case in wiki_cases:
        literature_status = case.get("comparison", {}).get("status")
        lean_status = case.get("lean", {}).get("status")
        if literature_status == "literature-open" and not case.get("frontier", {}).get("literature_open"):
            errors.append(f"BanditRLwiki case {case.get('id')} merges literature-open with another status")
        if literature_status == "source-audit-pending" and case.get("frontier", {}).get("literature_open"):
            errors.append(f"BanditRLwiki case {case.get('id')} treats a pending audit as literature-open")
        if lean_status == "compiled" and not case.get("lean", {}).get("declarations"):
            errors.append(f"BanditRLwiki case {case.get('id')} marks Lean compiled without declarations")
        if case.get("frontier", {}).get("formalization_open") and not case.get("frontier", {}).get("leaf_ids"):
            errors.append(f"BanditRLwiki case {case.get('id')} is open without named frontier leaves")
        for leaf_id in case.get("frontier", {}).get("leaf_ids", []):
            if not re.fullmatch(r"[A-Z0-9][A-Z0-9-]*", leaf_id):
                errors.append(f"BanditRLwiki case {case.get('id')} has malformed leaf id {leaf_id}")
        if "�" in json.dumps(case, ensure_ascii=False):
            errors.append(f"BanditRLwiki case {case.get('id')} contains a Unicode replacement character")
    wiki_index_path = output / "banditrlwiki" / "index.html"
    wiki_frontier_path = output / "banditrlwiki" / "frontier" / "index.html"
    wiki_papers_path = output / "banditrlwiki" / "papers" / "index.html"
    wiki_index_collector = pages.get(wiki_index_path.resolve())
    if wiki_index_collector:
        if wiki_index_collector.wiki_case_count != len(wiki_cases):
            errors.append("BanditRLwiki overview case-card count does not match source data")
        if wiki_index_collector.wiki_family_card_count != len(wiki_families):
            errors.append("BanditRLwiki overview family-card count does not match source data")
        if wiki_index_collector.wiki_source_port_count != len(wiki_active_source_audits):
            errors.append("BanditRLwiki overview active-source-port count does not match source data")
        for label, count in (
            ("literature", wiki_index_collector.wiki_literature_badge_count),
            ("source", wiki_index_collector.wiki_source_badge_count),
            ("Lean", wiki_index_collector.wiki_lean_badge_count),
        ):
            if count != len(wiki_cases):
                errors.append(
                    f"BanditRLwiki overview has {count} {label} badges for {len(wiki_cases)} cases"
                )
        wiki_index_source = wiki_index_path.read_text(encoding="utf-8")
        for boundary in (
            "Read three statuses, never one blended badge",
            "Open does not mean missing from this list.",
            "Published optimality, theorem-level source audit, and local Lean compilation",
        ):
            if boundary not in wiki_index_source:
                errors.append(f"BanditRLwiki overview is missing status boundary {boundary!r}")
    if wiki_frontier_path.exists():
        frontier_source = wiki_frontier_path.read_text(encoding="utf-8")
        for boundary in (
            "A mathematical literature gap is not the same as a missing source audit",
            "They are not labeled literature-open.",
            "The mathematics may already be known",
            "remain outside the minimax ledger",
        ):
            if boundary not in frontier_source:
                errors.append(f"BanditRLwiki frontier is missing status boundary {boundary!r}")
        literature_section = frontier_source.split(
            '<section id="literature-frontier">', 1
        )[-1].split('<section id="source-audit-queue">', 1)[0]
        source_queue_section = frontier_source.split(
            '<section id="source-audit-queue">', 1
        )[-1].split('<section id="formalization-frontier">', 1)[0]
        for case in source_audit_cases:
            if case["id"] in literature_section:
                errors.append(f"pending source audit {case['id']} appears in literature-open section")
            if case["id"] not in source_queue_section:
                errors.append(f"pending source audit {case['id']} is absent from source-audit queue")
        frontier_collector = pages.get(wiki_frontier_path.resolve())
        expected_frontier_cards = (
            len(literature_open_cases) + len(source_audit_cases) + len(formalization_open_cases)
        )
        if frontier_collector:
            if frontier_collector.frontier_case_count != expected_frontier_cards:
                errors.append("BanditRLwiki frontier case-card count does not match independent ledgers")
            if frontier_collector.frontier_named_leaf_count != len(formalization_leaf_ids):
                errors.append("BanditRLwiki rendered named-leaf count does not match source data")
            if frontier_collector.wiki_source_port_count != len(wiki_active_source_audits):
                errors.append("BanditRLwiki frontier active-source-port count does not match source data")
            for leaf_id in formalization_leaf_ids:
                if f"leaf-{leaf_id.lower()}" not in frontier_collector.ids:
                    errors.append(f"BanditRLwiki frontier is missing named leaf anchor {leaf_id}")
        if "static/banditrlwiki.js?v=" not in frontier_source:
            errors.append("BanditRLwiki frontier is missing hash-reveal interaction script")
    if wiki_papers_path.exists():
        paper_collector = pages.get(wiki_papers_path.resolve())
        if paper_collector:
            if paper_collector.wiki_paper_card_count != manifest.get("banditrlwiki_paper_count"):
                errors.append("BanditRLwiki paper-card count does not match manifest")
            if paper_collector.wiki_theorem_surface_count != theorem_surface_count:
                errors.append("BanditRLwiki paper index drops or duplicates theorem surfaces")
            if paper_collector.wiki_paper_case_link_count != len(paper_case_pairs):
                errors.append("BanditRLwiki paper index duplicates or drops paper/case links")
        paper_source = wiki_papers_path.read_text(encoding="utf-8")
        for case in wiki_cases:
            if case["id"] not in paper_source:
                errors.append(f"BanditRLwiki paper index does not link back to case {case['id']}")
    setting_pages = list((output / "banditrlwiki" / "settings").glob("*/index.html"))
    case_pages = list((output / "banditrlwiki" / "cases").glob("*/index.html"))
    if len(setting_pages) != len(wiki_families):
        errors.append("BanditRLwiki setting-page count does not match source data")
    if len(case_pages) != len(wiki_cases):
        errors.append("BanditRLwiki case-page count does not match source data")
    for wiki_page in list((output / "banditrlwiki").rglob("*.html")):
        collector = pages.get(wiki_page.resolve())
        if collector is None:
            continue
        relative = wiki_page.relative_to(output)
        duplicate_ids = [value for value, count in collector.id_counts.items() if count > 1]
        if duplicate_ids:
            errors.append(f"{relative}: duplicate HTML ids {duplicate_ids}")
        if collector.math_statement_count != collector.math_fallback_count or collector.math_statement_count != collector.math_tex_count:
            errors.append(f"{relative}: every Wiki formula needs one fallback and one MathJax source")
        if "�" in wiki_page.read_text(encoding="utf-8"):
            errors.append(f"{relative}: contains a Unicode replacement character")
    attribution_path = output / "attribution" / "index.html"
    if attribution_path.exists():
        attribution_source = attribution_path.read_text(encoding="utf-8")
        for boundary in (
            "example-cases/samplewiki.html",
            "example-cases/samplewiki/frontier.html",
            "did not expose a repository license file",
            "No Samplinglib source file, graph or theorem data",
        ):
            if boundary not in attribution_source:
                errors.append(f"attribution/index.html: missing Samplinglib boundary {boundary!r}")

    chapter_source = json.loads(
        (SITE_DIR / "content" / "chapters.json").read_text(encoding="utf-8")
    )["chapters"]
    expected_chapter_count = len(chapter_source)
    readings_source = json.loads(
        (SITE_DIR / "content" / "readings.json").read_text(encoding="utf-8")
    ).get("readings", [])
    chapter_slugs = {chapter.get("slug") for chapter in chapter_source}
    reading_slugs = {reading.get("slug") for reading in readings_source}
    if reading_slugs != chapter_slugs:
        errors.append("readings.json must contain exactly one crosswalk for every Book Map chapter")
    for reading in readings_source:
        teaching_route = reading.get("teaching_route")
        if (
            not isinstance(teaching_route, list)
            or not 1 <= len(teaching_route) <= 4
            or any(not isinstance(name, str) or not name.strip() for name in teaching_route)
            or len(teaching_route) != len(set(teaching_route))
        ):
            errors.append(
                f"readings.json: {reading.get('slug')} needs one to four unique teaching-route declarations"
            )
        notation = reading.get("notation")
        if not isinstance(notation, list) or len(notation) != 3:
            errors.append(
                f"readings.json: {reading.get('slug')} needs exactly three notation-primer entries"
            )
            continue
        if any(
            not isinstance(item, dict) or not str(item.get("term", "")).strip()
            or not str(item.get("meaning", "")).strip()
            for item in notation
        ):
            errors.append(f"readings.json: {reading.get('slug')} has an incomplete notation entry")
    textbook_spine = json.loads(
        (SITE_DIR / "content" / "textbook_spine.json").read_text(encoding="utf-8")
    )
    expected_spine_count = len(textbook_spine["chapters"])
    if manifest.get("textbook_spine_chapter_count") != expected_spine_count:
        errors.append("manifest textbook_spine_chapter_count does not match textbook_spine.json")
    if not (output / "static" / "favicon.svg").exists():
        errors.append("missing generated SVG favicon")
    for page, collector in pages.items():
        page_source = page.read_text(encoding="utf-8")
        if 'rel="icon"' not in page_source:
            errors.append(f"{page.relative_to(output)}: missing favicon link")
        for mojibake in ("�", "Ã", "Â", "â€", "ï»¿", "ᵓ"):
            if mojibake in page_source:
                errors.append(f"{page.relative_to(output)}: contains likely mojibake marker {mojibake!r}")
        if collector.nav_group_count != 7:
            errors.append(
                f"{page.relative_to(output)}: expected seven collapsible navigation groups, "
                f"found {collector.nav_group_count}"
            )
        if 'aria-keyshortcuts="/"' not in page_source:
            errors.append(f"{page.relative_to(output)}: global search is missing its keyboard shortcut")
        if 'data-nav-group-active="false" open' in page_source:
            errors.append(f"{page.relative_to(output)}: inactive sidebar groups must default to collapsed")
        if collector.side_nav_count != collector.side_nav_toggle_count:
            errors.append(f"{page.relative_to(output)}: page TOC is missing its accessible mobile toggle")
        if collector.math_statement_count != collector.math_fallback_note_count:
            errors.append(
                f"{page.relative_to(output)}: every mathematical statement needs one renderer-failure note"
            )
        if collector.site_sidebar_count != 1:
            errors.append(
                f"{page.relative_to(output)}: expected one site sidebar, found {collector.site_sidebar_count}"
            )
        if collector.book_nav_link_count != expected_chapter_count:
            errors.append(
                f"{page.relative_to(output)}: book navigation has {collector.book_nav_link_count} chapter links, "
                f"expected {expected_chapter_count}"
            )
        if collector.spine_nav_link_count != expected_spine_count:
            errors.append(
                f"{page.relative_to(output)}: textbook spine navigation has "
                f"{collector.spine_nav_link_count} chapter links, expected {expected_spine_count}"
            )

    for relative in (Path("index.html"), Path("learning/index.html")):
        collector = pages.get((output / relative).resolve())
        if collector and collector.book_chapter_card_count != expected_chapter_count:
            errors.append(
                f"{relative}: book map has {collector.book_chapter_card_count} chapter cards, "
                f"expected {expected_chapter_count}"
            )
        if collector and collector.primary_textbook_banner_count != 1:
            errors.append(
                f"{relative}: expected one prominent primary-textbook banner, "
                f"found {collector.primary_textbook_banner_count}"
            )
        page_source = (output / relative).read_text(encoding="utf-8")
        textbook_metadata = (
            PRIMARY_TEXTBOOK_TITLE,
            PRIMARY_TEXTBOOK_URL,
            "Cambridge University Press, 2020",
            "10.1017/9781108571401",
        )
        if any(item not in page_source for item in textbook_metadata):
            errors.append(f"{relative}: primary textbook identity, edition, DOI, or free-edition link is missing")
        coverage_expectations = (
            'class="textbook-coverage"',
            "10 source-mapped routes",
            "9 canonical cores compiled",
            "3 of 5 named terminals compile",
            "Not claimed complete",
        )
        for expectation in coverage_expectations:
            if expectation not in page_source:
                errors.append(f"{relative}: textbook coverage ledger is missing {expectation!r}")
        if collector and collector.spine_chapter_card_count != expected_spine_count:
            errors.append(
                f"{relative}: textbook spine has {collector.spine_chapter_card_count} chapter cards, "
                f"expected {expected_spine_count}"
            )
        if collector and collector.learning_route_count != 5:
            errors.append(
                f"{relative}: expected five mathematical learning routes, found {collector.learning_route_count}"
            )

    command_block_expectations = {
        Path("index.html"): 2,
        Path("installation/index.html"): 3,
    }
    for relative, expected in command_block_expectations.items():
        collector = pages.get((output / relative).resolve())
        if collector and collector.command_block_count != expected:
            errors.append(
                f"{relative}: found {collector.command_block_count} command blocks, expected {expected}"
            )
        if collector and collector.accessible_command_block_count != collector.command_block_count:
            errors.append(f"{relative}: every command block must be a labelled keyboard-scroll region")

    contributor_page = pages.get((output / "contributors" / "index.html").resolve())
    expected_contributors = manifest.get("contributor_count", 0)
    if contributor_page and contributor_page.contributor_card_count != expected_contributors + 1:
        errors.append(
            f"contributors/index.html: found {contributor_page.contributor_card_count} contributor cards, "
            f"expected {expected_contributors} contributors plus one invitation card"
        )

    module_pages = list((output / "modules").glob("*/index.html"))
    chapter_pages = list((output / "chapters").glob("*/index.html"))
    spine_pages = list((output / "textbook-spine").glob("*/index.html"))
    if len(module_pages) != manifest.get("module_count"):
        errors.append(
            f"module-page count {len(module_pages)} != manifest module_count {manifest.get('module_count')}"
        )
    for module_page in module_pages:
        module_html = module_page.read_text(encoding="utf-8")
        title_start = module_html.find('<h1 class="page-title identifier-title">')
        title_end = module_html.find("</h1>", title_start)
        if title_start < 0 or title_end < 0 or "<wbr>" not in module_html[title_start:title_end]:
            errors.append(f"{module_page.relative_to(output)}: module title lacks identifier wrap points")
        lede_match = re.search(r'<p class="lede">(.*?)</p>', module_html, re.DOTALL)
        if lede_match and (lede_match.group(1).lstrip().startswith("#") or "`" in lede_match.group(1)):
            errors.append(f"{module_page.relative_to(output)}: module lede leaks Markdown syntax")
    if len(chapter_pages) != expected_chapter_count:
        errors.append("chapter-page count does not match chapters.json")
    if len(spine_pages) != expected_spine_count:
        errors.append("textbook-spine chapter-page count does not match textbook_spine.json")
    chapter_source_theorems = 0
    chapter_source_boundaries = 0
    readings_by_slug = {reading.get("slug"): reading for reading in readings_source}
    for chapter_page in chapter_pages:
        collector = pages.get(chapter_page.resolve())
        if collector is None:
            continue
        relative = chapter_page.relative_to(output)
        page_source = chapter_page.read_text(encoding="utf-8")
        chapter_slug = chapter_page.parent.name
        teaching_route = readings_by_slug.get(chapter_slug, {}).get("teaching_route", [])
        visible_source = page_source.split(
            '<details class="inventory-disclosure teaching-disclosure">', 1
        )[0]
        visible_panel_count = visible_source.count('<article class="theorem-panel')
        if visible_panel_count != len(teaching_route):
            errors.append(
                f"{relative}: visible theorem panels {visible_panel_count} != teaching route {len(teaching_route)}"
            )
        if page_source.count('class="chapter-pager chapter-pager-primary"') != 1:
            errors.append(f"{relative}: expected one primary Book Map sequence pager")
        if page_source.count('class="chapter-pager chapter-pager-secondary"') != 1:
            errors.append(f"{relative}: expected one secondary Book Map sequence pager")
        if page_source.count('class="chapter-ledger-disclosure"') != 1:
            errors.append(f"{relative}: expected one progressive chapter status ledger")
        if collector.chapter_compass_count != 1:
            errors.append(f"{relative}: expected one source-and-Lean chapter compass")
        if collector.source_guide_count != 1:
            errors.append(f"{relative}: expected one textbook source guide")
        if collector.notation_primer_count != 1:
            errors.append(f"{relative}: expected one three-term notation primer")
        if collector.source_theorem_card_count < 1 and collector.source_boundary_count != 1:
            errors.append(f"{relative}: expected at least one source theorem or one explicit source boundary")
        if collector.source_theorem_card_count and collector.source_boundary_count:
            errors.append(f"{relative}: source theorem cards and a no-theorem boundary cannot coexist")
        if page_source.count('class="source-theorem-contract"') != collector.source_theorem_card_count:
            errors.append(f"{relative}: every source theorem needs one complete source contract")
        if page_source.count("Original at ") != collector.source_theorem_card_count:
            errors.append(f"{relative}: every source theorem needs one page-specific original-source link")
        if page_source.count("#page=") < collector.source_theorem_card_count + 1:
            errors.append(f"{relative}: source guide links are not page-specific")
        if collector.algorithm_flow_count != 1:
            errors.append(f"{relative}: expected one algorithm or proof flow")
        if collector.math_statement_count != collector.math_fallback_count or collector.math_statement_count != collector.math_tex_count:
            errors.append(
                f"{relative}: every mathematical statement needs one readable fallback and one escaped MathJax source"
            )
        if page_source.count('class="overflow-hint"') != collector.math_statement_count:
            errors.append(f"{relative}: every mathematical statement needs one mobile overflow hint")
        if collector.nested_math_errors:
            errors.append(f"{relative}: a mathematical statement swallowed teaching or Lean content")
        if collector.theorem_panel_count != collector.teaching_grid_count:
            errors.append(f"{relative}: theorem panel/teaching-grid structure mismatch")
        if page_source.count('class="technical-reading"') != collector.theorem_panel_count:
            errors.append(f"{relative}: every theorem panel needs one progressive technical disclosure")
        if collector.lean_code_count < collector.theorem_panel_count:
            errors.append(f"{relative}: theorem panel is missing an exact Lean statement")
        source_theorem_count = int(bool(readings_by_slug.get(chapter_slug, {}).get("source_theorem"))) + len(
            readings_by_slug.get(chapter_slug, {}).get("source_theorems", [])
        )
        if source_theorem_count > 1:
            if page_source.count('class="source-theorem-disclosure"') != source_theorem_count:
                errors.append(f"{relative}: multi-route source theorem disclosures are incomplete")
            if page_source.count('class="source-route-intro"') != 1:
                errors.append(f"{relative}: multi-route source guide lacks its compact orientation")
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

    ucb_page = output / "chapters" / "ucb" / "index.html"
    if ucb_page.exists():
        ucb_source = ucb_page.read_text(encoding="utf-8")
        for required in (
            "Source theorem contract",
            "Algorithm parameters",
            "Regret notion",
            "Closest local match to the source theorem",
            "Compiled extension",
            "Why an optimistic choice becomes a regret bound",
            "Reading boundary",
        ):
            if required not in ucb_source:
                errors.append(f"chapters/ucb/index.html: missing source-to-Lean guide {required!r}")
        if ucb_source.count('class="proof-bridge-step"') != 4:
            errors.append("chapters/ucb/index.html: expected four source-to-Lean proof-bridge steps")
        if 'href="#proof-bridge"' not in ucb_source:
            errors.append("chapters/ucb/index.html: proof bridge is missing from the page table of contents")
        closest_name = (
            "integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_"
            "le_textbookGapSum_finiteArmSubgaussianLaws_without_proxy_positivity"
        )
        anytime_name = "lintegral_ofReal_pseudoRegret_selectedPolicySuccessorTelescoping_le_trajMeasure"
        if ucb_source.find(closest_name) > ucb_source.find(anytime_name):
            errors.append("chapters/ucb/index.html: closest textbook UCB route must precede extensions")

    milestone_path = output / "implementation-map" / "milestone-data.json"
    module_data_path = output / "implementation-map" / "module-data.json"
    implementation_path = output / "implementation-map" / "index.html"
    if milestone_path.exists() and implementation_path.exists():
        milestone_payload = json.loads(milestone_path.read_text(encoding="utf-8"))
        milestone_items = milestone_payload.get("items", [])
        if len(milestone_items) != manifest.get("milestone_count"):
            errors.append("milestone-data.json count does not match manifest milestone_count")
        implementation_source = implementation_path.read_text(encoding="utf-8")
        initial_rows = implementation_source.count("data-milestone-row")
        page_size = milestone_payload.get("page_size")
        if initial_rows != min(page_size, len(milestone_items)):
            errors.append("Implementation Map initial milestone DOM does not match its page size")
        for required in ("data-milestone-more", "milestone-data.json"):
            if required not in implementation_source:
                errors.append(f"Implementation Map lacks progressive milestone support: {required}")
    else:
        errors.append("Implementation Map progressive milestone ledger is missing")
    if module_data_path.exists() and implementation_path.exists():
        module_payload = json.loads(module_data_path.read_text(encoding="utf-8"))
        module_items = module_payload.get("items", [])
        if len(module_items) != manifest.get("module_count"):
            errors.append("module-data.json count does not match manifest module_count")
        implementation_source = implementation_path.read_text(encoding="utf-8")
        initial_module_rows = implementation_source.count("data-module-row")
        module_page_size = module_payload.get("page_size")
        if initial_module_rows != min(module_page_size, len(module_items)):
            errors.append("Implementation Map initial module DOM does not match its page size")
        for required in ("data-module-more", "module-data.json"):
            if required not in implementation_source:
                errors.append(f"Implementation Map lacks progressive module support: {required}")
    else:
        errors.append("Implementation Map progressive module inventory is missing")
    if chapter_source_theorems != manifest.get("source_theorem_count"):
        errors.append(
            f"source theorem cards {chapter_source_theorems} != manifest source_theorem_count "
            f"{manifest.get('source_theorem_count')}"
        )
    if chapter_source_boundaries > expected_chapter_count:
        errors.append("source-boundary count exceeds the number of Book Map chapters")
    if manifest.get("reading_count") != expected_chapter_count:
        errors.append("manifest reading_count does not cover all Book Map chapters")
    for spine_page in spine_pages:
        collector = pages.get(spine_page.resolve())
        if collector is None:
            continue
        relative = spine_page.relative_to(output)
        page_source = spine_page.read_text(encoding="utf-8")
        if page_source.count('class="chapter-pager"') != 1:
            errors.append(f"{relative}: expected one Part IV sequence pager")
        if collector.algorithm_flow_count != 1:
            errors.append(f"{relative}: expected one maintainable proof or algorithm flow")
        if "Open Chapter " not in page_source or "#page=" not in page_source:
            errors.append(f"{relative}: Part IV source map lacks a page-specific textbook link")
        if collector.math_statement_count < 1:
            errors.append(f"{relative}: expected at least one mathematical statement")
        if collector.math_statement_count != collector.math_fallback_count or collector.math_statement_count != collector.math_tex_count:
            errors.append(
                f"{relative}: every spine mathematical statement needs one fallback and one MathJax source"
            )
        if page_source.count('class="overflow-hint"') != collector.math_statement_count:
            errors.append(f"{relative}: every spine mathematical statement needs one mobile overflow hint")
        if collector.nested_math_errors:
            errors.append(f"{relative}: a spine mathematical statement swallowed Lean or teaching content")
        for required in (PRIMARY_TEXTBOOK_TITLE, PRIMARY_TEXTBOOK_URL, "10.1017/9781108571401"):
            if required not in page_source:
                errors.append(f"{relative}: missing canonical textbook metadata {required}")
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

    catalog_data_path = output / "catalog-data.json"
    catalog_data = {}
    if not catalog_data_path.exists():
        errors.append("missing catalog-data.json")
    else:
        try:
            catalog_data = json.loads(catalog_data_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as error:
            errors.append(f"catalog-data.json: invalid JSON: {error}")
    catalog_items = catalog_data.get("items", []) if isinstance(catalog_data, dict) else []
    catalog_page_size = catalog_data.get("page_size") if isinstance(catalog_data, dict) else None
    if catalog_data.get("schema_version") != 2:
        errors.append("catalog-data.json: schema_version must be 2")
    if catalog_page_size != 100:
        errors.append("catalog-data.json: page_size must remain 100")
    if len(catalog_items) != manifest.get("declaration_count"):
        errors.append(
            f"catalog-data count {len(catalog_items)} != declaration_count {manifest.get('declaration_count')}"
        )
    for item in catalog_items:
        if not isinstance(item, list) or len(item) != 10:
            errors.append("catalog-data.json: compact declaration row must have 10 fields")
            break
    catalog_names = [item[0] for item in catalog_items if isinstance(item, list) and len(item) == 10]
    if len(catalog_names) != len(set(catalog_names)):
        errors.append("catalog-data.json: declaration names must be unique")
    search_urls_by_name = {
        item.get("name"): item.get("url") for item in search_items if isinstance(item, dict)
    }
    catalog_page_path = output / "declarations" / "index.html"
    for item in catalog_items:
        if not isinstance(item, list) or len(item) != 10:
            continue
        name, _kind, _module, module_slug, _chapter, _chapter_title, _status, _file, _line, anchor = item
        catalog_split = urlsplit(f"../modules/{module_slug}/index.html#{anchor}")
        search_split = urlsplit(str(search_urls_by_name.get(name, "")))
        catalog_target = (catalog_page_path.parent / catalog_split.path).resolve()
        search_target = (output / search_split.path).resolve()
        if catalog_target != search_target or catalog_split.fragment != search_split.fragment:
            errors.append(
                f"catalog-data.json: declaration URL disagrees with search-index for {name}"
            )
            break
    if catalog_data_path.exists() and catalog_data_path.stat().st_size > 6_000_000:
        errors.append("catalog-data.json: compact payload exceeds the 6 MB performance budget")
    if catalog_page_path.exists():
        catalog_page_source = catalog_page_path.read_text(encoding="utf-8")
        initial_catalog_rows = catalog_page_source.count("data-catalog-row")
        expected_initial_rows = min(catalog_page_size or 0, manifest.get("declaration_count", 0))
        if initial_catalog_rows != expected_initial_rows:
            errors.append(
                f"declarations/index.html: expected {expected_initial_rows} initial catalog rows, found {initial_catalog_rows}"
            )
        for required in (
            "data-catalog-body", "data-catalog-more", 'aria-live="polite"',
            'aria-label="Lean declaration catalog"', "data-catalog-more hidden",
            'href="../catalog-data.json"', 'href="../implementation-map/index.html"',
        ):
            if required not in catalog_page_source:
                errors.append(f"declarations/index.html: missing progressive catalog support {required}")

    highlight_payload = json.loads(
        (SITE_DIR / "content" / "highlights.json").read_text(encoding="utf-8")
    )
    highlights_by_chapter: dict[str, list[dict]] = defaultdict(list)
    for highlight in highlight_payload.get("highlights", []):
        highlights_by_chapter[highlight.get("chapter", "")].append(highlight)
    for chapter, chapter_highlights in highlights_by_chapter.items():
        if len(chapter_highlights) <= 6:
            continue
        featured = [item for item in chapter_highlights if item.get("featured") is True]
        if not featured or len(featured) > 6:
            errors.append(
                f"highlights.json: {chapter} needs one to six explicit featured teaching notes"
            )

    succinct_declaration = (
        "BanditRLProof.LowerBounds.Succinct.SuccinctUnitSystem."
        "IsSuccinctSupport.sourceQ_supportCombination_eq"
    )
    succinct_items = [item for item in search_items if item.get("name") == succinct_declaration]
    if len(succinct_items) != 1 or succinct_items[0].get("chapter") != "Frontier":
        errors.append("succinct geometry declarations must resolve to the Frontier chapter")
    sgb_prefix_declaration = (
        "BanditRLProof.Thompson."
        "latentArmStreamTrajectoryMeasure_map_stream_visiblePrefix_eq"
    )
    sgb_prefix_items = [item for item in search_items if item.get("name") == sgb_prefix_declaration]
    if len(sgb_prefix_items) != 1 or sgb_prefix_items[0].get("chapter") != "Frontier":
        errors.append("SGB deferred-decisions prefix declarations must resolve to the Frontier chapter")
    sgb_action_declaration = (
        "BanditRLProof.Thompson."
        "latentArmStreamTrajectoryMeasure_map_visiblePrefix_nextAction_eq_compProd"
    )
    sgb_action_items = [
        item for item in search_items if item.get("name") == sgb_action_declaration
    ]
    if len(sgb_action_items) != 1 or sgb_action_items[0].get("chapter") != "Frontier":
        errors.append("SGB next-action factorization must resolve to the Frontier chapter")
    sgb_branch_declaration = (
        "BanditRLProof.Thompson."
        "latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod"
    )
    sgb_branch_items = [
        item for item in search_items if item.get("name") == sgb_branch_declaration
    ]
    if len(sgb_branch_items) != 1 or sgb_branch_items[0].get("chapter") != "Frontier":
        errors.append("SGB unconditional branch product must resolve to the Frontier chapter")
    sgb_freshness_declarations = (
        "BanditRLProof.Thompson.latentArmStreamVisibleNextReward_joint_eq_compProd",
        "BanditRLProof.Thompson.latentArmStreamVisibleNextReward_condDistrib_ae_eq_nu",
        (
            "BanditRLProof.Thompson."
            "latentArmStreamVisibleTrajectoryMeasure_nextReward_joint_eq_compProd"
        ),
        (
            "BanditRLProof.Thompson."
            "latentArmStreamVisibleTrajectoryMeasure_nextReward_condDistrib_ae_eq_nu"
        ),
    )
    for declaration in sgb_freshness_declarations:
        freshness_items = [
            item for item in search_items if item.get("name") == declaration
        ]
        if len(freshness_items) != 1 or freshness_items[0].get("chapter") != "Frontier":
            errors.append(
                "SGB deterministic-time selected-reward freshness must resolve to the "
                f"Frontier chapter: {declaration}"
            )
            continue
        freshness_target = urlsplit(freshness_items[0]["url"])
        freshness_module_path = output / freshness_target.path
        if not freshness_module_path.exists():
            errors.append(f"SGB freshness declaration page is missing: {declaration}")
            continue
        freshness_module_source = freshness_module_path.read_text(encoding="utf-8")
        compiled_summary = re.compile(
            rf'<details class="declaration" id="{re.escape(freshness_target.fragment)}">'
            r"\s*<summary>.*?"
            r'<span class="status compiled">Compiled</span>.*?</summary>',
            re.DOTALL,
        )
        if not compiled_summary.search(freshness_module_source):
            errors.append(
                "SGB deterministic-time selected-reward freshness is not rendered as "
                f"compiled: {declaration}"
            )
    sgb_native_prefix_declaration = (
        "BanditRLProof.Thompson."
        "latentArmStreamVisibleTrajectoryMeasure_map_frestrictLe_eq_native"
    )
    sgb_native_prefix_items = [
        item for item in search_items if item.get("name") == sgb_native_prefix_declaration
    ]
    if (
        len(sgb_native_prefix_items) != 1
        or sgb_native_prefix_items[0].get("chapter") != "Frontier"
    ):
        errors.append("SGB native-prefix identification must resolve to the Frontier chapter")
    else:
        native_prefix_target = urlsplit(sgb_native_prefix_items[0]["url"])
        native_prefix_module_path = output / native_prefix_target.path
        if not native_prefix_module_path.exists():
            errors.append("SGB native-prefix declaration page is missing")
        else:
            native_prefix_module_source = native_prefix_module_path.read_text(encoding="utf-8")
            compiled_summary = re.compile(
                rf'<details class="declaration" id="{re.escape(native_prefix_target.fragment)}">'
                r"\s*<summary>.*?"
                r'<span class="status compiled">Compiled</span>.*?</summary>',
                re.DOTALL,
            )
            if not compiled_summary.search(native_prefix_module_source):
                errors.append("SGB native-prefix identification is not rendered as compiled")
    frontier_source = (output / "chapters" / "frontier" / "index.html").read_text(encoding="utf-8")
    for required in (
        "A Novel General Framework for Sharp Lower Bounds in Succinct Stochastic Bandits",
        "physical PDF pp. 4–5",
        "Definitions 3.1–3.3 and Lemmas 3.1–3.4",
        "Does Stochastic Gradient really succeed for Bandits?",
        "Theorem 1 (two-arm SGB regret upper bound)",
        "Corollary 1 (horizon-indexed two-arm SGB rate)",
        "physical PDF p. 5",
        "Theorem 2 (two-arm SGB phase transition)",
        "physical PDF p. 6; Appendix C pp. 31–40",
        "360 = 223 + 23 + 24 + 26 + 7 + 8 + 13 + 28 + 8",
        "LatentArmStreamVisiblePrefixNextActionBranchLocality",
        sgb_action_declaration,
        sgb_branch_declaration,
        *sgb_freshness_declarations,
        "identifies every inclusive finite prefix",
        "proves equality of the complete visible/native trajectory measures",
        "twoArmAppendixCMissingPullLatentPhaseEvent_subset_terminalCountBelow",
        "terminal-count-below event still needs an expected-regret consumer",
        "Pull-ordered or stopped selected-reward IID",
        (
            "stopped-prefix future-cylinder law needed to prove conditional "
            "no-return probability at least one half"
        ),
        "frozen terminal twoArmRademacherDirac_theoremTwo_polynomialRegret",
    ):
        if required not in frontier_source:
            errors.append(f"Frontier reading guide is missing source or status metadata: {required}")

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
    source_links: list[str] = []
    for collector in pages.values():
        totals["mermaid"] += collector.mermaid_count
        totals["diagram_regions"] += collector.diagram_region_count
        totals["accessible_diagram_regions"] += collector.accessible_diagram_region_count
        totals["mathjax"] += collector.mathjax_count
        totals["source_links"] += collector.source_link_count
        source_links.extend(collector.source_links)
    if totals["mermaid"] < 7:
        errors.append(f"expected at least 7 rendered Mermaid blocks, found {totals['mermaid']}")
    if totals["diagram_regions"] != totals["mermaid"]:
        errors.append("every Mermaid block must be contained by one diagram region")
    if totals["accessible_diagram_regions"] != totals["diagram_regions"]:
        errors.append("every diagram must be a labelled keyboard-scroll region")
    site_js = (output / "static" / "site.js").read_text(encoding="utf-8")
    for required in (
        "fitFlowchartViewBoxes",
        'svg[aria-roledescription^="flowchart"]',
        'flowchart: { htmlLabels: true',
        "labelOverflowRegions();",
    ):
        if required not in site_js:
            errors.append(f"site.js is missing the maintainable flowchart-fit hook: {required}")
    for required in (
        "data-toc-toggle",
        "setTocOpen",
        "syncTocCurrent",
        'setAttribute("aria-current", "location")',
        "math-fallback-active",
        "data-nav-group",
        "abrl-nav-groups-v2",
        'event.key !== "/"',
        'classList.toggle("is-scrollable"',
    ):
        if required not in site_js:
            errors.append(f"site.js is missing responsive reading support: {required}")
    for required in (
        "catalog-data.json",
        "catalogVisibleLimit",
        "catalogLoadPromise",
        "data-catalog-more",
        "data-catalog-body",
        'class="status ${escapeHtml(item.status)}"',
        "payload.kind_labels",
        "payload.source_base",
    ):
        if required not in site_js:
            errors.append(f"site.js is missing progressive catalog support: {required}")
    for required in (
        "enhanceLeanCodeBlocks",
        "data-code-wrap",
        "data-code-copy",
        "navigator.clipboard.writeText",
        'classList.toggle("wrap-lines"',
        'classList.toggle("scroll-lines"',
    ):
        if required not in site_js:
            errors.append(f"site.js is missing Lean code display controls: {required}")
    for required in (
        "milestone-data.json",
        "milestoneLoadPromise",
        "data-milestone-more",
        "revealMilestoneFragment",
    ):
        if required not in site_js:
            errors.append(f"site.js is missing progressive milestone support: {required}")
    for required in (
        "module-data.json",
        "moduleLoadPromise",
        "data-module-more",
        "revealModuleFragment",
    ):
        if required not in site_js:
            errors.append(f"site.js is missing progressive module support: {required}")
    for required in (
        "bringTargetIntoView",
        "collapsedTocHeight",
        "window.MathJax?.startup?.promise?.then(bringTargetIntoView)",
        "regionOverflows || mathTargetOverflows",
        "focus({ preventScroll: true })",
    ):
        if required not in site_js:
            errors.append(f"site.js is missing stabilized mobile deep-link or overflow support: {required}")
    if "status-badge status-" in site_js:
        errors.append("site.js uses a status class that disagrees with the generated status badge contract")
    workflow_source = (output / "workflow" / "index.html").read_text(encoding="utf-8")
    for required in ("master–worker", "does not yet justify", "harness-compare"):
        if required not in workflow_source:
            errors.append(f"workflow page is missing adaptive-harness boundary {required!r}")
    learning_path = (SITE_DIR / "diagrams" / "learning-path.mmd").read_text(encoding="utf-8")
    if re.search(r'\["[0-9]+\.', learning_path):
        errors.append(
            "learning-path Mermaid labels must not begin with ordered-list syntax; "
            "use zero-padded labels with a middle dot"
        )
    for required in ("01 · Foundations", "10 · Frontier + contribution workflow"):
        if required not in learning_path:
            errors.append(f"learning-path Mermaid is missing the safe chapter label: {required}")
    implementation_source = (output / "implementation-map" / "index.html").read_text(
        encoding="utf-8"
    )
    if implementation_source.count('class="diagram dependency-diagram') != 6:
        errors.append(
            "Implementation Map must retain one overview and five focused dependency diagrams"
        )
    if totals["mathjax"] != len(pages):
        errors.append(f"MathJax is not loaded on every HTML page ({totals['mathjax']} of {len(pages)})")
    if totals["source_links"] < manifest.get("declaration_count", 0):
        errors.append(
            f"expected at least one source link per declaration; found {totals['source_links']} for {manifest.get('declaration_count')}"
        )
    if expected_public_base_url:
        source_commit = manifest.get("source_commit", "")
        expected_source_prefix = f"{GITHUB_REPO}/blob/{source_commit}/BanditRLProof"
        redirected = [value for value in source_links if "/source-access/" in value]
        unpinned = [
            value for value in source_links
            if not value.startswith(expected_source_prefix)
        ]
        declaration_links = [
            value for value in source_links
            if value.startswith(expected_source_prefix)
            and re.search(r"#L[1-9][0-9]*$", value)
        ]
        if redirected:
            errors.append("public snapshot redirects exact source links to source-access")
        if unpinned:
            errors.append("public snapshot contains source links not pinned to source_commit")
        if len(set(declaration_links)) != manifest.get("declaration_count", 0):
            errors.append(
                "public snapshot does not retain exactly one unique commit-pinned file/line target per declaration"
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
        f"- BanditRLwiki settings/cases/papers: {manifest.get('banditrlwiki_family_count')}/"
        f"{manifest.get('banditrlwiki_case_count')}/{manifest.get('banditrlwiki_paper_count')}\n"
        f"- BanditRLwiki theorem surfaces: {manifest.get('banditrlwiki_theorem_surface_count')}\n"
        f"- BanditRLwiki literature-open/formalization-open cases: "
        f"{manifest.get('banditrlwiki_literature_open_count')}/"
        f"{manifest.get('banditrlwiki_formalization_open_case_count')}\n"
        f"- BanditRLwiki named formalization leaves: "
        f"{manifest.get('banditrlwiki_formalization_leaf_count')}\n"
        f"- BanditRLwiki active source-frozen ports: "
        f"{manifest.get('banditrlwiki_active_source_audit_count')}\n"
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
