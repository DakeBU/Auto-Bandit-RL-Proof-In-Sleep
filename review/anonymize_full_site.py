#!/usr/bin/env python3
"""Post-process the complete generated BanditRLlib site for double-blind review.

This script changes reviewer-facing identity and provenance surfaces only. It does
not rewrite Lean sources, theorem statements, source-audit status, proof-graph
semantics, or mathematical evidence.
"""
from __future__ import annotations

import argparse
import html
import re
from pathlib import Path
from urllib.parse import unquote

PUBLIC_REPO = "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep"
PUBLIC_SITE = "https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep"

PROJECT_NAMES = [
    "Dake Bu",
    "Ji Cheng",
    "Bo Xue",
    "Atsushi Nitanda",
    "Hau-San Wong",
    "Qingfu Zhang",
]
PROJECT_AFFILIATIONS = [
    "City University of Hong Kong",
    "Centre for Frontier AI Research",
]
TEXT_SUFFIXES = {
    ".html", ".htm", ".css", ".js", ".json", ".txt", ".xml", ".svg",
    ".md", ".yaml", ".yml", ".csv",
}


def rewrite_links(text: str) -> str:
    # Keep links within the deployed site local to the anonymous domain.
    text = text.replace(PUBLIC_SITE + "/", "/")
    text = text.replace(PUBLIC_SITE, "/")

    # Raw development-repository links are deliberately not exposed by the
    # website. Reviewers receive the anonymous source repository separately.
    text = re.sub(
        r"https://github\.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep(?:/[^\s\"'<>)]*)?",
        "#anonymous-source",
        text,
    )

    # Other author-controlled repository/site links are not necessary to review
    # this artifact and can reveal identity through the account name.
    text = re.sub(
        r"https://github\.com/DakeBU(?:/[^\s\"'<>)]*)?",
        "#anonymous-author-artifact",
        text,
    )
    text = re.sub(
        r"https://dakebu\.github\.io(?:/[^\s\"'<>)]*)?",
        "#anonymous-author-artifact",
        text,
        flags=re.I,
    )
    return text


def strip_author_sections(text: str) -> str:
    # Generated homepage contributor blocks are presentation, not mathematics.
    text = re.sub(
        r"<section id=\"contributors\".*?</section>",
        '<section id="contributors"><p class="eyebrow">Double-blind review</p><h2>Authors</h2><p>Anonymous during review.</p></section>',
        text,
        flags=re.I | re.S,
    )
    text = re.sub(
        r"<p[^>]*>\s*<strong>Authors?:</strong>.*?</p>",
        '<p><strong>Authors:</strong> Anonymous during review.</p>',
        text,
        flags=re.I | re.S,
    )
    return text


def inject_review_headers(text: str) -> str:
    if "<head" not in text.lower():
        return text
    insertion = (
        '<meta name="robots" content="noindex,nofollow,noarchive">\n'
        '<meta name="referrer" content="no-referrer">\n'
    )
    if 'name="robots"' not in text.lower():
        text = re.sub(r"(<head[^>]*>)", r"\1\n" + insertion, text, count=1, flags=re.I)
    elif 'name="referrer"' not in text.lower():
        text = re.sub(
            r"(<head[^>]*>)",
            r'\1\n<meta name="referrer" content="no-referrer">',
            text,
            count=1,
            flags=re.I,
        )
    return text


def rewrite_text(text: str, *, is_html: bool) -> str:
    text = strip_author_sections(text)
    text = rewrite_links(text)
    for name in PROJECT_NAMES:
        text = text.replace(name, "Anonymous Author")
    for affiliation in PROJECT_AFFILIATIONS:
        text = text.replace(affiliation, "Anonymous Institution")

    # User/account handles and local provenance strings.
    text = re.sub(r"(?i)DakeBU", "anonymous", text)
    text = re.sub(r"(?i)jicheng9617", "anonymous", text)
    text = re.sub(r"(?i)Auto-Bandit-RL-Proof-In-Sleep", "BanditRLlib-Review", text)
    text = re.sub(r"(?i)[A-Za-z0-9._%+-]+@(?:users\.noreply\.)?github\.com", "anonymous@example.invalid", text)
    text = re.sub(r"(?i)[A-Za-z0-9._%+-]+@cityu\.edu\.hk", "anonymous@example.invalid", text)

    if is_html:
        text = inject_review_headers(text)
    return text


def scan(root: Path) -> list[str]:
    blocked = [
        re.compile(r"Dake\s+Bu", re.I),
        re.compile(r"Ji\s+Cheng", re.I),
        re.compile(r"Bo\s+Xue", re.I),
        re.compile(r"Atsushi\s+Nitanda", re.I),
        re.compile(r"Hau[- ]San\s+Wong", re.I),
        re.compile(r"Qingfu\s+Zhang", re.I),
        re.compile(r"DakeBU", re.I),
        re.compile(r"jicheng9617", re.I),
        re.compile(r"github\.com/DakeBU", re.I),
        re.compile(r"dakebu\.github\.io", re.I),
        re.compile(r"Auto-Bandit-RL-Proof-In-Sleep", re.I),
        re.compile(r"City University of Hong Kong", re.I),
    ]
    problems: list[str] = []
    for path in root.rglob("*"):
        if not path.is_file() or path.suffix.lower() not in TEXT_SUFFIXES:
            continue
        try:
            text = html.unescape(unquote(path.read_text(encoding="utf-8")))
        except UnicodeDecodeError:
            continue
        for pattern in blocked:
            if pattern.search(text):
                problems.append(f"{path.relative_to(root)}: {pattern.pattern}")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("site", type=Path)
    args = parser.parse_args()
    root = args.site.resolve()
    if not root.is_dir():
        raise SystemExit(f"site directory not found: {root}")

    changed = 0
    for path in root.rglob("*"):
        if not path.is_file() or path.suffix.lower() not in TEXT_SUFFIXES:
            continue
        try:
            before = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        after = rewrite_text(before, is_html=path.suffix.lower() in {".html", ".htm"})
        if after != before:
            path.write_text(after, encoding="utf-8")
            changed += 1

    (root / "robots.txt").write_text("User-agent: *\nDisallow: /\n", encoding="utf-8")
    (root / "_headers").write_text(
        "/*\n"
        "  X-Robots-Tag: noindex, nofollow, noarchive\n"
        "  Referrer-Policy: no-referrer\n"
        "  X-Content-Type-Options: nosniff\n"
        "  Permissions-Policy: camera=(), microphone=(), geolocation=()\n",
        encoding="utf-8",
    )

    problems = scan(root)
    if problems:
        print("Anonymous BanditRLlib identity scan: FAIL")
        for item in problems[:100]:
            print(" -", item)
        return 1

    required = [
        "index.html",
        "banditrlwiki/index.html",
        "banditrlwiki/frontier/index.html",
        "declarations/index.html",
        "ide/index.html",
    ]
    missing = [rel for rel in required if not (root / rel).exists()]
    if missing:
        print("Anonymous BanditRLlib required-page check: FAIL")
        for rel in missing:
            print(" - missing", rel)
        return 1

    print(f"Anonymous BanditRLlib post-processing: PASS ({changed} files rewritten)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
