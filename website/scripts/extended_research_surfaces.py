#!/usr/bin/env python3
"""Generated research/publication surfaces added by the strict contributor contract."""

from __future__ import annotations

import html
import json
from collections import Counter
from pathlib import Path
from typing import Any, Callable


def _load(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _safe_mermaid(value: str) -> str:
    return value.replace('"', "'").replace("\n", " ")


def build_extended_research_surfaces(
    output: Path,
    *,
    layout: Callable[..., str],
    write_page: Callable[[Path, str, str], None],
    href_from: Callable[[str, str], str],
    public_repo_dir: Path,
    content_dir: Path,
    github_repo: str,
    verified: bool,
    generated_at: str,
) -> None:
    """Build atlas/frontier/Functor surfaces through the canonical site layout.

    These pages deliberately share the same sidebar, canonical/social metadata,
    MathJax, favicon, search shortcut, and verification banner as the rest of
    BanditRLlib.  They replace the earlier hand-written HTML prototypes.
    """

    atlas = _load(public_repo_dir / "data" / "setting-atlas.json")
    frontier = _load(public_repo_dir / "data" / "frontier-problems.json")
    functor = _load(content_dir / "functor_hypergraph.json")
    techniques = _load(content_dir / "bandit_technique_map.json")
    frontier_audits = _load(content_dir / "frontier_source_audits.json")

    _build_setting_atlas(
        output, atlas, techniques, layout, write_page, href_from, verified, generated_at
    )
    _build_technique_map(
        output, atlas, techniques, layout, write_page, href_from, verified, generated_at
    )
    _build_frontier_registry(
        output, frontier, frontier_audits, layout, write_page, href_from, verified, generated_at
    )
    _build_gap_entropy_case(
        output, frontier, layout, write_page, href_from, verified, generated_at
    )
    _build_gap_entropy_graph(
        output, layout, write_page, href_from, verified, generated_at
    )
    _build_functor_hypergraph(
        output, functor, techniques, layout, write_page, href_from, github_repo, verified, generated_at
    )


def _build_setting_atlas(
    output: Path,
    atlas: dict[str, Any],
    techniques: dict[str, Any],
    layout: Callable[..., str],
    write_page: Callable[[Path, str, str], None],
    href_from: Callable[[str, str], str],
    verified: bool,
    generated_at: str,
) -> None:
    page = "banditrlwiki/setting-atlas/index.html"
    axes = {axis["id"]: axis["title"] for axis in atlas["axes"]}
    counts = Counter(item["site_status"] for item in atlas["entries"])
    represented = sum(
        count for status, count in counts.items()
        if "covered" in status or status == "mentioned-not-indexed"
    )

    technique_by_setting: dict[str, list[dict[str, Any]]] = {}
    for technique in techniques.get("techniques", []):
        for setting_id in technique.get("setting_ids", []):
            technique_by_setting.setdefault(setting_id, []).append(technique)

    groups = []
    for axis in atlas["axes"]:
        rows = [item for item in atlas["entries"] if item["axis"] == axis["id"]]
        cards = []
        for item in sorted(rows, key=lambda x: (x["priority"], x["title"])):
            aliases = ""
            if item.get("aliases"):
                aliases = (
                    "<p><small><strong>Aliases.</strong> "
                    + html.escape(", ".join(item["aliases"]))
                    + "</small></p>"
                )
            linked_techniques = technique_by_setting.get(item["id"], [])
            technique_links = ""
            if linked_techniques:
                technique_links = (
                    '<p><strong>Technique map.</strong> '
                    + ' · '.join(
                        f'<a href="{href_from(page, "banditrlwiki/technique-map/index.html")}#technique-{html.escape(t["id"])}">{html.escape(t["title"])}</a>'
                        for t in linked_techniques
                    )
                    + '</p>'
                )
            cards.append(
                f"""<article class="info-card" id="setting-{html.escape(item['id'])}">
<p class="panel-kicker">{html.escape(item['priority'])} · {html.escape(item['kind'])} · {html.escape(item['site_status'])}</p>
<h3>{html.escape(item['title'])}</h3>
<p>{html.escape(item['summary'])}</p>{aliases}{technique_links}
</article>"""
            )
        groups.append(
            f"""<section id="axis-{html.escape(axis['id'])}">
<h2>{html.escape(axis['title'])} <small>· {len(rows)}</small></h2>
<div class="card-grid">{''.join(cards)}</div>
</section>"""
        )

    body = f"""
<section class="hero" id="atlas">
  <p class="eyebrow">Canonical multi-axis taxonomy</p>
  <h1 class="page-title">{html.escape(atlas['title'])}</h1>
  <p class="lede">{html.escape(atlas['scope'])}</p>
  <div class="stats-grid">
    <div class="stat"><span class="stat-value">{len(atlas['entries'])}</span><span class="stat-label">canonical entries</span></div>
    <div class="stat"><span class="stat-value">{represented}</span><span class="stat-label">represented or mentioned</span></div>
    <div class="stat"><span class="stat-value">{counts.get('missing-topic', 0)}</span><span class="stat-label">missing explicit topic</span></div>
    <div class="stat"><span class="stat-value">{counts.get('quarantine', 0)}</span><span class="stat-label">aliases needing source disambiguation</span></div>
  </div>
  <div class="hero-actions">
    <a class="button primary" href="{href_from(page, 'banditrlwiki/technique-map/index.html')}">Technique Map</a>
    <a class="button" href="{href_from(page, 'banditrlwiki/index.html')}">Bound &amp; Source Atlas</a>
    <a class="button" href="{href_from(page, 'banditrlwiki/frontier-problems/index.html')}">Frontier · open problems</a>
  </div>
</section>
<section id="taxonomy-rule">
  <h2>Do not flatten settings, objectives, and methods</h2>
  <p>BAI and regret minimization are objectives; Thompson sampling and GP-UCB are methods; LLM is an application bridge. A result becomes comparable only after the environment/action class, feedback, objective, probability mode, parameters, computation/oracle assumptions and theorem source are fixed.</p>
  <div class="callout warning"><strong>Ambiguous acronyms stay quarantined.</strong> OMDP, SLB and Transform require a cited source before canonicalization. In particular, SLB is used in the literature for both stochastic linear bandits and safe linear bandits, so the bare acronym is not merged into either node.</div>
</section>
{''.join(groups)}
<section id="maintenance">
  <h2>Contributor rule</h2>
  <p>Adding a setting name is not enough. A substantive update must use the repository contribution contract, connect the affected reader/route/progress surfaces, and classify its Lean Graph and Functor Hypergraph delta.</p>
  <p><a href="{href_from(page, 'community/index.html#codex-contract')}">Read the contributor/Codex publication contract →</a></p>
</section>
"""
    toc = [("atlas", "Atlas"), ("taxonomy-rule", "Taxonomy rule")]
    toc.extend((f"axis-{axis['id']}", axis["title"]) for axis in atlas["axes"])
    toc.append(("maintenance", "Contributor rule"))
    write_page(
        output,
        page,
        layout(page, atlas["title"], body, toc, "banditrlwiki-setting-atlas", verified, generated_at, wide=True),
    )


def _problem_card(page: str, problem: dict[str, Any], href_from: Callable[[str, str], str]) -> str:
    source = problem["source"]
    case_link = ""
    if problem.get("case_url"):
        case_link = (
            f'<a href="{href_from(page, "banditrlwiki/frontier-problems/" + problem["case_url"])}">'
            "Open dedicated case →</a> · "
        )
    return f"""<article class="info-card">
<p class="panel-kicker">{html.escape(problem['priority'])} · {html.escape(problem['status'])}</p>
<h3>{html.escape(problem['title'])}</h3>
<p>{html.escape(problem['area'])}</p>
<p><strong>Posed by.</strong> {html.escape(str(problem['posed_by']))}{' · ' + str(problem['posed_year']) if problem.get('posed_year') else ''}</p>
<p><strong>Local Lean.</strong> {html.escape(problem['lean']['local_status'])}</p>
<p><strong>Graph delta.</strong> {html.escape(problem['graph_delta'])}</p>
<p>{case_link}<a href="{html.escape(source['url'], quote=True)}">Primary problem/source ↗</a></p>
</article>"""


def _build_frontier_registry(
    output: Path,
    frontier: dict[str, Any],
    frontier_audits: dict[str, Any],
    layout: Callable[..., str],
    write_page: Callable[[Path, str, str], None],
    href_from: Callable[[str, str], str],
    verified: bool,
    generated_at: str,
) -> None:
    page = "banditrlwiki/frontier-problems/index.html"
    counts = Counter(problem["status"] for problem in frontier["problems"])
    core = [p for p in frontier["problems"] if p.get("core_bandit_rl", True)]
    adjacent = [p for p in frontier["problems"] if not p.get("core_bandit_rl", True)]
    core_cards = "".join(_problem_card(page, p, href_from) for p in core)
    adjacent_cards = "".join(_problem_card(page, p, href_from) for p in adjacent)

    screened_cards = []
    for collection in frontier_audits.get("collections", []):
        routed = "".join(
            f"<li><strong>{html.escape(item['title'])}</strong> — {html.escape(item['classification'])}; "
            f"{html.escape(item['action'])}</li>"
            for item in collection.get("items", [])
        )
        screened_cards.append(
            f"""<article class="info-card">
<p class="panel-kicker">screened {html.escape(collection['screened_date'])}</p>
<h3>{html.escape(collection['title'])}</h3>
<p><strong>Core Bandit/RL items:</strong> {collection.get('core_bandit_rl_count', 0)} ·
<strong>Adjacent routed items:</strong> {collection.get('adjacent_project_count', 0)}</p>
<ul>{routed}</ul>
<p><a href="{html.escape(collection['source_url'], quote=True)}">Open source collection ↗</a></p>
</article>"""
        )
    screening = "".join(screened_cards)
    body = f"""
<section class="hero" id="registry">
  <p class="eyebrow">Posed → progress → resolution → formalization</p>
  <h1 class="page-title">{html.escape(frontier['title'])}</h1>
  <p class="lede">{html.escape(frontier['scope'])}</p>
  <div class="stats-grid">
    <div class="stat"><span class="stat-value">{len(core)}</span><span class="stat-label">core Bandit/RL histories</span></div>
    <div class="stat"><span class="stat-value">{sum(v for k,v in counts.items() if k.startswith('resolved'))}</span><span class="stat-label">resolved histories in this audit</span></div>
    <div class="stat"><span class="stat-value">{counts.get('source-open-current-audit',0)+counts.get('partial-current-audit',0)}</span><span class="stat-label">open/partial current audits</span></div>
    <div class="stat"><span class="stat-value">{counts.get('audit-needed',0)}</span><span class="stat-label">closure audits still needed</span></div>
  </div>
  <div class="hero-actions"><a class="button primary" href="{href_from(page, 'banditrlwiki/setting-atlas/index.html')}">Full Setting Atlas</a><a class="button" href="{href_from(page, 'banditrlwiki/frontier/index.html')}">Formalization frontier leaves</a></div>
</section>
<section id="status-contract">
  <h2>Mathematical openness and Lean openness are different ledgers</h2>
  <p>An old open-problem paper is discovery evidence, not proof that the problem is still open. Current closure status is dated and source-traceable; external/preprint/peer-reviewed resolutions stay distinct. Missing local Lean code is tracked separately.</p>
</section>
<section id="core-problems">
  <h2>Core Bandit / RL problem histories</h2>
  <p>These questions change a Bandit or reinforcement-learning theorem contract directly.</p>
  <div class="card-grid">{core_cards}</div>
</section>
<section id="adjacent-problems">
  <h2>Adjacent project frontier</h2>
  <p>These are useful to ABRL, but their mathematical contract belongs to Online Learning, optimization, statistics, games, or another cross-library route. They are intentionally not counted as core Bandit/RL open problems.</p>
  <div class="card-grid">{adjacent_cards if adjacent_cards else '<p class="empty">No adjacent problems indexed.</p>'}</div>
</section>
<section id="screened-sources">
  <h2>Screened open-problem collections</h2>
  <p>We record collections that were checked even when they contribute zero core Bandit/RL questions. This prevents “not listed” from being confused with “not audited”.</p>
  <div class="card-grid">{screening}</div>
</section>
<section id="contribute">
  <h2>How to add or update a problem history</h2>
  <p>Freeze the primary problem statement, current resolution evidence, publication status, exact Lean status and expected graph delta. Then use the same contributor contract as theorem work; a missing formalization must never be relabelled as a literature-open theorem.</p>
  <a href="{href_from(page, 'community/index.html#codex-contract')}">Contributor/Codex contract →</a>
</section>
"""
    write_page(
        output,
        page,
        layout(
            page,
            frontier["title"],
            body,
            [("registry", "Registry"), ("status-contract", "Status contract"), ("core-problems", "Core Bandit/RL"), ("adjacent-problems", "Adjacent routes"), ("screened-sources", "Screened sources"), ("contribute", "Contribute")],
            "banditrlwiki-frontier-problems",
            verified,
            generated_at,
            wide=True,
        ),
    )


def _build_gap_entropy_case(
    output: Path,
    frontier: dict[str, Any],
    layout: Callable[..., str],
    write_page: Callable[[Path, str, str], None],
    href_from: Callable[[str, str], str],
    verified: bool,
    generated_at: str,
) -> None:
    problem = next(p for p in frontier["problems"] if p["id"] == "gap-entropy-bai")
    page = "banditrlwiki/frontier-problems/gap-entropy/index.html"

    progress = "".join(
        f'<li><strong>{item["year"]}.</strong> <a href="{html.escape(item["url"], quote=True)}">{html.escape(item["title"])}</a> — {html.escape(item["note"])}</li>'
        for item in problem.get("progress", [])
    )
    resolution = "".join(
        f'<li><strong>{item["year"]}.</strong> <a href="{html.escape(item["url"], quote=True)}">{html.escape(item["title"])}</a> — {html.escape(item["note"])}</li>'
        for item in problem.get("resolution", [])
    )
    declarations = "".join(f"<li><code>{html.escape(name)}</code></li>" for name in problem["lean"]["declarations"])

    body = f"""
<section class="hero" id="case">
  <p class="eyebrow">P0 frontier history · external formalization bridge</p>
  <h1 class="page-title">{html.escape(problem['title'])}</h1>
  <p class="lede">This page preserves the decade-long problem history and the graph structure introduced by its resolution without pretending that an external Lean project is locally compiled.</p>
  <div class="hero-actions"><a class="button primary" href="{href_from(page, 'lean-graph/external/gap-entropy/index.html')}">Open external Lean graph bridge</a><a class="button" href="{href_from(page, 'banditrlwiki/frontier-problems/index.html')}">All frontier histories</a></div>
</section>
<section id="source">
  <h2>Original source problem</h2>
  <p><strong>{html.escape(problem['source']['title'])}</strong> · {html.escape(problem['posed_by'])} · {problem['posed_year']}</p>
  <p><a href="{html.escape(problem['source']['url'], quote=True)}">Open primary source ↗</a></p>
</section>
<section id="history">
  <h2>Progress and resolution</h2>
  <ul>{progress}{resolution}</ul>
</section>
<section id="lean">
  <h2>Formalization boundary</h2>
  <p>External status: <strong>{html.escape(problem['lean']['status'])}</strong>. BanditRLlib local status: <strong>{html.escape(problem['lean']['local_status'])}</strong>. The external repository uses {html.escape(problem['lean']['external_toolchain'])}; BanditRLlib currently uses {html.escape(problem['lean']['local_toolchain'])}.</p>
  <ul>{declarations}</ul>
  <div class="callout warning"><strong>Truth boundary.</strong> These declaration names are attributed external evidence. They are not local BanditRLlib compiled declarations until a source-faithful toolchain/port decision passes the local project gate.</div>
</section>
<section id="graph-delta">
  <h2>Why this belongs in the proof graph</h2>
  <p>{html.escape(problem['graph_delta'])}</p>
  <p>The contribution should be audited as possible <strong>bridge/hub</strong> structure, not merely as one terminal BAI theorem: gap-scale grouping, an order-oblivious benchmark, policy representation, information lower bounds and a universal algorithm sit between generic probability infrastructure and the final sample-complexity claim.</p>
</section>
"""
    write_page(
        output,
        page,
        layout(
            page,
            "Gap-Entropy frontier history",
            body,
            [("case", "Case"), ("source", "Source"), ("history", "History"), ("lean", "Lean boundary"), ("graph-delta", "Graph delta")],
            "banditrlwiki-frontier-problems",
            verified,
            generated_at,
        ),
    )


def _build_gap_entropy_graph(
    output: Path,
    layout: Callable[..., str],
    write_page: Callable[[Path, str, str], None],
    href_from: Callable[[str, str], str],
    verified: bool,
    generated_at: str,
) -> None:
    page = "lean-graph/external/gap-entropy/index.html"
    body = f"""
<section class="hero" id="bridge">
  <p class="eyebrow">External formalization bridge · P0</p>
  <h1 class="page-title">GapEntropy → BanditRLlib graph slice</h1>
  <p class="lede">Externally kernel-checked declarations are mapped against BanditRLlib's BAI, probability and information-theoretic routes without being promoted to local proof dependencies.</p>
  <div class="callout warning"><strong>Verification boundary.</strong> The external project is frozen at a pinned commit and uses a different Lean toolchain. External/source nodes and conceptual-overlap edges remain overlays; only BanditRLlib's own compiled nodes inherit local verification status.</div>
</section>
<section id="explorer">
  <div class="lean-graph-app" data-lean-graph data-graph-overview-source="gap-entropy.json" data-graph-search-source="search-index.json">
    <header class="lean-graph-toolbar">
      <div class="lean-graph-views" role="group" aria-label="External bridge view">
        <button type="button" data-graph-view="overview" data-graph-view-source="gap-entropy.json" aria-pressed="true">GapEntropy bridge</button>
      </div>
      <div class="lean-graph-search-shell">
        <label for="gap-entropy-graph-search">Search this bridge</label>
        <input id="gap-entropy-graph-search" type="search" data-graph-search placeholder="gap entropy, benchmark, probability" autocomplete="off" role="combobox" aria-autocomplete="list" aria-controls="gap-entropy-graph-suggestions" aria-expanded="false">
        <ul id="gap-entropy-graph-suggestions" data-graph-suggestions role="listbox" hidden></ul>
      </div>
      <div class="lean-graph-actions">
        <label for="gap-entropy-branch-size">Branch size</label>
        <select id="gap-entropy-branch-size" data-graph-branch-size><option value="12">12</option><option value="24">24</option></select>
        <button type="button" data-graph-fit>Fit</button>
        <button type="button" data-graph-reset>Reset</button>
        <span data-graph-count aria-live="polite">Loading graph…</span>
      </div>
    </header>
    <div class="lean-graph-stage">
      <div class="lean-graph-canvas" data-graph-canvas tabindex="0" aria-label="GapEntropy external bridge graph canvas">
        <svg data-graph-svg role="img" aria-label="GapEntropy external formalization bridge graph"></svg>
        <p class="lean-graph-empty" data-graph-empty hidden>No matching branch is visible.</p>
      </div>
      <aside class="lean-graph-detail" data-graph-detail aria-live="polite"></aside>
    </div>
  </div>
</section>
<section id="semantics">
  <h2>Edge semantics</h2>
  <p>External theorem-internal dependencies are source evidence inside the external slice. Links from BanditRLlib probability/information routes to external nodes are explicitly conceptual-overlap or frontier-closure edges, not imports. A future local port must reclassify each edge as exact reuse, adapter-needed, new local lemma, or conceptual only.</p>
  <p><a href="{href_from(page, 'banditrlwiki/frontier-problems/gap-entropy/index.html')}">Read the problem history and graph-delta interpretation →</a></p>
</section>
"""
    write_page(
        output,
        page,
        layout(
            page,
            "GapEntropy external Lean graph bridge",
            body,
            [("bridge", "Bridge"), ("explorer", "Explorer"), ("semantics", "Edge semantics")],
            "lean-graph",
            verified,
            generated_at,
            extra_scripts=("static/lean-graph.js",),
            wide=True,
        ),
    )


def _build_functor_hypergraph(
    output: Path,
    functor: dict[str, Any],
    techniques: dict[str, Any],
    layout: Callable[..., str],
    write_page: Callable[[Path, str, str], None],
    href_from: Callable[[str, str], str],
    github_repo: str,
    verified: bool,
    generated_at: str,
) -> None:
    page = "functor-hypergraph/index.html"
    mermaid = ["flowchart LR"]
    cards = []
    seen_domains: dict[str, str] = {}
    domain_index = 0
    for index, family in enumerate(functor["families"]):
        fid = f"F{index}"
        mermaid.append(f'{fid}["{_safe_mermaid(family["title"])}"]')
        for domain in family["domains"]:
            if domain not in seen_domains:
                did = f"D{domain_index}"
                domain_index += 1
                seen_domains[domain] = did
                mermaid.append(f'{did}["{_safe_mermaid(domain)}"]')
            mermaid.append(f"{seen_domains[domain]} -. conceptual .-> {fid}")
        hypothesis = "".join(f"<li>{html.escape(item)}</li>" for item in family["hypothesis_map"])
        conclusion = "".join(f"<li>{html.escape(item)}</li>" for item in family["conclusion_map"])
        sources = " · ".join(html.escape(item) for item in family["source_ids"])
        substrates = " · ".join(f"<code>{html.escape(item)}</code>" for item in family["candidate_lean_substrates"])
        technique_ids = family.get("technique_ids", [])
        technique_links = " · ".join(
            f'<a href="{href_from(page, "banditrlwiki/technique-map/index.html")}#technique-{html.escape(tid)}"><code>{html.escape(tid)}</code></a>'
            for tid in technique_ids
        )
        cards.append(
            f"""<article class="info-card" id="{html.escape(family['id'].replace(':','-'))}">
<p class="panel-kicker">{html.escape(family['status'])} · {html.escape(family['id'])}</p>
<h3>{html.escape(family['title'])}</h3>
<p><strong>Mechanism.</strong> {html.escape(family['mechanism'])}</p>
<p><strong>Formula/skeleton.</strong> {html.escape(family['formula'])}</p>
<p><strong>Domains.</strong> {html.escape(' · '.join(family['domains']))}</p>
<details><summary>Hypothesis and conclusion map</summary><h4>Hypotheses</h4><ul>{hypothesis}</ul><h4>Conclusions</h4><ul>{conclusion}</ul></details>
<p><strong>Technique Map.</strong> {technique_links or 'No named technique entry yet.'}</p>
<p><strong>Candidate Lean substrates.</strong> {substrates or 'No local substrate mapped yet.'}</p>
<p><strong>Source/route IDs.</strong> {sources}</p>
<div class="callout warning"><strong>Failure boundary.</strong> {html.escape(family['failure_boundary'])}</div>
</article>"""
        )

    diagram = "\n".join(mermaid)
    body = f"""
<section class="hero" id="hypergraph">
  <p class="eyebrow">Conceptual proof-mechanism memory</p>
  <h1 class="page-title">{html.escape(functor['title'])}</h1>
  <p class="lede">{html.escape(functor['scope'])}</p>
  <div class="hero-actions"><a class="button primary" href="{href_from(page, 'banditrlwiki/setting-atlas/index.html')}">Bandit Taxonomy</a><a class="button" href="{href_from(page, 'banditrlwiki/technique-map/index.html')}">Technique Map</a><a class="button" href="{href_from(page, 'lean-graph/index.html')}">Lean Graph</a><a class="button" href="{href_from(page, 'community/index.html#codex-contract')}">Contribution protocol</a></div>
  <div class="callout warning"><strong>Not a theorem graph.</strong> Hyperedges are dashed conceptual correspondences. A family name does not assert theorem equivalence, a Lean dependency, or a certified categorical functor.</div>
</section>
<section id="incidence">
  <h2>Incidence view</h2>
  <p>Families are rendered as hyperedge hubs connecting domains. The diagram is deliberately dashed because these are candidate recurring mechanisms.</p>
  <figure class="diagram" tabindex="0" role="region" aria-label="Functor Hypergraph conceptual incidence graph">
    <pre class="mermaid">{html.escape(diagram)}</pre>
    <figcaption>Conceptual incidence graph generated from <code>website/content/functor_hypergraph.json</code>.</figcaption>
    <span class="diagram-scroll-hint" data-diagram-scroll-hint hidden>Swipe horizontally or use the left and right arrow keys to read the full diagram <span aria-hidden="true">↔</span></span>
  </figure>
</section>
<section id="families">
  <h2>Candidate mechanism families</h2>
  <div class="card-grid">{''.join(cards)}</div>
</section>
<section id="admission">
  <h2>Admission rule for contributors and Codex</h2>
  <p>Every substantive contribution runs a conceptual-mirror audit. Return <code>none-found-with-reason</code> for a routine local result; otherwise publish a typed candidate with domains, formula, mechanism, hypothesis/conclusion maps, source evidence, candidate Lean substrates and a failure boundary. The proposing actor should not be the only validator.</p>
  <p>Validated conceptual structure is recorded here and in <code>website/content/graph_memory_index.json</code>. Formal proof dependencies remain owned by Lean source and the Lean Graph.</p>
  <p><a href="{github_repo}/blob/main/docs/contributor-codex-contract.md">Read the repository Codex contract ↗</a></p>
</section>
"""
    write_page(
        output,
        page,
        layout(
            page,
            "Functor Hypergraph",
            body,
            [("hypergraph", "Hypergraph"), ("incidence", "Incidence view"), ("families", "Families"), ("admission", "Admission rule")],
            "functor-hypergraph",
            verified,
            generated_at,
            wide=True,
        ),
    )


def _build_technique_map(
    output: Path,
    atlas: dict[str, Any],
    techniques: dict[str, Any],
    layout: Callable[..., str],
    write_page: Callable[[Path, str, str], None],
    href_from: Callable[[str, str], str],
    verified: bool,
    generated_at: str,
) -> None:
    page = "banditrlwiki/technique-map/index.html"
    setting_by_id = {item["id"]: item for item in atlas["entries"]}
    cards = []
    for technique in techniques.get("techniques", []):
        setting_links = []
        for setting_id in technique.get("setting_ids", []):
            setting = setting_by_id.get(setting_id)
            if setting:
                setting_links.append(
                    f'<a href="{href_from(page, "banditrlwiki/setting-atlas/index.html")}#setting-{html.escape(setting_id)}">{html.escape(setting["title"])}</a>'
                )
        routes = " · ".join(f"<code>{html.escape(route)}</code>" for route in technique.get("lean_routes", []))
        source_links = "".join(
            f'<li><a href="{html.escape(src["url"], quote=True)}">{html.escape(src["title"])}</a> — {html.escape(src.get("role", ""))}</li>'
            for src in technique.get("source_refs", [])
        )
        cross = "".join(
            f'<li><a href="{html.escape(item["repo"], quote=True)}">{html.escape(item["project"])}</a> — {html.escape(item["role"])}</li>'
            for item in technique.get("cross_library", [])
        )
        cards.append(
            f"""<article class="info-card" id="technique-{html.escape(technique['id'])}">
<p class="panel-kicker">{html.escape(technique['category'])} · {html.escape(technique['status'])}</p>
<h3>{html.escape(technique['title'])}</h3>
<p>{html.escape(technique['mechanism'])}</p>
<p><strong>Used by settings.</strong> {' · '.join(setting_links) if setting_links else 'No canonical setting mapped yet.'}</p>
<p><strong>Functor family.</strong> <a href="{href_from(page, 'functor-hypergraph/index.html')}#{html.escape(technique['functor_family'].replace(':','-'))}"><code>{html.escape(technique['functor_family'])}</code></a></p>
<p><strong>Current Lean routes.</strong> {routes or 'No compiled route mapped yet.'}</p>
{('<details><summary>Primary/current source anchors</summary><ul>' + source_links + '</ul></details>') if source_links else ''}
{('<details><summary>Cross-library substrates</summary><ul>' + cross + '</ul></details>') if cross else ''}
</article>"""
        )
    body = f"""
<section class="hero" id="techniques">
  <p class="eyebrow">Setting → new technique → proof mechanism</p>
  <h1 class="page-title">{html.escape(techniques['title'])}</h1>
  <p class="lede">{html.escape(techniques['scope'])}</p>
  <div class="hero-actions">
    <a class="button primary" href="{href_from(page, 'banditrlwiki/setting-atlas/index.html')}">Bandit Taxonomy</a>
    <a class="button" href="{href_from(page, 'functor-hypergraph/index.html')}">Functor Hypergraph</a>
    <a class="button" href="{href_from(page, 'lean-graph/index.html')}">Lean Graph</a>
  </div>
  <div class="callout"><strong>How to read this page.</strong> Taxonomy says <em>what changes in the problem</em>. Technique Map says <em>what new mathematical move handles that change</em>. Functor Hypergraph asks whether the move is structurally reusable across domains. Lean Graph records what is actually formalized.</div>
</section>
<section id="map">
  <h2>{len(cards)} technique families</h2>
  <div class="card-grid">{''.join(cards)}</div>
</section>
<section id="boundary">
  <h2>Truth boundary</h2>
  <p>A setting→technique link is a reviewed teaching/research relation. It becomes a formal Lean dependency only after a concrete declaration calls a compiled interface. Cross-library candidates remain dashed until an adapter/import is verified.</p>
</section>
"""
    write_page(
        output,
        page,
        layout(
            page,
            techniques["title"],
            body,
            [("techniques", "Technique Map"), ("map", "Techniques"), ("boundary", "Truth boundary")],
            "banditrlwiki-technique-map",
            verified,
            generated_at,
            wide=True,
        ),
    )


def build_lean_graph_technique_overlay(
    output: Path,
    *,
    content_dir: Path,
    public_repo_dir: Path,
    verified: bool,
    generated_at: str,
) -> None:
    """Add a conceptual Settings→Techniques→Lean/cross-library slice to Lean Graph.

    This overlay is intentionally separate from compiler-backed graph generation.
    All non-formal relations are dashed by relation class in the site stylesheet.
    """
    atlas = _load(public_repo_dir / "data" / "setting-atlas.json")
    techniques = _load(content_dir / "bandit_technique_map.json")

    root = "library:banditrl"
    setting_group = "group:setting-layer"
    technique_group = "group:technique-layer"
    substrate_group = "group:technique-substrates"
    nodes: list[dict[str, Any]] = [
        {"id": root, "label": "BanditRLlib", "kind": "library", "status": "compiled" if verified else "source",
         "subtitle": "formal library root", "parent": "", "order": 0, "url": "../index.html"},
        {"id": setting_group, "label": "Bandit Taxonomy", "kind": "conceptual layer", "status": "source",
         "subtitle": "settings / objectives / methods", "parent": root, "order": 1, "url": "../banditrlwiki/setting-atlas/index.html"},
        {"id": technique_group, "label": "Technique Map", "kind": "conceptual layer", "status": "source",
         "subtitle": "mathematical mechanisms", "parent": setting_group, "order": 2, "url": "../banditrlwiki/technique-map/index.html"},
        {"id": substrate_group, "label": "Formal / cross-library substrates", "kind": "integration layer", "status": "partial",
         "subtitle": "compiled ABRL routes and dashed candidates", "parent": technique_group, "order": 3, "url": "../functor-hypergraph/index.html"},
    ]
    edges: list[dict[str, str]] = [
        {"source": root, "target": setting_group, "relation": "contains"},
        {"source": setting_group, "target": technique_group, "relation": "conceptual layer"},
        {"source": technique_group, "target": substrate_group, "relation": "conceptual layer"},
    ]

    setting_ids = set()
    for order, item in enumerate(atlas.get("entries", []), start=10):
        if item.get("kind") == "ambiguous":
            continue
        node_id = f"setting:{item['id']}"
        setting_ids.add(item["id"])
        nodes.append({
            "id": node_id, "label": item["title"], "kind": item["kind"], "status": "source",
            "subtitle": item.get("summary", ""), "parent": setting_group, "order": order,
            "url": f"../banditrlwiki/setting-atlas/index.html#setting-{item['id']}",
        })
        edges.append({"source": setting_group, "target": node_id, "relation": "contains"})

    route_nodes: dict[str, str] = {}
    def ensure_route(route: str) -> str:
        if route in route_nodes:
            return route_nodes[route]
        if route.startswith("teaching:"):
            slug = route.split(":", 1)[1]
            node_id = f"substrate:teaching:{slug}"
            label = f"Teaching route · {slug}"
            url = f"../chapters/{slug}/index.html"
        elif route.startswith("spine:"):
            slug = route.split(":", 1)[1]
            node_id = f"substrate:spine:{slug}"
            label = f"Source spine · {slug}"
            url = f"../textbook-spine/{slug}/index.html"
        else:
            node_id = f"substrate:{route.replace(':','-')}"
            label = route
            url = "../implementation-map/index.html"
        route_nodes[route] = node_id
        nodes.append({
            "id": node_id, "label": label, "kind": "Lean route candidate",
            "status": "partial", "subtitle": route, "parent": substrate_group,
            "order": 1000 + len(route_nodes), "url": url,
        })
        edges.append({"source": substrate_group, "target": node_id, "relation": "contains"})
        return node_id

    for order, technique in enumerate(techniques.get("techniques", []), start=100):
        node_id = f"technique:{technique['id']}"
        nodes.append({
            "id": node_id, "label": technique["title"], "kind": "technique",
            "status": "source", "subtitle": technique["mechanism"],
            "parent": technique_group, "order": order,
            "url": f"../banditrlwiki/technique-map/index.html#technique-{technique['id']}",
        })
        edges.append({"source": technique_group, "target": node_id, "relation": "contains"})
        for setting_id in technique.get("setting_ids", []):
            if setting_id in setting_ids:
                edges.append({"source": f"setting:{setting_id}", "target": node_id, "relation": "uses technique"})
        for route in technique.get("lean_routes", []):
            edges.append({"source": node_id, "target": ensure_route(route), "relation": "candidate Lean substrate"})

    aspbe = "external:aspbe"
    nodes.append({
        "id": aspbe, "label": "ASPBE / QuantumComputinglib", "kind": "external formal library",
        "status": "source", "subtitle": "quantum state/operator/oracle/circuit substrate",
        "parent": substrate_group, "order": 1999,
        "url": "https://dakebu.github.io/Quantum-Computing-Block-Encoding/",
    })
    edges.append({"source": substrate_group, "target": aspbe, "relation": "contains"})
    if any(t["id"] == "quantum-estimation-testing" for t in techniques.get("techniques", [])):
        edges.append({"source": "technique:quantum-estimation-testing", "target": aspbe, "relation": "cross-library candidate"})

    payload = {
        "schema_version": 1,
        "generated_at": generated_at,
        "edge_direction": "Conceptual setting→technique→substrate relations. Dashed overlays are not formal Lean dependencies.",
        "evidence_boundary": "Only compiled ABRL declarations/routes inherit local proof status. Setting-technique and external-library relations are conceptual/candidate overlays.",
        "root": root,
        "views": {"techniques": [root, setting_group, technique_group, substrate_group]},
        "nodes": nodes,
        "edges": edges,
    }
    target = output / "lean-graph" / "views" / "techniques.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(payload, ensure_ascii=False, separators=(",", ":")) + "\n", encoding="utf-8")
