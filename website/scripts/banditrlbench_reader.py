"""Readable QA, operational entry points and exact graph-location overlays."""
from __future__ import annotations

import hashlib
import html
import json
import subprocess
from pathlib import Path
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[2]
BENCH = ROOT / 'benchmarks/banditrlbench'
REPO = 'https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep'


def prose(text, notation):
    """Literal presentation substitutions; never rewrite the sealed question."""
    pieces = [text]
    # Long expressions must be captured before their constituent symbols.
    for entry in sorted(notation, key=lambda e: -len(e[0])):
        literal, tex, *kind = entry
        replaced = []
        for piece in pieces:
            if not isinstance(piece, str):
                replaced.append(piece)
                continue
            parts = piece.split(literal)
            for i, part in enumerate(parts):
                if i:
                    replaced.append((tex, bool(kind), literal))
                replaced.append(part)
        pieces = replaced
    rendered = ''
    for piece in pieces:
        if isinstance(piece, str):
            rendered += html.escape(piece)
        else:
            tex, display, fallback = piece
            if display:
                rendered += ('<span class="math-statement bench-equation" data-math-statement '
                             'data-scroll-label="Benchmark proof formula">'
                             '<span class="math-fallback-note" aria-hidden="true">Formula renderer unavailable; readable fallback: </span>'
                             '<span class="math-fallback">' + html.escape(fallback) + '</span>'
                             '<span class="math-tex" aria-hidden="true">\\[' + html.escape(tex) + '\\]</span>'
                             '<span class="overflow-hint" aria-hidden="true">Swipe to read the full formula <span>→</span></span></span>')
            else:
                rendered += '<span class="math-inline">\\(' + html.escape(tex) + '\\)</span>'
    return rendered


def graph_locations(data, output):
    graph = json.loads((output / 'lean-graph/graph.json').read_text(encoding='utf-8'))
    nodes = {n['id']: n for n in graph['nodes']}
    source_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    locations = []
    for core in data['cores']:
        nid = 'declaration:' + core['source_declaration']
        if nid not in nodes:
            raise ValueError('Benchmark anchor absent from generated Lean Graph: ' + nid)
        node = nodes[nid]
        locations.append(dict(core_id=core['core_id'], node_id=nid, module_id=node['parent'],
                              reader_url=node['url'], status=node['status'],
                              graph_source_commit=source_commit,
                              source_relation='context-only' if core['core_id'] == 'BRB-004' else 'source-correspondence',
                              frozen_source_commit=core['source_commit'],
                              current_source_matches_frozen=hashlib.sha256((ROOT / core['source_file']).read_bytes()).hexdigest() == core['source_sha256'],
                              relations=[e for e in graph['edges'] if nid in (e['source'], e['target'])],
                              boundary='Current structural/navigation graph; source correspondence is not a proof dependency.'))
    return locations


def build_pages(data, output, verified, generated_at, layout, write_page):
    esc = html.escape
    notation = json.loads((BENCH / 'notation.json').read_text(encoding='utf-8'))
    targets = json.loads((BENCH / 'targets.json').read_text(encoding='utf-8'))
    replay = json.loads((BENCH / 'reference-replay.json').read_text(encoding='utf-8'))
    replay_results = {r['core_id']: r for r in replay['results']}
    locations = {r['core_id']: r for r in graph_locations(data, output)}
    try:
        from .bench_visuals import landing, fold_sections, protocol_page
    except ImportError:
        from bench_visuals import landing, fold_sections, protocol_page
    def emit(path, title, body):
        if path.endswith('/run/index.html') or path.endswith('/review/index.html'):
            body = fold_sections(body)
        write_page(output, path, layout(path, title, '<div class="bench-reader">' + body + '</div>', [], 'banditrlbench', verified, generated_at, extra_scripts=('static/bench-reader.js',)))
    def hero(title, lede):
        return f'<section class="hero"><p class="eyebrow">BanditRLBench · public development edition</p><h1 class="page-title">{title}</h1><p class="lede">{lede}</p></section>'
    warning = '<p class="bench-edition">Public dev · 4 cores · 2 Lean warmups · Gold admission and held-out tests pending</p>'
    nav = '<nav aria-label="Benchmark"><a href="../index.html">Overview</a> · <a href="../non-lean/index.html">Natural-language QA</a> · <a href="../lean/index.html">Lean QA</a> · <a href="../run/index.html">Run and train</a> · <a href="../review/index.html">Expert review</a> · <a href="../protocol/index.html">Task protocol</a></nav>'
    emit('banditrlbench/index.html', 'BanditRLBench', landing())
    emit('banditrlbench/protocol/index.html', 'BanditRLBench · Task protocol', protocol_page())
    for track, title in [('non-lean', 'Natural-language QA'), ('lean', 'Lean QA')]:
        listing = '<p class="bench-toc">Jump to: ' + ' · '.join(f'<a href="#{c["core_id"]}">{c["core_id"]}</a>' for c in data['cores'] if track == 'non-lean' or c['core_id'] in targets) + '</p>'
        for core in data['cores']:
            cid = core['core_id']
            if track == 'lean' and cid not in targets:
                continue
            loc = locations[cid]
            p = lambda text: prose(text, notation[cid])
            question = core['question'] if track == 'non-lean' else core['lean']['question']
            listing += f'<details class="task-browser"'+(' open' if cid == 'BRB-001' else '')+f'><summary>{cid} · {esc(core["title"])}</summary><article class="bench-task" id="{cid}"><p class="eyebrow">{cid} · {esc(core["family_id"])} · dev</p><h2>{esc(core["title"])}</h2><h3>Assumptions</h3><ul>' + ''.join('<li>' + p(a) + '</li>' for a in core['assumptions']) + '</ul><h3>Your task</h3><p>' + p(question) + '</p>'
            if track == 'lean':
                listing += '<p class="callout">Only the fixed signature below is graded. The NL assumptions describe the parent problem; the signature is the exact formal contract.</p><pre class="lean-code"><code>' + esc('theorem Submission ' + targets[cid]['signature'] + ' := by\n  -- your proof') + '</code></pre>'
            listing += '<details><summary>Solution and assessment rubric</summary><div class="bench-proof">' + p(core['answer']) + '</div><ol>' + ''.join('<li>' + p(r) + '</li>' for r in core['rubric']) + '</ol>'
            if track == 'lean':
                listing += '<h3>Reference for this subtarget</h3><pre class="lean-code"><code>' + esc(targets[cid]['reference_proof']) + '</code></pre><p>This library-application proof does not certify the complete NL answer or demonstrate novel proof synthesis.</p>'
            listing += '</details><section class="bench-location"><h3>Locate this mathematics</h3><p><a href="../../lean-graph/index.html?node=' + quote(loc['node_id'], safe='') + '">Open exact Lean Graph node →</a> · <a href="../../lean-graph/' + esc(loc['reader_url']) + '">Read the declaration →</a></p><p><code>' + esc(core['source_declaration']) + '</code></p><p>Relation: <strong>' + loc['source_relation'] + '</strong>. ' + ('This is context for an original counterexample, not a proof of its answer.' if cid == 'BRB-004' else 'The declaration anchors this core; formal companion scope is stated separately.') + '</p></section>'
            if cid in replay_results:
                measured = replay_results[cid]
                actual = [name for name in measured['dependencies']['value_constants'] if name.startswith('BanditRLProof.')]
                listing += '<details><summary>Actual constants in the checked reference proof</summary><p>Project constants read from the compiled proof value: ' + ', '.join('<code>' + esc(name) + '</code>' for name in actual) + '.</p><p>Axioms: ' + ', '.join(esc(name) for name in measured['axioms']) + '.</p><p>Recorded library environment: <code>' + replay['environment']['library_commit'] + '</code>. This is direct fixed-target proof evidence, not the transitive dependency closure of the library theorem. <a href="../reference-replay.json">Full type/proof constants and environment receipt</a>.</p></details>'
            source = f'{REPO}/blob/{core["source_commit"]}/{core["source_file"]}'
            listing += f'<details><summary>Frozen source and verification boundary</summary><p><a href="{source}" data-benchmark-core="{cid}" data-benchmark-contract="{core["contract_hash"]}" data-benchmark-snapshot="{core["source_commit"]}">Frozen benchmark source ({core["source_commit"][:7]})</a></p><p>Source SHA-256: <code>{core["source_sha256"]}</code><br>Question contract: <code>{core["contract_hash"]}</code></p><p>Current graph source matches frozen bytes: {str(loc["current_source_matches_frozen"]).lower()}. Current graph location is navigation, not evidence of a new compiled dependency edge.</p><p>NL gold admission: pending. <a href="../reference-check.json">Reference compilation receipt</a>. <a href="../run/index.html">Replay formal submissions</a>.</p></details></article></details>'
        emit(f'banditrlbench/{track}/index.html', 'BanditRLBench · ' + title, hero(title, 'Read the assumptions, attempt the task, then unfold the solution. Exact graph locations stay visible.') + nav + warning + listing)

    run = hero('Run, evaluate and train', 'Start with prompt-only data. Keep the access condition, model identity and evidence attached to each result.') + nav + warning
    run += '''<section><h2>1. Prepare a run</h2><p>Python 3.11+ and Git are enough for NL tasks. Work from this repository root. The command creates a new directory and never overwrites a previous run.</p><pre><code>python tools/banditrlbench.py prepare --track non-lean --mode closed-book --model YOUR_MODEL --agent YOUR_AGENT --output _out/nl-run
# Lean track: replace non-lean with lean and choose lean-assisted.</code></pre><p>Give the agent <code>prompts.jsonl</code>, then fill <code>predictions.jsonl</code>. Lean rows contain exact imports and target signatures; submit only the proof expression. The runner makes no API calls. Record generation settings, token/cost budgets and transcripts alongside <code>run.json</code>.</p><p><a href="../non-lean-prompts.jsonl">Download NL prompts</a> · <a href="../lean-prompts.jsonl">Download Lean prompts</a></p></section>
<section><h2>2. Assess natural-language answers</h2><pre><code>python tools/banditrlbench.py review-pack --predictions _out/nl-run/predictions.jsonl --output _out/review
# A domain expert fills review.jsonl, with identity, criterion scores and reasons.
python tools/banditrlbench.py assess --predictions _out/nl-run/predictions.jsonl --review _out/review/review.jsonl --output _out/nl-results</code></pre><p>The reviewer packet contains candidate gold and must stay outside the agent input. Scores are explicit expert rubric judgments, not an automatic mathematical verifier. Contracts and response hashes must match; incomplete or stale reviews are rejected.</p></section>
<section><h2>3. Replay trusted Lean proofs</h2><p>Use the committed <code>lean-toolchain</code> and <code>lake-manifest.json</code>. Build and check the library first, then run:</p><pre><code>python tools/bandit.py check
python tools/banditrlbench.py replay --trusted-local --library . --mode lean-assisted --model YOUR_MODEL --agent YOUR_AGENT --predictions _out/lean-run/predictions.jsonl --output _out/lean-results
python tools/banditrlbench.py canary --trusted-local --library . --output _out/canary</code></pre><p>Each fixed-target replay records compiler logs, axiom closure and direct constants in the checked type and proof. Canary tests require reference success and empty, incorrect and placeholder rejection. These are harness checks, not model scores.</p><p class="callout warning">Trusted local execution only: Lean elaboration can execute code. This runner is not a security sandbox. Do not submit untrusted model code on a workstation with credentials. Container isolation and a Harbor adapter have not been validated or released.</p></section>
<section><h2>4. Train and report honestly</h2><pre><code>python website/scripts/banditrlbench.py export --track non-lean --include-solutions --output _out/dev-training.jsonl</code></pre><p>This opt-in exports public development answers for practice or supervised training. The Lean export includes the exact formal target and its reference proof. There is no train/test split yet; every solution alias stays in its family. Report closed-book, text-retrieval, graph-retrieval and Lean-assisted runs separately. Local access modes are operator declarations, not enforced isolation.</p><p>No leaderboard, held-out score, automated NL correctness or RL-training environment is claimed. <a href="../review/index.html">See admission and contribution requirements</a>.</p></section>'''
    emit('banditrlbench/run/index.html', 'BanditRLBench · Run and train', run)
    review = hero('Expert review and contribution', 'Inspect the question, source, formal scope and graph location before admitting an answer or interpreting a score.') + nav
    review += '<section><h2>Inspect a core</h2><ol><li>Check the ordered assumptions and question contract; keep source corrections separate from the frozen task.</li><li>Open its exact graph node and declaration page. Containment, imports and reviewed teaching links retain their existing meanings.</li><li>Compare the NL answer with the exact formal signature. BRB-003 checks the schedule sum only; BRB-004 has a context-only anchor.</li><li>Review criterion-by-criterion with a reason. Compiler acceptance and source fidelity are separate verdicts.</li></ol><p><a href="../graph-locations.json">Download the machine-readable graph-location map</a>. This is a QA overlay; it does not create theorem-dependency edges or certify graph coverage.</p></section>'
    review += '<section><h2>Contribute a task family</h2><p>Open a proposal with a precise task, interest and difficulty explanation, immutable source identity, correct solution, assessment method, environment, exact graph placement and explicit failure boundary. A formal companion also needs a frozen signature, reference replay and negative controls. Use a personal branch and the repository contribution manifest. Review the proposed gold independently before admission.</p><p><a href="' + REPO + '/blob/main/benchmarks/banditrlbench/CONTRIBUTING.md">Task contribution guide</a> · <a href="' + REPO + '/blob/main/benchmarks/banditrlbench/ENVIRONMENT.md">Environment and isolation boundary</a></p></section>'
    review += '<section><h2>Release gates still open</h2><ul><li>Independent expert gold admission and harder topic coverage.</li><li>Family/solution leakage audit before a train/test release.</li><li>Untrusted-code container verifier and tested Harbor integration.</li><li>Reference and no-op controls across replicated environments; transparent model trials and error analysis before any leaderboard.</li></ul><p>Workflow design draws on <a href="https://docs.harborframework.com/tasks/overview">Harbor task anatomy</a> and <a href="https://github.com/harbor-framework/terminal-bench/blob/main/CONTRIBUTING.md">Terminal-Bench contribution practices</a>. No compatibility or affiliation is implied; no external task content is copied.</p></section>'
    emit('banditrlbench/review/index.html', 'BanditRLBench · Expert review', review)
    dest = output / 'banditrlbench'
    for source, name in [('cores.json', 'cores.json'), ('lean/Reference.lean', 'Reference.lean'), ('reference-check.json', 'reference-check.json'), ('reference-replay.json', 'reference-replay.json')]:
        (dest / name).write_bytes((BENCH / source).read_bytes())
    (dest / 'graph-locations.json').write_text(json.dumps(list(locations.values()), indent=2) + '\n', encoding='utf-8')
