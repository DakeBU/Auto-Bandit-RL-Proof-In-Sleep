# 🌐 BanditRLlib literate formalization website

This directory contains the original static generator for BanditRLlib, the
public Lean library produced by the ABRL research harness. It is generated from
the current Lean tree instead of a hand-maintained declaration list.

The build:

- indexes every supported declaration under `BanditRLProof/`;
- preserves exact namespace, statement, module, imports, and source location;
- maps every declaration into a ten-chapter Book Map;
- preserves that Book Map while adding a separate, ordered Part IV lower-bound
  Textbook Spine from `content/textbook_spine.json`;
- adds reviewed teaching notes from `content/highlights.json`;
- gives every Book Map source theorem a five-field model/assumption/parameter/
  regret/guarantee contract and links directly to the cited PDF page;
- gives UCB readers a source-to-Lean proof bridge from confidence validity to
  suboptimal selection, pull-count control, and the final gap-sum bound;
- keeps a prominent textbook-coverage ledger: ten source-mapped teaching routes,
  nine compiled canonical cores, three compiled Part-IV source terminals, and no
  claim that the whole textbook is complete;
- keeps each chapter's default teaching route to two to four named declarations
  with human-readable mathematical headings while retaining exact searchable
  Lean names and the full compiled inventory in a collapsed extension section;
- provides native wrap/scroll and copy controls for exact Lean statements, with
  a readable no-JavaScript fallback;
- loads the exhaustive declaration catalogue through a compact versioned data
  schema instead of repeating full source and module URLs per declaration;
- progressively loads the complete Implementation Map module inventory from a
  generated JSON ledger while preserving an initial no-JavaScript table;
- keeps compiled, partial, stated, planned, and blocked routes distinct through
  `content/results.json`;
- renders maintainable Mermaid architecture, dependency, progress, learning,
  installation, formalization, and contribution diagrams;
- generates an interactive Lean Graph over all current modules and declarations,
  with progressive chapter/module/declaration expansion, search, status-aware
  branch inspection, and reviewed prerequisite/consumer edges; its lightweight
  overview loads first, while the full searchable graph is deferred until the
  reader searches, changes view, or opens a branch;
- generates a landing-page evidence snapshot from the Lean index, teaching
  crosswalks, implementation ledger, and harness-comparison log instead of
  hand-entered completion percentages;
- renders the latest deterministic hierarchical-versus-master-worker comparison
  as an evidence pipeline, candidate hybrid operating pattern, and next matched
  experiment on the Workflow page while refusing to display a winner before the
  matched evidence threshold is met;
- generates BanditRLwiki from `content/banditrlwiki.json`: an
  assumption-indexed upper/lower-bound atlas with primary-paper theorem links,
  independent literature/source-audit/Lean status, stable case pages, a paper
  index, audit progress, and explicit frontier leaves;
- exposes installation, contributors, contribution, governance, attribution,
  roadmap, source-access, declaration, implementation-map, and textbook-spine
  pages;
- supplies a provider-independent local formalization adapter and a versioned
  lemma-packet handoff contract.

Within the separate Part IV spine, Chapters 13--17 expose compiled semantic,
information-theoretic, Gaussian-KL, consistency, and tail-event dependency
slices while keeping their source terminal theorems blocked where the adaptive
history-law or construction bridge is absent. The website also exposes a
source-frozen NeurIPS 2025 delayed best-of-both-worlds audit: 197 named
source-audit declarations compile across accounting, causal processing,
allocation, elimination, event assembly, one-round action-law, trace, D.11,
and line-10 initialization layers, but the Delayed SAPO state machine,
generated sampling trajectory, D.4 probability producer, switching path, and
stochastic/adversarial regret endpoints do not. A compiled dependency slice is
never presented as a completed source theorem.

The generator and checks use the Python standard library. The published static
site loads MathJax and Mermaid from jsDelivr.

BanditRLwiki currently covers 13 comparison cases in seven assumption families,
19 primary papers, and 27 separately indexed theorem surfaces. It deliberately
reports zero `literature-open` cases until a scoped primary-source audit supports
such a claim; one case remains in the source-audit queue, while the 13
formalization-open cases expose 39 stable named leaves. Two additional
source-frozen ports—the 54-declaration succinct-lower-bound audit and the
stochastic-gradient-bandit audit—are displayed outside that comparison ledger.
The latter retains the exact counted 352-declaration audit-slice inventory
`352 = 223 + 23 + 18 + 24 + 7 + 8 + 13 + 28 + 8` through deterministic-time
selected-reward freshness.  A separate ten-declaration module now proves
equality of the complete visible/native trajectory measures.  The selected-
block module adds 32 declarations: eight for missing-pull-aware block transport,
fourteen for the exact finite Appendix-C `S0/S1` event, and ten for the disjoint
all-present/missing-pull probability split.  These compiled layers are not a
selected-IID theorem.  The missing branch still needs a bridge to the
fixed-cutoff starvation consumer; the stopped-prefix future-cylinder law,
conditional no-return probability, Rademacher/ballot phase, asymptotic assembly,
and frozen Theorem-2 terminal remain open.  The SGB audit therefore remains
partial, with Theorems 2–4 open; the succinct-lower-bound port also has no
compiled paper-level terminal.

## 🛠️ Build locally

```text
python tools/bandit.py check
python website/scripts/build_site.py --lean-verified
python website/scripts/check_site.py
python website/scripts/ide_server.py
```

Open `http://127.0.0.1:8000/`; Live Formalization is at `/ide/`. Omitting
`--lean-verified` creates an explicitly unverified preview.

## 🧪 Live Formalization boundary

The browser always provides formula rendering, reviewed mapping navigation,
dependency visualization, editing, and packet export. The loopback service adds
temporary Lean compilation and optional retrieval-grounded candidate generation.
It never writes repository source and must never be placed behind a public
tunnel.

Configure a provider only through the server environment:

```text
ABRL_FORMALIZER_PROVIDER=json-http
ABRL_FORMALIZER_ENDPOINT=https://your-provider.example/v1/formalize
ABRL_FORMALIZER_API_KEY=server-side-secret
```

Without a provider, the service reports candidate generation as unavailable.
With one, it still labels output as a candidate. Semantic review, Lean
compilation, proof completion, and BanditRLlib integration are separate states.

## 🤝 Contribution contract

`community/contribution.schema.json` is schema version 1.1. It records source,
plain-English and LaTeX statements, Lean code, BanditRLlib/Mathlib/LML retrieval
candidates, assumptions, unresolved obligations, independent status fields,
compiler evidence, and contributor credit. Maintainers assign `integrated` only
after the full ABRL gate passes and the change is merged to `main`.

## 🔒 Private static review

`scripts/serve_private.py` serves only generated static files over loopback with
HTTP Basic Authentication. A temporary tunnel may point to that static server,
but never to `ide_server.py`.

## 🚀 Deployment

`.github/workflows/documentation.yml` builds Lean and tests, builds the site,
checks links and mapping integrity, and deploys `website/_site/` to GitHub Pages:

<https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/>

The canonical source is:

<https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep>

## 🧬 Attribution

The implementation-map organization is inspired by **Sho Sonoda's**
[Lean-Ridgelet](https://github.com/shosonoda/lean-ridgelet) and its
[Blueprint](https://shosonoda.github.io/lean-ridgelet/). The community-facing
sidebar and book-to-library organization are inspired by
[StatsMLlib](https://statsmllib.github.io/). The generator, HTML, CSS,
JavaScript, diagrams, and prose here are original; no source file or template
was copied from either project. Attribution does not imply participation,
endorsement, review, or maintenance by those projects or authors.

The progressive graph interaction is also informed by Samplinglib's public
[Underlying Lean Graph of Libraries](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/lean-foundations.html).
BanditRLwiki's setting-to-case-to-frontier organization is informed by its
[SampleWiki](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki.html)
and [Frontier](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki/frontier.html).
BanditRLlib's graph model, theorem data, generated HTML, CSS, and JavaScript are
independently implemented; no Samplinglib source, graph or theorem data,
template, stylesheet, or prose is copied.
