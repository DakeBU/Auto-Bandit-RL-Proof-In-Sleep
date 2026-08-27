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
- keeps compiled, partial, stated, planned, and blocked routes distinct through
  `content/results.json`;
- renders maintainable Mermaid architecture, dependency, progress, learning,
  installation, formalization, and contribution diagrams;
- generates an interactive Lean Graph over all current modules and declarations,
  with progressive chapter/module/declaration expansion, search, status-aware
  branch inspection, and reviewed prerequisite/consumer edges;
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
295-declaration stochastic-gradient-bandit audit—are displayed outside that
comparison ledger.  The latter contains a historical 223-declaration
Theorem-1/Appendix-E stack, a 23-declaration bounded Corollary-1 companion, an
18-declaration fixed-cutoff starvation consumer, a 24-declaration chronological
nth-pull bridge, and a 7-declaration latent fixed-arm product/readout layer.  The
new layer proves an unconditional finite product law for fixed-arm latent
coordinates and almost-sure readout at every finite nth pull.  It does not prove
the native trajectory adapter and does not make totalized or
occurrence-conditioned stopped rewards IID.  The stopped-prefix future-cylinder,
conditional no-return producer, ballot phase, and terminal remain blocked.  The
SGB audit therefore remains partial, with Theorems 2–4 open;
the succinct-lower-bound port also has no compiled paper-level terminal.

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
