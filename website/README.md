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
- exposes installation, contributors, contribution, governance, attribution,
  roadmap, source-access, declaration, implementation-map, and textbook-spine
  pages;
- supplies a provider-independent local formalization adapter and a versioned
  lemma-packet handoff contract.

Within the separate Part IV spine, Chapter 13 is partial with compiled
semantic/deterministic leaves, Chapter 14 is partial with a compiled §14.2
relative-entropy, event-data-processing, and Bretagnolle--Huber slice, and
Chapter 15 is partial with compiled unit-Gaussian likelihood-ratio and arm-KL
leaves. Lemma 15.1 and the Gaussian `1/27` minimax terminal remain blocked on
the conditional-kernel KL integral and stochastic-policy history-law bridge;
§14.1 coding and full Exercise 14.10 are not promoted.

The generator and checks use the Python standard library. The published static
site loads MathJax and Mermaid from jsDelivr.

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
