# ABRL and BanditRLlib

> **Anonymous frozen review snapshot.** This branch contains the full project state used for double-blind review. It preserves the Lean library, source audits, BanditRLwiki, textbook material, proof graph, harness, evaluation protocols, website generators, and tests, while withholding project authorship from reviewer-facing entry points.

## What this repository contains

This repository has two connected parts.

1. **ABRL** is a target-faithful theorem-proving and autoformalization harness for bandit and reinforcement-learning theory. It keeps the mathematical target fixed, records source evidence and proof obligations, uses Lean compiler feedback during construction, separates source review from formal checking, and admits results only after deterministic gates.
2. **BanditRLlib** is the reusable Lean 4 library and literate website produced by accepted work. It organizes textbook material, formal declarations, source-frozen paper audits, upper/lower-bound comparisons, frontier leaves, and proof dependencies in one inspectable system.

`BanditRLProof` is the Lean namespace used by the library; **BanditRLlib** is the public-facing name of the library and reader.

## Main mathematical surfaces

The frozen snapshot includes:

- a textbook spine for stochastic bandits and reinforcement learning, including the Part-IV lower-bound chapters;
- BanditRLwiki, which compares assumption-indexed upper and lower bounds while keeping literature optimality, source fidelity, and local Lean evidence separate;
- source-frozen paper audits for stochastic-gradient bandits, succinct lower bounds, delayed/nonstationary bandits, and related frontier material;
- compiler-backed algorithmic and probabilistic infrastructure for finite bandits, adversarial bandits, linear/contextual bandits, Thompson sampling, finite-horizon RL, information-theoretic lower bounds, stopping-time arguments, kernels, and measure-theoretic probability;
- an exported proof graph connecting settings, declarations, dependencies, reusable routes, and open leaves;
- a target-drift evaluation protocol that compares formalization workflows without treating an unrun or unmatched comparison as evidence of superiority.

The website distinguishes several kinds of status. A source theorem can be faithfully audited without being fully formalized; a Lean declaration can compile without closing an entire paper theorem; a literature bound can be optimal under its stated assumptions without having a local Lean certificate. These statuses are intentionally not collapsed.

## Harness

ABRL treats a formalization target as a fixed mathematical contract. Work may move through retrieval, proof design, Lean implementation, compiler diagnosis, counterexample search, and source review, but the target itself does not silently drift in order to make a proof easier.

A candidate is accepted only when the relevant source, Lean, dependency, and regression checks pass. The repository also contains a bounded master--worker comparison protocol; its purpose is to study organization, not to assume that one agent architecture is better in advance.

The main repository gate is:

```bash
python3 tools/bandit.py check
```

The website can be built locally with:

```bash
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
python3 -m http.server 8000 --directory website/_site
```

## Repository map

```text
BanditRLProof/               Lean production library
BanditRLProof.lean           root Lean import surface
tests/ and Tests/            focused and integration checks
research-wiki/               proof memory, paper audits, proof-graph data
website/                     BanditRLlib and BanditRLwiki reader
artifacts/                   accepted evidence and generated records
evaluation/                  target-drift and workflow-evaluation protocols
tools/                       build, verification, graph, and audit tooling
reviews/                     source and acceptance review records
.agents/                     agent and harness instructions
```

## Anonymous review boundary

Project authorship and author-controlled development URLs are withheld in reviewer-facing entry points. Mathematical source authors remain named where they are cited as sources. The review branch is frozen: later development does not enter it unless the snapshot is deliberately refreshed and re-verified.
