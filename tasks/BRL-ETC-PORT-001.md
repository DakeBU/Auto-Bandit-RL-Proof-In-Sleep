# Port the Explore-Then-Commit regret proof route

Task id: `BRL-ETC-PORT-001`
Kind: `literaturePort`
Status: `planned`
Harness: `hierarchical`

## Goal

Formalize or stage the Explore-Then-Commit regret proof route using ABRL's
finite-action surfaces and LML theorem cards.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declaration: `Bandits.ETC.regret_le`
- Upstream module: `LeanMachineLearning.Online.Bandit.Algorithms.ETC`
- Local surface: `BanditRLProof/Algorithms/ETC.lean`
- Textbook/source card: `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario card: `SCN-STOCHASTIC-FINITE`
- Mathlib cards: `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS`, `MLIB-PROBABILITY-INDEPENDENCE`

## Lean Target

```lean
-- staged targets:
-- BanditRLProof.ETC.obligationNames
-- future local theorem compatible with Bandits.ETC.regret_le
```

## Proof Obligations

- [ ] Prove or import round-robin exploration counts.
- [ ] Map empirical mean argmax commit.
- [ ] Record wrong-commit probability concentration theorem.
- [ ] Derive pull-count bound after commit.
- [ ] Connect to regret decomposition.

## Mathlib-Ready Leaf Contract

Current leaf classes are recorded in
`proof-obligations/BRL-ETC-PORT-001.md`.  Generic finite-cycle arithmetic and
regularity lemmas should be treated as Mathlib candidates; ETC-specific
algorithm wrappers stay project-local.  Do not change the proof route without
recording the missing assumption, counterexample, or source mismatch.

## Build Gate

```bash
python3 tools/bandit.py check
```
