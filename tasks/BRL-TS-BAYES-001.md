# Stage Thompson sampling Bayesian regret

Task id: `BRL-TS-BAYES-001`
Kind: `theoremFormalization`
Status: `planned`
Harness: `hierarchical`

## Goal

Maintain a proof-DAG and memory route for Thompson sampling posterior action
identity and Bayesian regret, with LML theorem cards as the first source.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declarations: `Bandits.TS.hasCondDistrib_action`, `Bandits.integral_regret_le`
- Local surface: `BanditRLProof/Algorithms/Thompson.lean`
- Textbook/source cards: `TXT-SLIVKINS-2019-2024`, `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario card: `SCN-STOCHASTIC-FINITE`
- Mathlib cards: `MLIB-PROBABILITY-KERNEL`, `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL`

## Lean Target

```lean
-- staged targets:
-- BanditRLProof.Thompson.obligationNames
-- future posterior action identity
-- future Bayesian regret bound
```

## Proof Obligations

- [ ] Record posterior best-action distribution assumptions.
- [ ] Record conditional-distribution interface.
- [ ] Record clipped-UCB bridge.
- [ ] Record bounded/sub-Gaussian environment assumptions.
- [ ] Decide whether to import LML or keep theorem cards.

## Mathlib-Ready Leaf Contract

Current leaf classes are recorded in
`proof-obligations/BRL-TS-BAYES-001.md`.  Generic integral, measurability,
conditional-distribution, and algebra leaves should be Mathlib candidates when
stated cleanly; Thompson-specific posterior-action wrappers remain
project-local or theorem-card-only until imported.  Persistent failure must
trigger a prior-support, integrability, or conditional-distribution audit.

## Build Gate

```bash
python3 tools/bandit.py check
```
