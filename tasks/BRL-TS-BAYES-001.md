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

## Build Gate

```bash
python3 tools/bandit.py check
```
