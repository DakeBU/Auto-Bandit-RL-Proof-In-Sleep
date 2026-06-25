# Port the UCB regret proof route

Task id: `BRL-UCB-PORT-001`
Kind: `literaturePort`
Status: `planned`
Harness: `hierarchical`

## Goal

Build a local ABRL route for the finite stochastic UCB regret theorem, starting
from theorem cards and ending in either a compiled local theorem, a documented
import route, or a precise blocked ledger.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declaration: `Bandits.UCB.regret_le`
- Upstream module: `LeanMachineLearning.Online.Bandit.Algorithms.UCB`
- Local surface: `BanditRLProof/Algorithms/UCB.lean`

## Lean Target

```lean
-- staged targets:
-- BanditRLProof.UCB.obligationNames
-- future local theorem compatible with Bandits.UCB.regret_le
```

## Proof Obligations

- [ ] Decide `card-only`, `port`, or `dependency` route.
- [ ] Map UCB index, width, empirical mean, and pull-count definitions.
- [ ] Record sub-Gaussian tail dependencies.
- [ ] Record expected pull-count bound dependencies.
- [ ] Keep proof export clear that LML is theorem-card status until local closure.

## Build Gate

```bash
python3 tools/bandit.py check
```
