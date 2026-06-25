# Proof Blueprint: BRL-UCB-PORT-001

Generated: `2026-06-25T01:31:20+00:00`

## Source Task

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


## Conversion Window Snapshot

# Conversion Window: UCB regret theorem-card route

Task id: `BRL-UCB-PORT-001`

## Natural-Language Statement

For a finite stochastic bandit with sub-Gaussian rewards, UCB chooses the arm
with maximal empirical mean plus a confidence width.  The expected regret is
bounded by a logarithmic pull-count term for suboptimal arms plus summable bad
event terms.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `K` | number of arms | `K : Nat` | finite action count | typed |
| `A_t` | action at time `t` | `action : Nat -> Fin K` | action trace | local surface |
| `N_{t,a}` | pull count | `pullCount action a t` | count | compiled |
| `Delta_a` | arm gap | `FiniteBanditModel.gap` | rational gap surface | compiled |
| UCB width | confidence radius | `BanditRLProof.UCB.score` placeholder | index surface | typed contract |
| `Bandits.UCB.regret_le` | upstream theorem | LML theorem card | regret bound | theorem-card |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite arms | compiled surface | ABRL core | no |
| reward means | compiled rational surface | ABRL core | no |
| sub-Gaussian rewards | theorem-card/obligation | LML/Mathlib route | yes |
| measurable action process | theorem-card/obligation | LML route | yes |
| expected pull-count bound | theorem-card/obligation | LML route | yes |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `UCB-INIT` | initial exploration gives positive counts | finite arms | lower Lean | TBD | build | planned |
| `UCB-INDEX` | selected arm maximizes UCB index | UCB definition | lower architect | TBD | build | planned |
| `UCB-GOOD` | good event implies pull count bound | index algebra | lower Lean | TBD | build | planned |
| `UCB-TAILS` | upper/lower tail bounds | concentration cards | lower retrieval | cited result | memory | obligation |
| `UCB-REGRET` | regret bound from pull counts | regret decomposition | lower Lean | future theorem | build | blocked |

## Route Decision

Current route: `card-only` until a task explicitly aligns Mathlib/LML
dependencies or ports the needed concentration and probability lemmas.


## Obligation Snapshot

# Proof Obligations: BRL-UCB-PORT-001

| Node | Target | Dependencies | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `UCB-ROUTE` | choose card-only, port, or dependency route | task packet | upper | no Lean declaration | memory | planned |
| `UCB-CORE` | verify ABRL finite trace and pseudo-regret surfaces | `BanditRLProof.Core`, `Regret` | reviewer | `pseudoRegret_succ` | `python3 tools/bandit.py check` | compiled |
| `UCB-INDEX` | replace placeholder score with UCB width when dependency layer is selected | route decision | lower Lean | TBD | build | blocked |
| `UCB-CONC` | record or prove sub-Gaussian tail lemmas | concentration cards | lower retrieval | TBD | memory/build | obligation |
| `UCB-FINAL` | local theorem compatible with `Bandits.UCB.regret_le` | all above | lower Lean | TBD | build | blocked |

## Current Reviewer Note

The upstream LML theorem is a theorem card only.  Do not export it as an ABRL
local proof until the route is imported or ported.


## Relevant LML Theorem Cards

```json
[
  {
    "id": "LML-BANDIT-REGRET-GAP",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.regret_eq_sum_gap",
    "module": "LeanMachineLearning.Online.Bandit.Regret",
    "role": "Regret decomposition into a sum of action gaps.",
    "status": "theorem-card"
  },
  {
    "id": "LML-BANDIT-REGRET-PULLCOUNT",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.regret_eq_sum_pullCount_mul_gap",
    "module": "LeanMachineLearning.Online.Bandit.Regret",
    "role": "Regret decomposition through arm pull counts.",
    "status": "theorem-card"
  },
  {
    "id": "LML-ETC-REGRET",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.ETC.regret_le",
    "module": "LeanMachineLearning.Online.Bandit.Algorithms.ETC",
    "role": "Explore-Then-Commit expected regret bound.",
    "status": "theorem-card"
  },
  {
    "id": "LML-UCB-REGRET",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.UCB.regret_le",
    "module": "LeanMachineLearning.Online.Bandit.Algorithms.UCB",
    "role": "UCB logarithmic pull-count regret route.",
    "status": "theorem-card"
  },
  {
    "id": "LML-TS-POSTERIOR-ACTION",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.TS.hasCondDistrib_action",
    "module": "LeanMachineLearning.Online.Bandit.Algorithms.TS",
    "role": "Thompson sampling action distribution equals posterior best-action distribution.",
    "status": "theorem-card"
  },
  {
    "id": "LML-TS-BAYES-REGRET",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.integral_regret_le",
    "module": "LeanMachineLearning.Online.Bandit.Algorithms.Regret.BayesRegretTS",
    "role": "Bayesian regret upper bound for Thompson sampling.",
    "status": "theorem-card"
  }
]
```

## Recent Trials

```json
[]
```

## Reviewer Gate

```bash
python3 tools/bandit.py check
```
