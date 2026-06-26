# Conversion Window: Thompson sampling Bayesian regret

Task id: `BRL-TS-BAYES-001`

Source card: `TXT-SLIVKINS-2019-2024`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-Language Statement

Thompson sampling samples an action according to the posterior probability that
the action is optimal.  Bayesian regret is bounded by decomposing regret through
posterior confidence terms and controlling clipped-UCB deviations.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| prior `Q` | parameter prior | `Thompson.PriorSketch.priorName` | descriptor | typed |
| kernel `kappa` | environment reward kernel | `Thompson.PriorSketch.rewardKernelName` | descriptor | typed |
| posterior best action | action distribution | `Bandits.TS.hasCondDistrib_action` | LML theorem card | theorem-card |
| Bayesian regret | expected regret over prior | `Bandits.integral_regret_le` | LML theorem card | theorem-card |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| `TS-POSTERIOR` | LML theorem cards, future probability imports | `LML-TS-POSTERIOR-ACTION`, `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-KERNEL` | theorem-card route through posterior best-action distribution | pivot only after conditional-distribution statement audit |
| `TS-DECOMP` | regret decomposition cards, integral notation | `LML-TS-BAYES-REGRET`, `MLIB-MEASURE-INTEGRAL` | decompose Bayesian regret under posterior action identity | pivot only after integrability/prior-support audit |
| `TS-BOUND` | clipped-UCB and concentration cards | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-REAL-LOG-SQRT` | combine posterior identity, decomposition, and clipped confidence | pivot only after concentration contract audit |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `TS-POSTERIOR` | posterior action identity | conditional distribution | retrieval | LML card | measurability, conditional distribution, posterior regularity | theorem-card-only | memory | theorem-card |
| `TS-DECOMP` | Bayesian regret decomposition | posterior identity | lower architect | TBD | integrability, finite expected regret, prior support | mathlib-candidate for generic integral/algebra leaves | build | planned |
| `TS-CLIPPED-UCB` | clipped UCB bridge | confidence lemma | retrieval | LML card | bounded/clipped rewards, sub-Gaussian tail contracts | theorem-card-only | memory | theorem-card |
| `TS-BOUND` | final Bayesian regret bound | all above | lower Lean | future theorem | all contracts above | project-local | build | blocked |
