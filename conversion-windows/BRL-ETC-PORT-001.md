# Conversion Window: Explore-Then-Commit regret route

Task id: `BRL-ETC-PORT-001`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-Language Statement

Explore-Then-Commit pulls each arm a fixed number of times, commits to the arm
with the largest empirical mean, and pays regret through exploration plus the
probability of committing to a suboptimal arm.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| round-robin exploration | arm `t % K` | `ETC.exploreArm` | finite action selector | compiled |
| `m` | exploration pulls per arm | `ETC.Spec.explorationPulls` | parameter | compiled |
| commit argmax | selected empirical best arm | `ETC.CommitOracle.choose` | contract | typed |
| `Bandits.ETC.regret_le` | upstream theorem | LML theorem card | regret bound | theorem-card |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| `ETC-COUNT` | pull count recursion, `ETC.exploreArm` | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | induction plus finite-cycle arithmetic | pivot only after modulo/count statement audit |
| `ETC-WRONG` | concentration theorem cards | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL` | pairwise empirical-mean tail event union | pivot only after checking sub-Gaussian and measurability contracts |
| `ETC-REGRET` | regret decomposition cards | `LML-ETC-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | exploration term plus wrong-commit term | pivot only after source theorem mismatch is recorded |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ETC-COUNT` | each arm has `m` exploration pulls | round-robin arithmetic | lower Lean | TBD | finite arms, positive arm count | mathlib-candidate for generic arithmetic leaves | build | planned |
| `ETC-COMMIT` | commit arm maximizes empirical mean | argmax contract | lower architect | TBD | nonempty finite candidates, denominator positivity | project-local wrapper | build | planned |
| `ETC-WRONG` | wrong commit probability | sub-Gaussian tail | retrieval | cited result | measurability, integrability, sub-Gaussian independence | theorem-card-only | memory | obligation |
| `ETC-PULL` | pull count after commit | `ETC-COMMIT`, `ETC-WRONG` | lower Lean | TBD | finite horizon, committed arm exists | project-local | build | planned |
| `ETC-REGRET` | regret bound | pull-count decomposition | lower Lean | future theorem | all contracts above | project-local | build | blocked |
