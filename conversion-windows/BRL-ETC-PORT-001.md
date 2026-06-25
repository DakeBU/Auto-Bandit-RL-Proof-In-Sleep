# Conversion Window: Explore-Then-Commit regret route

Task id: `BRL-ETC-PORT-001`

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

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `ETC-COUNT` | each arm has `m` exploration pulls | round-robin arithmetic | lower Lean | TBD | build | planned |
| `ETC-COMMIT` | commit arm maximizes empirical mean | argmax contract | lower architect | TBD | build | planned |
| `ETC-WRONG` | wrong commit probability | sub-Gaussian tail | retrieval | cited result | memory | obligation |
| `ETC-PULL` | pull count after commit | `ETC-COMMIT`, `ETC-WRONG` | lower Lean | TBD | build | planned |
| `ETC-REGRET` | regret bound | pull-count decomposition | lower Lean | future theorem | build | blocked |
