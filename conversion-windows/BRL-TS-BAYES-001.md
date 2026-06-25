# Conversion Window: Thompson sampling Bayesian regret

Task id: `BRL-TS-BAYES-001`

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

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `TS-POSTERIOR` | posterior action identity | conditional distribution | retrieval | LML card | memory | theorem-card |
| `TS-DECOMP` | Bayesian regret decomposition | posterior identity | lower architect | TBD | build | planned |
| `TS-CLIPPED-UCB` | clipped UCB bridge | confidence lemma | retrieval | LML card | memory | theorem-card |
| `TS-BOUND` | final Bayesian regret bound | all above | lower Lean | future theorem | build | blocked |
