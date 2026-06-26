# Proof Obligations: BRL-TS-BAYES-001

Source card: `TXT-SLIVKINS-2019-2024`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `TS-SKETCH` | prior and reward-kernel descriptor surface | ABRL Thompson file | `BanditRLProof.Algorithms.Thompson` | `MLIB-PROBABILITY-KERNEL`, `MLIB-FINTYPE-FIN` | keep descriptor typed while probability layer is staged | finite action and horizon descriptors | project-local | reviewer | `Thompson.PriorSketch` | check | compiled |
| `TS-POSTERIOR` | posterior action identity | conditional distribution | LML theorem card, future probability imports | `LML-TS-POSTERIOR-ACTION`, `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-KERNEL` | theorem-card route via posterior best-action distribution | measurability, conditional distribution, posterior regularity | theorem-card-only until imported or ported | retrieval | LML card | memory | theorem-card |
| `TS-DECOMP` | Bayesian regret decomposition | posterior identity | regret decomposition cards, integral notation | `LML-TS-BAYES-REGRET`, `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA` | decompose regret under posterior action identity | integrability, finite expected regret, prior support | mathlib-candidate for generic integral/algebra leaves | lower architect | TBD | build | planned |
| `TS-CONC` | clipped-UCB concentration bridge | sub-Gaussian cards | LML concentration cards | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-REAL-LOG-SQRT` | reduce clipped confidence terms to reusable tail lemmas | sub-Gaussian, bounded/clipped rewards, summability | theorem-card-only until imported or ported | retrieval | LML card | memory | theorem-card |
| `TS-FINAL` | local Bayesian regret theorem | all above | local wrappers plus theorem cards/imports | `LML-TS-BAYES-REGRET`, `MLIB-ASYMPTOTICS` | combine posterior identity, decomposition, and concentration | all upstream contracts above | project-local | lower Lean | TBD | build | blocked |
