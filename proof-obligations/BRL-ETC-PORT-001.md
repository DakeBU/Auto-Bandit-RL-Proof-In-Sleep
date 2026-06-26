# Proof Obligations: BRL-ETC-PORT-001

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ETC-CORE` | verify exploration-arm finite selector | ABRL core | `BanditRLProof.Algorithms.ETC` | `LOCAL-LEAF-ALGORITHM-WRAPPERS`, `MLIB-FINTYPE-FIN` | finite selector value proof | finite action count, nonzero exploration horizon | project-local | reviewer | `ETC.exploreArm_val`, `ETC.exploreArm_eq_of_mod_eq` | check | compiled |
| `ETC-COUNT` | prove round-robin pull-count arithmetic | `ETC.exploreArm` | pull count recursion, Nat modulo lemmas | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | induction on time plus finite-cycle arithmetic | finite actions, positive arm count | mathlib-candidate for generic arithmetic leaves | lower Lean | `pullCount_succ_of_eq`, `pullCount_succ_of_ne`, `pullCount_const_self`, `pullCount_const_of_ne` | build | planned |
| `ETC-COMMIT` | define empirical-mean argmax commit | finite history | finite argmax contract, reward sums | `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS` | expose commit oracle before probability proof | finite arms, nonempty candidate set, denominator positivity | project-local wrapper | middle/lower | TBD | build | planned |
| `ETC-CONC` | wrong-commit probability bound | sub-Gaussian cards | concentration theorem cards | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL` | reduce wrong commit to pairwise empirical-mean tail events | measurability, integrability, independence/sub-Gaussian contract | theorem-card-only until imported or ported | retrieval | TBD | memory/build | obligation |
| `ETC-FINAL` | local theorem compatible with `Bandits.ETC.regret_le` | all above | regret decomposition, pull-count ledger | `LML-ETC-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | exploration regret plus wrong-commit regret | all upstream contracts above | project-local | lower Lean | TBD | build | blocked |
