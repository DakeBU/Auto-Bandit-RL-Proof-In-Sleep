# Conversion Window: UCB regret theorem-card route

Task id: `BRL-UCB-PORT-001`

Source card: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

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

## Local API And Proof Route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| `UCB-INIT` | pull count recursion, finite arms | `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS` | prove positive counts after initialization | pivot only after positivity statement audit |
| `UCB-INDEX` | UCB score surface, future log/sqrt API | `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA` | selected arm maximizes empirical mean plus width | pivot only after confidence-radius API audit |
| `UCB-GOOD` | index inequality, gap algebra | `MLIB-ORDER-ALGEBRA` | good event implies suboptimal arm pull-count bound | pivot only after checking gap/denominator hypotheses |
| `UCB-TAILS` | concentration theorem cards | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL` | one-sided tails plus union/summability | pivot only after sub-Gaussian and measurability contract audit |
| `UCB-REGRET` | regret decomposition, pull-count bound | `LML-UCB-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | sum gap times expected pulls plus bad events | pivot only after source theorem mismatch is recorded |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-INIT` | initial exploration gives positive counts | finite arms | lower Lean | TBD | finite actions, positive arm count, positive horizon | project-local with generic Nat leaves | build | planned |
| `UCB-INDEX` | selected arm maximizes UCB index | UCB definition | lower architect | TBD | positive counts, positive log argument, order/algebra facts | mathlib-candidate for generic order/algebra leaves | build | planned |
| `UCB-GOOD` | good event implies pull count bound | index algebra | lower Lean | TBD | positive gap, denominator positivity, bounded width | mathlib-candidate for generic inequality leaves | build | planned |
| `UCB-TAILS` | upper/lower tail bounds | concentration cards | lower retrieval | cited result | measurability, integrability, sub-Gaussian MGF, summability | theorem-card-only until imported or ported | memory | obligation |
| `UCB-REGRET` | regret bound from pull counts | regret decomposition | lower Lean | future theorem | all contracts above | project-local | build | blocked |

## Route Decision

Current route: `card-only` until a task explicitly aligns Mathlib/LML
dependencies or ports the needed concentration and probability lemmas.
