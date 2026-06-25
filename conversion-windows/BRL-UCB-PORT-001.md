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
