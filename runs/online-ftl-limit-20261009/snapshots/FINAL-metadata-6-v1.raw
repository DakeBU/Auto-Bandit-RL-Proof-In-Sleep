# Conversion Window: Actual FTL best regret and fixed-comparator ordinary-limit criterion

Task id: `ONLINE-FTL-LIMIT-20261009`

Source card:
Scenario card:

## Natural-Language Statement

Write the theorem, proof fragment, or paper equation in precise prose.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `A_t` | action at time `t` | | action process | unmapped |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite action set | typed | task packet | no |
| sub-Gaussian rewards | obligation | cited result | yes |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Mathlib/LML cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | theorem-card route plus local wrappers | pivot only after reviewer records a mathematical reason |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Human proof map | Retrieval cards | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| root | target theorem | TBD | upper | | this file | TBD | TBD | project-local | `lake build && lake build Tests` | planned |

## Gaps

- [ ] Missing definition:
- [ ] Missing lemma:
- [ ] Missing regularity contract:
- [ ] Mathlib candidate to upstream:
- [ ] Missing cited-result entry:


## Own draft five derived FTL limit obligations

Orabona v10 printed2/PDF14 first defines signed regret against the minimum fixed comparator in[0,1], then defines comparator-wise regret. The no-regret sentence displays an ordinary limit <=0. Printed4/PDF16 Theorem1.3 gives actual strict-past mean predictions with initial1/2 and best-fixed regret <=4+4lnT; printed6/PDF18 concludes sublinear growth. Existing upper-epsilon NoRegret and literal finite-real-limit LimitNoRegret remain distinct, existing headers/bodies untouched. The previously accepted abstract signed-unbounded-affine obstruction is not a bounded-square-loss FTL counterexample.

Freeze five DERIVED hinge obligations: F1 actual meanPredict cumulative loss minus empirical-mean comparator loss is nonnegative for EVERY real observation stream and every naturalT including0, by prefix minimization and the actual strict-past prediction. F2 exact fixed-comparator decomposition for all realy,u andT including0: actual regret(u,T)=actual regret(empMean_T,T)-T*(u-empMean_T)^2. F3 for one infinite unit observation stream, the ACTUAL interval-minimum signed best regret divided byT tends to0, using F1 plus source4log upper; no regret lower/upper oracle is input. F4 for the SAME actual FTL and every real fixedu,a, ordinary normalized regret tends toa IFF (u-empMean_T)^2 tends to-a. F5 when the stream empirical mean tends tom, every real comparator limit is-(u-m)^2; restricting comparators to[0,1] produces literal LimitNoRegret. The extra empirical-mean convergence is an explicit sufficient condition; do not attribute it to the arbitrary-stream source theorem.

No probability/expectation/high-probability/minE exchange/pathwise-best-regret nonnegativity for arbitrary algorithms. F1 uses a produced hindsight empirical mean, not a caller minimizer/stability premise. F1/F2 unbounded-stream statements do not claim valid unit game outputs for unbounded observations. F3/F4/F5 retain all-time unit observations. T0 normalization uses Lean total division by0=0 and is irrelevant to atTop; finite F2 includesT0 by empty sums. No unconditional ordinary limit for every arbitrary bounded stream is claimed. A concrete bounded oscillating-mean same-FTL counterexample and exact all-comparator converse remain separate required source-semantics reconciliation work, not silently excluded or declared false here. This package does not complete C1 or the whole Goal; original source obligations and subsequent chapters remain.

Exact frozen headers/DAG: docs/contracts/online-ftl-limit-v1. Contract review pending,0 production bodies compiled;5 derived obligations open.
