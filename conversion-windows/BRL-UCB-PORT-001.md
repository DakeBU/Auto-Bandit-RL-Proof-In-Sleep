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
| UCB empirical mean | selected reward sum divided by realized pull count | `UCB.realEmpiricalMean`; `ETC.realHistoryEmpMean` via the compiled history wrapper | trace/history score | compiled-local |
| UCB width | `sqrt(2*c*log(n+1)/pullCount)` | `UCB.realWidth`; `UCB.realHistoryWidth` | path-dependent trace/history confidence radius | compiled-local |
| UCB index/action | empirical mean plus realized width, least-encoded argmax | `UCB.realIndex`; `UCB.realIndexAction`; `UCB.realHistoryIndexAction` | measurable maximal selector | compiled-local |
| `Bandits.UCB.regret_le` | upstream theorem | LML theorem card | regret bound | theorem-card |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite arms | compiled surface | ABRL core | no |
| reward means | compiled rational surface | ABRL core | no |
| sub-Gaussian rewards | generic local fixed-sum/conditional wrappers compiled; UCB fixed-count specialization open | LML/Mathlib route | yes |
| measurable action process | native index selector measurability compiled; recursive environment action law open | local port/LML route | yes |
| expected pull-count bound | theorem-card/obligation | LML route | yes |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| `UCB-INIT` | pull count recursion, finite arms | `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS` | prove positive counts after initialization | pivot only after positivity statement audit |
| `UCB-INDEX` | `UCBRealHistoryIndex`, history score wrappers, local measurable sums/counts | `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS` | realized pull-count width, history/trace equality, least-encoded measurable maximizer | compiled; do not pivot back to deterministic proxy |
| `UCB-GOOD` | index inequality, gap algebra | `MLIB-ORDER-ALGEBRA` | good event implies suboptimal arm pull-count bound | pivot only after checking gap/denominator hypotheses |
| `UCB-TAILS` | fixed-sample sub-Gaussian wrappers plus compiled peeling and missing generated-process arm-stream source | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-SUBGAUSSIAN`, `LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW` | instantiate the fixed-prefix source/law, then apply one-sided tails to each fixed count | pivot only after source-construction or conditional-MGF equivalence audit |
| `UCB-REGRET` | regret decomposition, pull-count bound | `LML-UCB-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | sum gap times expected pulls plus bad events | pivot only after source theorem mismatch is recorded |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-INIT` | initial exploration gives positive counts | finite arms | lower Lean | TBD | finite actions, positive arm count, positive horizon | project-local with generic Nat leaves | build | planned |
| `UCB-INDEX` | source-shaped Real empirical mean, random width, history equality, and selected arm maximizes the UCB index | UCB/history definitions | lower architect | `UCB.realIndexAction_spec`; `UCB.realHistoryIndexAction_finitePairHistoryOfTrace`; `UCB.measurable_realIndexAction` | positive K for selector; timewise measurable action/reward for measurable endpoints; no count positivity needed for totalized division | project-local over Mathlib log/sqrt/measurability APIs | build | compiled |
| `UCB-GOOD` | good event implies pull count bound | index algebra | lower Lean | TBD | positive gap, denominator positivity, bounded width | mathlib-candidate for generic inequality leaves | build | planned |
| `UCB-PEELING-LAW` | adaptive `(pullCount,sumRewards)` event bounded by a finite sum of fixed-sample arm events | fixed-arm prefix source and complete-stream law | lower Lean | `UCB.measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource_identDistrib` | measurable source/canonical spaces and stream coordinates, measurable `Nat x Real` event, decidable projected-count filter; no probability/MGF/independence premise | project-local over Mathlib `IdentDistrib` and finite union | build | compiled |
| `UCB-ARM-STREAM-SOURCE` | instantiate the prefix source and canonical stationary/product stream law for the actual generated UCB sequence | generated action/reward process and stationary arm kernel | lower Lean | TBD | pathwise unused-reward indexing, measurable latent stream, stationary product/independent law, generated-action compatibility | project-local source construction; exact LML array model remains card-only | build | obligation |
| `UCB-TAILS` | upper/lower tail bounds | `UCB-PEELING-LAW`, `UCB-ARM-STREAM-SOURCE`, fixed-sample concentration cards | lower retrieval | TBD local specialization | measurable fibers, sub-Gaussian MGF, positive proxy, finite peeling sum | Mathlib-backed fixed-sum theorem plus project-local adapter | build | obligation |
| `UCB-REGRET` | regret bound from pull counts | regret decomposition | lower Lean | future theorem | all contracts above | project-local | build | blocked |

## Route Decision

Current route: local source-faithful port. The native Real path-dependent index,
history mapping, generic fixed-count peeling, and complete-stream law transport
compile under ABRL's current toolchain. LML remains a theorem card rather than
a dependency. The next route-specific leaf is constructing the fixed-arm
prefix source and canonical stationary/product stream law for the actual
generated UCB sequence, not another deterministic confidence-proxy wrapper.

## Compiled Native Real History Index

| Leaf | Lean-facing statement | APIs/imports | Proof route | Regularity | Retrieval evidence | Status | Failure policy |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-NATIVE-REAL-HISTORY-INDEX` | `UCB.realEmpiricalMean`; `UCB.realWidth`; `UCB.realIndex`; history variants; least-encoded actions; maximality/measurability; exact history/trace equalities | `UCBRealHistoryIndex`, `ETCRealHistoryScore`, `ETCRealArgmaxTie`, finite pair history, measurable sum/count cast, Mathlib log/sqrt/div | define the source score, identify inclusive history at `n` with trace time `n+1`, transport every coordinate, reuse least-encoded finite argmax | `0<K` for action; canonical measurable `Fin K` and timewise measurable action/reward for measurable endpoints; no measure/law/MGF/independence/filtration/count positivity | pinned LML `ucbWidth'`/`ucbWidth`, `empMean'`/`empMean`, `nextArm`, `measurableArgmax`, `regret_le`; local Mathlib cards | compiled-local with external canaries | random width/index mapping is closed; fixed-count peeling now compiles separately; next instantiate its actual generated-process source/law, then fixed-count tails and expected pulls; do not identify the deterministic proxy route with this theorem |

## Compiled Fixed-Count Peeling And Law Transport

| Leaf | Lean-facing statement | APIs/imports | Proof route | Regularity | Retrieval evidence | Status | Failure policy |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-FIXED-COUNT-PEELING-LAW` | latent arm stream/prefix/source definitions; pathwise adaptive-count peeling; complete-stream `IdentDistrib` transport to canonical fixed-prefix events | `UCBFixedCountPeeling`, `ProbabilityUnionBound`, `pullCount_le_time`, `Finset` range/filter/sum, measurable Pi/sum, Mathlib `IdentDistrib` | rewrite selected sum as prefix at realized count, cover by finite count union, apply outer-measure union bound, compose the stream law with each fixed prefix sum | measurable source/canonical spaces and stream coordinates, measurable event, decidable projected-count filter; no probability, independence, MGF, filtration, or positive count | pinned LML `identDistrib_sum_range_snd` and `prob_pullCount_prod_sumRewards_mem_le`; local Mathlib measure/independence/finite-sum cards | compiled-local with two external canaries | generic peeling is closed; next construct `UCB-ARM-STREAM-SOURCE` for the actual generated process or an equivalent conditional-MGF source before claiming one-sided tails |
