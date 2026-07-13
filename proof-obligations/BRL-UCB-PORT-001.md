# Proof Obligations: BRL-UCB-PORT-001

Source card: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-ROUTE` | choose card-only, port, or dependency route | task packet | pinned LML source, ABRL core | `LML-UCB-REGRET`, `TXT-LATTIMORE-SZEPESVARI-2020` | port the mathematical route locally while keeping actual LML symbols card-only across the toolchain mismatch | theorem-card status, toolchain alignment | project-local decision | upper | route recorded in task/conversion window | memory | compiled |
| `UCB-CORE` | verify ABRL finite trace and pseudo-regret surfaces | `BanditRLProof.Core`, `Regret`, `LeafLemmas`, `PullCountDecomposition`, `RegretDecomposition` | pull counts, segment counts, reward sums, gap surface, deterministic pull-count partition, deterministic regret-by-pull-count identity | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS`, `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`, `LOCAL-LEAF-REGRET-DECOMPOSITION`, `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | compiled dependency-light bookkeeping plus Mathlib Finset wrappers, finite-action count partition, and arm reindexing | finite arms, horizon, rational mean model | project-local compiled leaves | reviewer | `pullCount_le_time`, `pullCount_add_le`, `finset_sum_pullCount_eq_time`, `sumRewards_add_eq_of_forall_ne_between`, `pseudoRegret_add_eq_of_forall_gap_zero_between`, `pseudoRegret_eq_finset_sum_gap_mul_pullCount` | `python3 tools/bandit.py check` | compiled |
| `UCB-INDEX` | compile the pinned-source Real empirical mean, realized pull-count width, finite-history index, and least-encoded selector | port route | `UCBRealHistoryIndex`, `ETCRealHistoryScore`, measurable sum/count APIs, Real log/sqrt | `LOCAL-LEAF-UCB-NATIVE-REAL-HISTORY-INDEX`, `MLIB-REAL-LOG-SQRT`, `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL` | define `sumRewards/pullCount` and `sqrt(2*c*log(n+1)/pullCount)`, align inclusive history at `n` with trace time `n+1`, reuse least-encoded argmax | positive K only for selector; canonical measurable Fin and timewise action/reward measurability for measurable endpoints; no count positivity or probability law | project-local over Mathlib and compiled local wrappers | lower Lean | `UCB.realIndexAction`; `UCB.realHistoryIndexAction_finitePairHistoryOfTrace`; `UCB.measurable_realIndexAction` | build | compiled |
| `UCB-CONC` | record or prove sub-Gaussian tail lemmas | concentration cards, `MeasureFoundation`, `MeasurableSums`, `MeasurableLocalQuantities`, `MeasurableRegret`, `MeasurablePullCount`, `MeasurablePullCountCast`, `ExpectationFoundation`, `ExpectationSums`, `ExpectationPullCount`, `ExpectationWeightedPullCount` | LML/Mathlib concentration route plus measurable action-event/indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities | `LOCAL-LEAF-MEASURE-FOUNDATION`, `LOCAL-LEAF-MEASURABLE-SUMS`, `LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES`, `LOCAL-LEAF-MEASURABLE-REGRET`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST`, `LOCAL-LEAF-EXPECTATION-FOUNDATION`, `LOCAL-LEAF-EXPECTATION-SUMS`, `LOCAL-LEAF-EXPECTATION-PULLCOUNT`, `LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`, `MLIB-CONDITIONAL-EXPECTATION` | one-sided and union-bounded tail event control after event, pull-indicator, selected-reward indicator, finite-sum, `sumRewards`, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities are explicit | measurability, lower-integral event measures, lower-integral finite sums, lower-integral pull counts, lower-integral weighted pull counts, integrability, sub-Gaussian MGF, summability | theorem-card-only until imported or ported, with local measurable-event, indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count leaves compiled | lower retrieval | `measurableSet_actionTrace_eval_eq`, `measurable_actionTrace_eval_eq_indicator_const`, `measurable_actionTrace_eval_eq_indicator_reward`, `measurable_finset_sum_indicator_reward`, `measurable_sumRewards`, `measurable_pseudoRegret`, `measurable_pullCount`, `measurable_natCast_pullCount`, `lintegral_actionTrace_eval_eq_indicator_one`, `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`, `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`, `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` plus TBD tail declarations | memory/build | obligation |
| `UCB-PEELING-LAW` | transport the adaptive `(pullCount,sumRewards)` event to a finite sum of fixed-sample arm-reward events | native index and a fixed-arm prefix source | `UCBFixedCountPeeling`, `ProbabilityUnionBound`, `IdentDistrib`, count/sum wrappers | `LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW`, `LOCAL-LEAF-UCB-NATIVE-REAL-HISTORY-INDEX`, `LML-UCB-REGRET`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-FINSET-SUMS` | pathwise selected-reward prefix identity, finite count union, then complete-stream law transport by measurable fixed-prefix composition | measurable source/canonical spaces, measurable stream coordinates and event, decidable projected-count filter; no probability/MGF/independence premise | project-local source transport over Mathlib `IdentDistrib` and finite union | lower Lean | `UCB.measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource_identDistrib` | build | compiled |
| `UCB-ARM-STREAM-SOURCE` | construct the prefix source and canonical stationary arm-stream law for the actual generated UCB sequence | `UCB-PEELING-LAW`, generated UCB action/reward process | recursive unused-reward indexing or array/product source; policy measurability; stationary arm laws | `LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW`, `LML-UCB-REGRET`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-KERNEL` | mirror LML array/stream representation, or prove an equivalent adaptive conditional-MGF source | exact selected-reward-prefix identity, measurable latent stream, stationary product/independent law, generated-action compatibility | project-local source construction; LML remains card-only | lower Lean | TBD | build | obligation |
| `UCB-FINAL` | local theorem compatible with `Bandits.UCB.regret_le` | all above including `UCB-ARM-STREAM-SOURCE` | compiled native Real index, deterministic regret decomposition, pull-count partition/bounds, fixed-sample tails | `LOCAL-LEAF-UCB-NATIVE-REAL-HISTORY-INDEX`, `LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW`, `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`, `LOCAL-LEAF-REGRET-DECOMPOSITION`, `LML-UCB-REGRET`, `MLIB-ASYMPTOTICS` | source-faithful index behavior, fixed-count peeling tails, expected pull counts, then gap-weighted sum | all upstream contracts above | project-local final theorem | lower Lean | TBD | build | blocked |

Compiled bridge update: `EXP-PULLCOUNT-LE-TIME` is now available through
`LOCAL-LEAF-EXPECTATION-PULLCOUNT-BOUNDS` and declaration
`lintegral_natCast_pullCount_le_time`.  Use it as an `ENNReal` probability
pull-count budget bound for UCB expected-count scaffolding; it does not close
`EXP-REGRET-PULLCOUNT`, concentration, or the final UCB theorem.

Compiled weighted bridge update: `EXP-WEIGHTED-PULLCOUNT-LE-TIME` is now
available through `LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT-BOUNDS` and
declaration
`lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.  Use it
as the `ENNReal` weighted probability budget bound before choosing a
`Fin K`/`Finset.univ`, scalar-conversion, or Bochner expected-regret route.

Compiled finite-arm bridge update: `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` is now
available through `LOCAL-LEAF-EXPECTATION-FINITE-BANDIT-BOUNDS` and declaration
`lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.  Use it as
the finite-arm `Finset.univ` budget bound before the separate scalar conversion
for `FiniteBanditModel.gap : Fin K -> Rat`.

Compiled model-gap bridge update: `EXP-MODEL-GAP-OFREAL-BOUND` is now available
through `LOCAL-LEAF-EXPECTATION-FINITE-BANDIT-MODEL-BOUNDS` and declaration
`lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time`.
Use it as an `ENNReal.ofReal` surrogate bound for `FiniteBanditModel.gap`; it
does not prove Rat-valued expected regret or gap faithfulness.

Compiled scalar bridge update: `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` is now
available through `LOCAL-LEAF-SCALAR-ENNREAL` and declaration
`ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg`.  Use it for exact scalar
conversion under explicit nonnegativity before any UCB Rat-valued expected
regret claim.

Compiled pointwise pseudo-regret bridge update:
`OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` is now available through
`LOCAL-LEAF-SCALAR-PSEUDOREGRET` and declaration
`ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg`.
Use it as a scalar/model faithfulness bridge under explicit model-gap
nonnegativity; it does not prove expected regret, model-gap nonnegativity,
concentration, or the final UCB theorem.

Compiled lower-integral pseudo-regret bridge update:
`EXP-OFREAL-PSEUDOREGRET-BOUND` is now available through
`LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-OFREAL-BOUNDS` and declaration
`lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg`.
Use it as an `ENNReal.ofReal` lower-integral bound under explicit model-gap
nonnegativity; it does not prove Rat-valued expected regret, Bochner expected
regret, model-gap nonnegativity, concentration, or the final UCB theorem.

Compiled Rat-contract pseudo-regret bridge update:
`EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` is now available through
`LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-RAT-BOUNDS` and declaration
`lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg`.
Use it when UCB scaffolding has a Rat-level gap nonnegativity contract; it does
not prove that contract from `FiniteBanditModel.bestArm`.

## Current Reviewer Note

The upstream LML theorem is a theorem card only.  Do not export it as an ABRL
local proof until the route is imported or ported.

## Native Real History Index Obligation

`UCB-NATIVE-REAL-HISTORY-INDEX` is discharged in
`BanditRLProof.Algorithms.UCBRealHistoryIndex`. The module defines the actual
source-shaped Real empirical mean and sample-path-dependent width
`sqrt(2*c*log(n+1)/pullCount)`, their sum, inclusive finite-pair-history
versions, and least-encoded score maximizers.

The proof reuses the compiled finite-history count/sum/mean wrappers, maps the
inclusive history at index `n` to trace horizon `n+1`, and proves exact score
and selector equality. Mathlib measurable division/sqrt plus local measurable
sum/count declarations prove every score coordinate and the selected action
measurable. The selector also exposes score maximality for every arm.

Regularity is `0 < K` for the selector and timewise measurable action/reward
coordinates for measurable endpoints. There is no probability measure,
reward law, MGF, independence, filtration, or count-positivity assumption.
Retrieval evidence is pinned LML `ucbWidth'`, `ucbWidth`, `empMean'`,
`empMean`, `nextArm`, `measurableArgmax`, and `Bandits.UCB.regret_le`, plus
Mathlib log/sqrt and local finite-sum/measurability cards.

Status is `leanCompiled` with focused and external canary builds. Failure
policy: do not reuse the older deterministic `proxy : Nat -> Arm -> NNReal`
surface as though it were this random width. The next source-faithful blocker
is now source construction for the compiled fixed-count peeling interface;
after that come one-sided fixed-count sub-Gaussian tails, expected pull counts,
and the final regret sum.

## Fixed-Count Peeling Law Obligation

`UCB-FIXED-COUNT-PEELING-LAW` discharges `UCB-PEELING-LAW` in
`BanditRLProof.Algorithms.UCBFixedCountPeeling`. The source structure records a
measurable latent `Nat -> Fin K -> Real` table and the exact pathwise identity
between `sumRewards` and the arm prefix of length `pullCount`. The first theorem
peels an adaptive `(pullCount,sumRewards)` event over the finite filtered range
`0,...,n`; the second transports every fixed-count term from one
`IdentDistrib` law for the complete stream.

The proof uses `pullCount_le_time`, `Finset.range/filter/sum`,
`ProbabilityUnionBound.measure_biUnion_finset_le`, measurable Pi evaluation,
`Finset.measurable_sum`, and `IdentDistrib.comp/measure_mem_eq`. Its contracts
are measurable source/canonical spaces, measurable stream coordinates,
measurable event `s`, and decidability of the projected count predicate. It
does not assume a probability measure, independence, an MGF, filtration, or a
positive count.

Retrieval evidence is pinned LML
`SumRewards.identDistrib_sum_range_snd` and
`prob_pullCount_prod_sumRewards_mem_le` at commit
`19dc3ab132c2a7539f5944503d1114eac4c5bb74`, plus the local Mathlib cards for
`IdentDistrib`, finite sums, measure, and finite union bounds. Status is
`leanCompiled` with focused and external canary builds. Failure policy: the
generic peeling/law theorem is closed, but it must not be presented as a UCB
tail theorem until `UCB-ARM-STREAM-SOURCE` constructs the prefix source and
canonical stationary/product stream law for the actual generated UCB process,
or proves a separately recorded conditional-MGF substitute.
