# Proof Obligations: BRL-ETC-PORT-001

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ETC-CORE` | verify exploration-arm finite selector | ABRL core | `BanditRLProof.Algorithms.ETC` | `LOCAL-LEAF-ALGORITHM-WRAPPERS`, `MLIB-FINTYPE-FIN` | finite selector value proof | finite action count, nonzero exploration horizon | project-local | reviewer | `ETC.exploreArm_val`, `ETC.exploreArm_eq_of_mod_eq` | check | compiled |
| `ETC-COUNT` | prove round-robin pull-count arithmetic | `ETC.exploreArm`, `PullCountDecomposition` | pull count recursion, finite-action count partition, Nat modulo lemmas | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | induction on time plus finite-cycle arithmetic, with `finset_sum_pullCount_eq_time` as the global count budget | finite actions, positive arm count | project-local compiled partition plus mathlib-candidate arithmetic leaves | lower Lean | `pullCount_succ_of_eq`, `pullCount_succ_of_ne`, `pullCount_add_eq_of_forall_ne_between`, `pullCount_add_eq_add_of_forall_eq_between`, `finset_sum_pullCount_eq_time` | build | planned |
| `ETC-COMMIT` | define empirical-mean argmax commit | finite history | finite argmax contract, reward sums | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS` | expose commit oracle before probability proof | finite arms, nonempty candidate set, denominator positivity | project-local wrapper | middle/lower | `sumRewards_add_eq_of_forall_ne_between` | build | planned |
| `ETC-CONC` | wrong-commit probability bound | sub-Gaussian cards, `MeasureFoundation`, `MeasurableSums`, `MeasurableLocalQuantities`, `MeasurableRegret`, `MeasurablePullCount`, `MeasurablePullCountCast`, `ExpectationFoundation`, `ExpectationSums`, `ExpectationPullCount`, `ExpectationWeightedPullCount` | concentration theorem cards plus measurable action-event/indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities | `LOCAL-LEAF-MEASURE-FOUNDATION`, `LOCAL-LEAF-MEASURABLE-SUMS`, `LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES`, `LOCAL-LEAF-MEASURABLE-REGRET`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST`, `LOCAL-LEAF-EXPECTATION-FOUNDATION`, `LOCAL-LEAF-EXPECTATION-SUMS`, `LOCAL-LEAF-EXPECTATION-PULLCOUNT`, `LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL` | reduce wrong commit to pairwise empirical-mean tail events after event, pull-indicator, selected-reward indicator, finite-sum, `sumRewards`, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities are explicit | measurability, lower-integral event measures, lower-integral finite sums, lower-integral pull counts, lower-integral weighted pull counts, integrability, independence/sub-Gaussian contract | theorem-card-only until imported or ported, with local measurable-event, indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count leaves compiled | retrieval | `measurableSet_actionTrace_eval_eq`, `measurable_actionTrace_eval_eq_indicator_const`, `measurable_actionTrace_eval_eq_indicator_reward`, `measurable_finset_sum_indicator_reward`, `measurable_sumRewards`, `measurable_pseudoRegret`, `measurable_pullCount`, `measurable_natCast_pullCount`, `lintegral_actionTrace_eval_eq_indicator_one`, `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`, `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`, `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` plus TBD tail declarations | memory/build | obligation |
| `ETC-FINAL` | local theorem compatible with `Bandits.ETC.regret_le` | all above | compiled deterministic regret decomposition, pull-count partition ledger | `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`, `LOCAL-LEAF-REGRET-DECOMPOSITION`, `LML-ETC-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | exploration regret plus wrong-commit regret | all upstream contracts above | project-local | lower Lean | `pseudoRegret_eq_finset_sum_gap_mul_pullCount`, `finset_sum_pullCount_eq_time` plus TBD final theorem | build | blocked |

Compiled bridge update: `EXP-PULLCOUNT-LE-TIME` is now available through
`LOCAL-LEAF-EXPECTATION-PULLCOUNT-BOUNDS` and declaration
`lintegral_natCast_pullCount_le_time`.  Use it as an `ENNReal` probability
pull-count budget bound for ETC expected-count scaffolding; it does not close
`EXP-REGRET-PULLCOUNT`, wrong-commit concentration, or the final ETC theorem.

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
conversion under explicit nonnegativity before any ETC Rat-valued expected
regret claim.

Compiled pointwise pseudo-regret bridge update:
`OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` is now available through
`LOCAL-LEAF-SCALAR-PSEUDOREGRET` and declaration
`ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg`.
Use it as a scalar/model faithfulness bridge under explicit model-gap
nonnegativity; it does not prove expected regret, model-gap nonnegativity,
concentration, or the final ETC theorem.

Compiled lower-integral pseudo-regret bridge update:
`EXP-OFREAL-PSEUDOREGRET-BOUND` is now available through
`LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-OFREAL-BOUNDS` and declaration
`lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg`.
Use it as an `ENNReal.ofReal` lower-integral bound under explicit model-gap
nonnegativity; it does not prove Rat-valued expected regret, Bochner expected
regret, model-gap nonnegativity, concentration, or the final ETC theorem.

Compiled Rat-contract pseudo-regret bridge update:
`EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` is now available through
`LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-RAT-BOUNDS` and declaration
`lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg`.
Use it when ETC scaffolding has a Rat-level gap nonnegativity contract; it does
not prove that contract from `FiniteBanditModel.bestArm`.

Wrong-commit event-reduction design update:
`ETC-WRONG-COMMIT-PROBABILITY-DESIGN` is recorded as a theorem-card-only /
missing-leaf design in
`research-wiki/open-problems/etc-wrong-commit-probability-design.md`.  Use it
as the first `ETC-CONC` layer before any Hoeffding, sub-Gaussian, martingale,
filtration, or final ETC theorem attempt.  The intended event reduction is:
wrong commit implies existence of a non-best arm whose empirical mean beats or
ties the selected best arm's empirical mean.

Compiled wrong-commit event leaf update:
`ETC-MEAS-COMMITARM-NE-BESTARM` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.measurableSet_commitArm_ne_bestArm`.  It proves only that a measurable
finite-valued commit arm yields a measurable non-best-commit event.  It does
not prove empirical-mean comparison-event measurability, measure monotonicity,
wrong-commit event reduction, concentration, or final ETC regret.  Ask
Extended Pro again before choosing between those next leaves.

Compiled wrong-commit event-reduction leaf update:
`ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.wrong_commit_subset_exists_empMean_ge_bestArm`.  It proves only the pure
set inclusion from the wrong-commit event to the existential empirical-mean
comparison event, under the explicit commit-arm argmax contract.  It does not
prove measure monotonicity, probability bounds, empirical-mean comparison-event
measurability, finite event unions, concentration, or final ETC regret.  Ask
Extended Pro again before choosing the next probability-facing wrapper.

Compiled wrong-commit measure-wrapper leaf update:
`ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`.  It proves only
the arbitrary-measure inequality obtained from the compiled subset lemma and
`mu.mono`.  It does not prove empirical-mean comparison-event measurability,
finite event unions, concentration, filtration, or final ETC regret.  The
subsequent regularity/event-structure leaves are recorded below.

Compiled pairwise empirical-mean event leaf update:
`ETC-MEAS-EMPMEAN-GE-EMPMEAN` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.measurableSet_empMean_ge_empMean`.  It proves only that pairwise
Rat-valued empirical-mean comparison events are measurable under coordinate
measurability of `empMean`.  It does not prove finite existential/union event
measurability, concentration, filtration, empirical-mean construction, or final
ETC regret.  The finite event wrapper is recorded below.

Compiled finite existential wrong-mean event leaf update:
`ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`.  It proves only that
the finite existential wrong-mean event over non-best arms is measurable under
coordinate measurability of `empMean`, using `Finset.measurableSet_biUnion` and
the compiled pairwise event wrapper.  It does not prove a probability union
bound, concentration, filtration, empirical-mean construction, or final ETC
regret.  The finite-union probability wrapper is recorded below.

Compiled finite-union probability wrapper leaf update:
`ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM` is now available
through `BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`.  It proves only that
the measure of the finite existential wrong-mean event is bounded by the finite
sum of guarded pairwise wrong-mean event measures.  It uses
`MeasureTheory.measure_biUnion_finset_le` and does not require event
measurability, empirical-mean coordinate measurability, a probability measure,
`commitArm`, argmax, concentration, filtration, empirical-mean construction, or
final ETC regret.  The next paragraph records the final elementary assembly
after it was selected and compiled.

Compiled final elementary probability assembly leaf update:
`ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`.  It proves only that
the measure of the wrong-commit event is bounded by the finite sum of guarded
pairwise wrong-mean event measures under the explicit empirical-mean argmax
contract.  It composes
`ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset` with
`ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`, and does not require a
probability measure, event measurability, empirical-mean coordinate
measurability, concentration, filtration, empirical-mean construction, pairwise
tail bounds, or final ETC regret.  The next paragraph records the abstract
pairwise-tail consumer after it was selected and compiled.

Compiled abstract pairwise-tail consumer leaf update:
`ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`.  It proves only that the
wrong-commit event is bounded by the finite sum of abstract non-best pairwise
tail bounds, under the explicit empirical-mean argmax contract and tail
assumptions.  It consumes the compiled finite guarded wrong-mean-event sum
wrapper, `Finset.sum_le_sum`, and `mu.mono`; it does not prove empirical-mean
construction, actual concentration, filtration, conditional expectation,
independence, or final ETC regret.  The next paragraph records the filtered
nonbest tail sharpening after it was selected and compiled.

Compiled if-zeroed nonbest pairwise-tail consumer leaf update:
`ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`.  It proves only
that the wrong-commit event is bounded by
`sum (fun a => if a = model.bestArm then 0 else tail a)`, under the explicit
empirical-mean argmax contract and abstract non-best tail assumptions.  It
does not prove empirical-mean construction, actual concentration, filtration,
conditional expectation, independence, filtered `Finset.filter` normalization,
or final ETC regret.  The next paragraph records the filtered-sum
normalization after it was selected and compiled.

Compiled filtered-sum pairwise-tail consumer leaf update:
`ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail`.  It proves only
that the wrong-commit event is bounded by the filtered finite sum over non-best
arms.  It consumes the if-zeroed nonbest tail consumer plus
`Finset.sum_filter`/`Finset.sum_congr`; it does not prove empirical-mean
construction, actual concentration, filtration, conditional expectation,
independence, or final ETC regret.  The next paragraph records the first
deterministic denominator-support leaf after it was selected and compiled.

Compiled exploration pull-count positivity leaf update:
`ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` is now available through
`BanditRLProof.Algorithms.ETCTraceCountLemmas` and declaration
`ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos`.  It proves only
that every arm has positive pull count at the fixed-commit ETC exploration
horizon when `0 < spec.explorationPulls`.  It consumes the exact count theorem
`ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`; it does not define
empirical means, introduce a measure, or prove concentration, filtration,
conditional expectation, independence, or final ETC regret.  The next
paragraph records the Rat-cast denominator adapter after it was selected and
compiled.

Compiled Rat-cast exploration pull-count positivity leaf update:
`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` is now available
through `BanditRLProof.Algorithms.ETCTraceCountLemmas` and declaration
`ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos`.  It
proves only that the fixed-commit ETC exploration-horizon pull count is
positive after casting to `Rat`, under the same
`0 < spec.explorationPulls` assumption.  It consumes the Nat positivity theorem
and `exact_mod_cast`; it does not define empirical means, introduce a measure,
or prove concentration, filtration, conditional expectation, independence, or
final ETC regret.  The next paragraph records the Rat nonzero-denominator
adapter after it was selected and compiled.

Compiled Rat-cast exploration pull-count nonzero leaf update:
`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO` is now available
through `BanditRLProof.Algorithms.ETCTraceCountLemmas` and declaration
`ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero`.  It
proves only that the fixed-commit ETC exploration-horizon pull count is nonzero
after casting to `Rat`, under the same `0 < spec.explorationPulls` assumption.
It consumes the Rat positivity adapter and `ne_of_gt`; it does not define
empirical means, introduce division or zero-fallback API choices, introduce a
measure, or prove concentration, filtration, conditional expectation,
independence, or final ETC regret.  Use local two-agent review before choosing
empirical-mean construction or the actual pairwise concentration route.

Compiled fixed-commit exploration empirical-mean leaf update:
`ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` is now available through
`BanditRLProof.Algorithms.ETCEmpiricalMean` and declarations
`ETC.empMeanAtExploration` plus
`ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls`.  It defines
the deterministic empirical mean at the fixed-commit ETC exploration horizon
and rewrites the denominator to `spec.explorationPulls` using
`ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`.  The theorem
requires only `spec : ETC.Spec K`, `commitArm a : Fin K`, and
`reward : RewardTrace Rat`; it does not require positivity because Rat
division is total.  It does not introduce an argmax oracle, stochastic reward
trace, measurability wrapper, probability measure, concentration, filtration,
conditional expectation, independence, or final ETC regret.  Ask Extended Pro
again before choosing argmax/measurability wiring for this API or the actual
pairwise concentration route.

Compiled fixed-commit exploration numerator-measurability leaf update:
`ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION` is now available
through `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability` and
declaration `ETC.measurable_sumRewards_actionWithCommit_exploration`.  It
proves measurability of the selected-reward numerator of the fixed-commit ETC
empirical mean under stochastic reward traces with timewise measurable
coordinates.  It consumes `measurable_sumRewards` with the constant stochastic
action trace `fun _ : Omega => ETC.actionWithCommit spec commitArm` and closes
the action-coordinate measurability obligation with `measurable_const`.  It
does not introduce `Measure`, `MeasurableDiv`, a full empirical-mean
measurability theorem, argmax wiring, concentration, filtration, conditional
expectation, independence, or final ETC regret.  The follow-up full
empirical-mean measurability wrapper is recorded below; remaining route choices
still require Extended Pro review before moving to a Mathlib/Rat division
import or wrapper, argmax wiring, or the actual pairwise concentration route.

Compiled fixed-commit exploration empirical-mean measurability leaf update:
`ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST` is now
available through
`BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability` and declaration
`ETC.measurable_empMeanAtExploration_of_measurable_div_const`.  It proves
measurability of `ETC.empMeanAtExploration spec commitArm (reward omega) a`
under stochastic reward traces once the explicit contract
`forall c : Rat, Measurable (fun x : Rat => x / c)` is supplied.  It consumes
`ETC.measurable_sumRewards_actionWithCommit_exploration` and composes the
numerator with division by the fixed pull-count denominator.  It does not add a
Mathlib/Rat division-measurability import, argmax wiring, concentration,
filtration, conditional expectation, independence, or final ETC regret.  Ask
Extended Pro again before choosing the Mathlib/Rat division-measurability
import or wrapper, argmax wiring, or the actual pairwise concentration route.

Compiled Rat division-by-constant measurability wrapper update:
`RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON` is now available through
`BanditRLProof.RatMeasurability` and declaration
`measurable_rat_div_const`.  It proves
`Measurable (fun x : Rat => x / c)` under `[MeasurableSpace Rat]` and
`[MeasurableSingletonClass Rat]`, using countability of `Rat`.  It deliberately
does not claim the result under an arbitrary measurable space without
measurable singletons, and it does not remove the `hdiv_const` argument from
the ETC empirical-mean theorem in this batch.  The next narrow leaf is
`ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION`, the no-`hdiv_const`
empirical-mean measurability theorem consuming this wrapper.

Compiled no-`hdiv_const` fixed-commit exploration empirical-mean
measurability leaf update:
`ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION` is now available
through `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability` and
declaration `ETC.measurable_empMeanAtExploration`.  It proves measurability of
`ETC.empMeanAtExploration spec commitArm (reward omega) a` under stochastic
reward traces with `[MeasurableSingletonClass Rat]`, consuming
`measurable_rat_div_const` and the explicit-division theorem
`ETC.measurable_empMeanAtExploration_of_measurable_div_const`.  It does not
add a measure, argmax wiring, concentration, filtration, conditional
expectation, independence, or final ETC regret.  The next Extended Pro round
selected a coordinate-shaped empirical-mean measurability wrapper before any
commit argmax or pairwise concentration work.

Compiled coordinate fixed-commit exploration empirical-mean measurability leaf
update:
`ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES` is now available through
`BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability` and declaration
`ETC.measurable_empMeanAtExploration_coordinates`.  It packages
`ETC.measurable_empMeanAtExploration` into the
`forall a : Fin K, Measurable ...` shape consumed by downstream empirical-mean
event measurability lemmas.  It does not add a measure, commit oracle,
argmax proof, concentration, filtration, conditional expectation,
independence, or final ETC regret.  The next Extended Pro recommendation was
the deterministic commit-oracle argmax consumer recorded below.

Compiled abstract commit-oracle argmax consumer update:
`ETC-COMMIT-ORACLE-ARGMAX-CONSUMER` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`.  It
instantiates the compiled wrong-commit set-inclusion theorem with
`commitArm omega := oracle.choose (empMean omega)` and derives the required
argmax contract from an explicit
`forall scores a, scores a <= scores (oracle.choose scores)` assumption.  It
does not construct a concrete oracle, prove oracle measurability, add a
measure, prove concentration, add filtration, or prove final ETC regret.  The
next Extended Pro round selected the oracle-specialized pairwise-tail
probability wrapper recorded below.

Compiled oracle-specialized pairwise-tail probability wrapper update:
`ETC-COMMIT-ORACLE-PROB-WRAPPER` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`.  It specializes the
existing arbitrary commit-arm pairwise-tail consumer to
`commitArm omega := oracle.choose (empMean omega)` and derives the required
argmax contract from `hchoose_argmax`.  It does not require a probability
instance, event measurability, oracle measurability, concrete oracle
construction, actual concentration, filtration, or final ETC regret.  Ask
Extended Pro again before choosing the next post-oracle probability leaf.  The
next Extended Pro round selected the oracle-specialized filtered-sum wrapper
recorded below.

Compiled oracle-specialized filtered-sum probability wrapper update:
`ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`.  It
specializes the existing arbitrary commit-arm filtered-sum pairwise-tail
consumer to `commitArm omega := oracle.choose (empMean omega)` and derives the
required argmax contract from `hchoose_argmax`.  It does not require a
probability instance, event measurability, oracle measurability, concrete
oracle construction, actual concentration, filtration, or final ETC regret.
Use local two-agent review before choosing the next post-filtered-oracle
probability leaf.  The next Extended Pro round selected the
oracle-specialized if-zeroed nonbest wrapper recorded below.

Compiled oracle-specialized if-zeroed nonbest probability wrapper update:
`ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`.  It
specializes the existing arbitrary commit-arm if-zeroed nonbest pairwise-tail
consumer to `commitArm omega := oracle.choose (empMean omega)` and derives the
required argmax contract from `hchoose_argmax`.  It does not require a
probability instance, event measurability, oracle measurability, concrete
oracle construction, actual concentration, filtration, or final ETC regret.
Use local two-agent review before choosing the next post-oracle
probability/measurability leaf.  The next Extended Pro round selected the
oracle-selected wrong-event measurability wrapper recorded below.

Compiled oracle-selected wrong-event measurability wrapper update:
`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.measurableSet_commitOracle_ne_bestArm`.  It specializes the existing
arbitrary commit-arm wrong-event measurability canary to
`commitArm omega := oracle.choose (empMean omega)` under a direct
`Measurable (fun omega => oracle.choose (empMean omega))` contract.  It does
not require a measure, probability instance, concrete oracle construction,
proof of oracle choice measurability from empirical means, concentration,
filtration, or final ETC regret.  Use local two-agent review before choosing the
next post-oracle route or leaf.  The next Extended Pro round selected the
oracle-choice measurability route and identified the compiled bridge recorded
below.

Compiled oracle-choice measurability bridge update:
`ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`.  It uses
Mathlib's `measurable_of_countable` to prove that
`fun score : Fin K -> Rat => oracle.choose score` is measurable under explicit
`[Countable (Fin K -> Rat)]` and
`[MeasurableSingletonClass (Fin K -> Rat)]` contracts, then composes with
empirical-mean vector measurability.  It does not require concrete oracle
construction, argmax correctness, actual concentration, filtration, or final
ETC regret.  The next Extended Pro round selected the empirical-mean
coordinate-to-vector measurability bridge recorded below.

Compiled empirical-mean vector measurability bridge update:
`ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` is now available through
`BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.measurable_empMeanVector_of_forall_measurable`.  It uses Mathlib's
Pi measurable-space API `measurable_pi_lambda` to package coordinatewise
empirical-mean measurability into
`Measurable (fun omega => (empMean omega : Fin K -> Rat))` under the standard
Pi instance induced by `[MeasurableSpace Rat]`.  It does not assume an
arbitrary `[MeasurableSpace (Fin K -> Rat)]`, construct an oracle, prove
argmax correctness, add concentration, add filtration, or prove final ETC
regret.  The next Extended Pro round selected the coordinate-to-oracle-choice
composition wrapper recorded below.

Compiled coordinatewise oracle-choice measurability wrapper update:
`ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES` is now available
through `BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.measurable_commitOracle_choose_of_forall_measurable_empMean`.  It
composes the Pi-space empirical-mean vector bridge with the countable
score-vector oracle-choice bridge, producing
`Measurable (fun omega => oracle.choose (empMean omega))` directly from
coordinatewise empirical-mean measurability.  It does not assume an arbitrary
local `[MeasurableSpace (Fin K -> Rat)]`, construct an oracle, prove argmax
correctness, add probability, add concentration, add filtration, or prove
final ETC regret.  Use local two-agent review before choosing the next
coordinate-to-wrong-event measurability wrapper, concrete argmax route,
pairwise-tail import route, filtration layer, or final theorem.  The next
Extended Pro round selected the coordinate-to-wrong-event measurability
wrapper recorded below.

Compiled coordinatewise oracle wrong-event measurability wrapper update:
`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` is now available
through `BanditRLProof.Algorithms.ETCMeasurability` and declaration
`ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`.  It
composes the coordinatewise oracle-choice measurability wrapper with the
oracle-selected wrong-event measurability wrapper, producing measurability of
`{omega | oracle.choose (empMean omega) = model.bestArm -> False}` directly
from coordinatewise empirical-mean measurability.  It does not construct an
oracle, prove argmax correctness, add a probability measure, add
concentration, add filtration, or prove final ETC regret.

Compiled concrete argmax update: `ETC-COMMIT-ORACLE-CONCRETE-ARGMAX` is now
available through `BanditRLProof.Algorithms.ETCArgmaxOracle` and declarations
`ETC.argmaxCommitOracle`, `ETC.argmaxCommitOracle_choose_spec`, and
`ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_argmaxOracle`.  It
constructs a finite Rat argmax-backed commit oracle by scanning
`List.finRange K`, proves the maximality certificate, and feeds the existing
abstract wrong-event set-inclusion consumer.  It does not start pairwise-tail
import, add filtration, or prove a final theorem.  Use local two-agent review
before choosing the next narrow post-argmax leaf.

Compiled concrete filtered-sum probability wrapper update:
`ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL` is now available
through `BanditRLProof.Algorithms.ETCArgmaxOracle` and declaration
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`.  Its
exact statement specializes the filtered finite-sum abstract non-best
pairwise-tail consumer to `ETC.argmaxCommitOracle hK`:

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose (empMean omega) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

It consumes `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`
and discharges the abstract oracle argmax certificate with
`ETC.argmaxCommitOracle_choose_spec`.  It does not prove the abstract
`hpair_tail` hypothesis, import Hoeffding/sub-Gaussian concentration, add
filtration, or prove final ETC regret.  The local dual review recorded in
`reports/local_dual_review_after_concrete_argmax_decision_2026-06-30.md`
selected `ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD` as the next route decision; that
route card is now recorded in
`research-wiki/open-problems/etc-pairwise-tail-import-route-card.md`.  It is
theorem-card-only and should be split into a smaller import/contract leaf before
attempting actual concentration, filtration, or final ETC regret.

Compiled pairwise-tail contract surface update:
`ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` is now available through
`BanditRLProof.Algorithms.ETCPairwiseTailContract` and declarations
`ETC.PairwiseEmpMeanTailContract` and
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract`.
The contract packages exactly the non-best pairwise empirical-mean tail bound
for fixed-commit ETC empirical means:

```lean
structure ETC.PairwiseEmpMeanTailContract
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal) : Prop
```

The consumer theorem instantiates the concrete argmax filtered probability
wrapper with
`fun omega a => ETC.empMeanAtExploration spec commitArm (reward omega) a`.
It does not prove the contract, import any sub-Gaussian/Hoeffding theorem,
introduce filtration, or prove final ETC regret.  The next route should not be
a final concentration theorem.

Compiled empirical-mean comparison finite-sum update:
`ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` is now available through
`BanditRLProof.Algorithms.ETCEmpiricalMean` and declaration
`ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos`.
It states that, when `0 < spec.explorationPulls`, comparing two fixed-commit
ETC empirical means at the exploration horizon is equivalent to comparing the
corresponding fixed-horizon `sumRewards` numerators:

```lean
theorem ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a b : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    ETC.empMeanAtExploration spec commitArm reward b <=
      ETC.empMeanAtExploration spec commitArm reward a ↔
    sumRewards (ETC.actionWithCommit spec commitArm) reward b
        (spec.explorationPulls * K) <=
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
        (spec.explorationPulls * K)
```

It consumes the empirical-mean denominator rewrite and Mathlib's ordered-field
division lemma for a positive common denominator.  It does not produce centered
deviation variables, import any tail theorem, add probability, introduce
filtration, or prove final ETC regret.  The next narrow leaf should be a
concrete tail import/adapter such as `TAIL-SUBGAUSS-DIFF-SUM-IMPORT`.

Compiled independent sub-Gaussian finite-sum tail wrapper update:
`TAIL-SUBGAUSS-SUM` is now available through
`BanditRLProof.ConcentrationSubGaussian` and declaration
`Concentration.subGaussian_sum_tail_of_iIndepFun`.

```lean
theorem Concentration.subGaussian_sum_tail_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= s.sum (fun i => X i omega)} <=
      Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real)))
```

It is a thin wrapper around Mathlib
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`.  It does
not instantiate ETC rewards, prove pairwise reward-difference sub-Gaussian
contracts, add filtration, or prove final ETC regret.

Compiled ENNReal independent sub-Gaussian finite-sum tail wrapper update:
`TAIL-SUBGAUSS-DIFF-SUM-IMPORT` is now available through
`BanditRLProof.ConcentrationSubGaussian` and declaration
`Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun`.

```lean
theorem Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega | eps <= s.sum (fun i => X i omega)} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real))))
```

It composes the real-valued wrapper with `Measure.real`,
`measure_ne_top`, and `ENNReal.le_ofReal_iff_toReal_le`.  The summands remain
abstract; a later ETC leaf must instantiate them with centered
non-best-minus-best exploration reward differences and connect the event to
`ETC.PairwiseEmpMeanTailContract`.  Do not add filtration or final ETC regret
in this layer.

Compiled conditional sub-Gaussian finite-prefix tail wrapper update:
`TAIL-COND-SUBGAUSS` is now available through
`BanditRLProof.ConcentrationSubGaussian` and declarations
`Concentration.condSubGaussian_sum_tail_of_stronglyAdapted` and
`Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`.

```lean
theorem Concentration.condSubGaussian_sum_tail_of_stronglyAdapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : Filtration Nat mOmega}
    (h_adapted : StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= (Finset.range n).sum (fun i => Y i omega)} <=
      Real.exp (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real)))
```

The ENNReal declaration has the same hypotheses plus `[IsFiniteMeasure mu]`
and returns the event measure bounded by the same exponential RHS wrapped in
`ENNReal.ofReal`.  This imports Mathlib's Azuma-Hoeffding route for strongly
adapted conditionally sub-Gaussian processes.  It does not prove full policy
predictability, prove conditional MGF witnesses for ETC rewards, or discharge
the final adaptive ETC theorem.

Compiled history filtration update:
`FILTRATION-HISTORY` is now available through
`BanditRLProof.HistoryFiltration` and declaration
`History.historyFiltration`, with supporting declarations
`History.historyGenerators`, `History.historyGenerators_mono`,
`History.historyMeasurableSpace`, `History.historyMeasurableSpace_mono`,
`History.historyMeasurableSpace_le`, `History.historyFiltration_apply`,
`History.measurableSet_action_mem_historyFiltration`, and
`History.measurableSet_reward_mem_historyFiltration`.

```lean
def History.historyFiltration
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Filtration Nat mOmega
```

This is a singleton-event history canary generated from past action/reward
coordinate preimages.  It does not prove policy predictability, adapted reward
processes, conditional expectation identities, conditional MGF witnesses,
kernels, or final adaptive ETC regret.

Compiled adapted-coordinate update:
`ADAPTED-ACTION` is now available through
`BanditRLProof.HistoryFiltration` and declaration
`History.measurable_action_mem_historyFiltration_of_lt`, with companion
declaration `History.measurable_reward_mem_historyFiltration_of_lt`.

```lean
theorem History.measurable_action_mem_historyFiltration_of_lt
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    {i t : Nat} (hit : i < t) :
    @Measurable Omega Action
      (History.historyFiltration action reward haction hreward t)
      inferInstance
      (fun omega => action omega i)
```

The proof uses Mathlib `measurable_to_countable'` with source measurable space
set to the generated history filtration.  This proves countable/discrete past
coordinate measurability, not arbitrary policy predictability, conditional
reward laws, kernels, or conditional MGF witnesses.

Compiled conditional centered-diff witness update:
`ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT` is now available through
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and declarations
`ETC.CenteredDiffCondSubGaussianWitnesses` and
`ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`.

```lean
structure ETC.CenteredDiffCondSubGaussianWitnesses
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)

theorem ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (w : ETC.CenteredDiffCondSubGaussianWitnesses
      mu spec model commitArm reward tail) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail
```

The package fields are per-arm variance proxies `c`, filtrations,
`StronglyAdapted` centered-diff processes, zeroth `HasSubgaussianMGF`, later
`HasCondSubgaussianMGF`, and tail domination.  The consumer combines the
compiled centered-diff event inclusion with
`Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`.  It still
does not derive those witness fields from a concrete reward law, prove a
conditional expectation identity, or prove full policy predictability.

Compiled shifted-history adaptedness update:
`ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY` is now available through
`BanditRLProof.HistoryFiltration` and
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.  The declarations are
`History.historyFiltrationSucc`, `History.historyFiltrationSucc_apply`,
`ETC.measurable_centeredPairwiseRewardDiff_historyFiltrationSucc`, and
`ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc`.
This proves the fixed-commit centered pairwise reward-difference process is
`StronglyAdapted` to the generated history filtration shifted by one time step,
under timewise reward-coordinate measurability.  It does not prove
`HasCondSubgaussianMGF`, conditional mean-zero, arbitrary policy
predictability, or a final adaptive ETC theorem.

Compiled zero-summand conditional MGF update:
`ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS` is now available through
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.  The declarations are
`ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_action_miss`,
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss`, and
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss`.
They prove zero-variance MGF witnesses when the fixed `actionWithCommit` trace
at time `t` pulls neither the comparison arm nor `model.bestArm`, by reducing
the centered pairwise reward-difference summand to zero and using Mathlib
`fun_zero` lemmas.

Compiled sampled-arm conditional MGF transfer update:
`ETC-CENTERED-DIFF-COND-MGF-SAMPLED-TRANSFER` is now available through
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.  The declarations are
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm`,
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm`,
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm`,
and
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm`.
They transfer sampled centered-reward conditional MGF witnesses to the
fixed-commit centered pairwise reward-difference summand when
`actionWithCommit` pulls either the comparison arm or `model.bestArm`.

Compiled reward-level conditional witness contract update:
`ETC-CENTERED-REWARD-COND-SUBGAUSSIAN-WITNESS-CONTRACT` is now available through
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.  The declarations are
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_centeredReward`,
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_centeredReward`,
`ETC.CenteredRewardCondSubGaussianWitnesses`, and
`ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`.
They package sampled centered-reward conditional MGF witnesses, the zeroth
unconditional witness, reward-coordinate measurability, and tail domination,
then construct `ETC.CenteredDiffCondSubGaussianWitnesses`.  Concrete
reward-law/kernel conditional MGF, deterministic action-history/full-history
independence, arbitrary policy predictability, and final adaptive ETC remain
open.

Compiled conditional mean-zero source update:
`ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE` is now available through
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.  The declarations are
`ETC.centeredReward_condExp_eq_zero_of_indep`,
`ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep`, and
`ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep`.  They wrap
Mathlib `MeasureTheory.condExp_indep_eq`: if the centered reward coordinate
sigma-algebra is independent of the conditioning sigma-algebra and the centered
reward has integral zero, then its conditional expectation is zero.  The second
theorem specializes the target conditioning sigma-algebra to
`History.historyFiltrationSucc`; the third uses the `i + 1` versus filtration
level `i` shape required by the Mathlib conditional tail wrapper.  This still
does not prove full-history independence or conditional MGF witnesses.

Compiled reward-only past independence update:
`ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE` is now available through
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
`BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.  The declarations
are `ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward` and
`ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi`.  They prove that
reward-coordinate `iIndepFun` implies the centered reward at time `i + 1` is
independent of the reward-only past coordinate sigma-algebra generated by
`j <= i`, with an infinite-product specialization.  Deterministic action
generators and full `History.historyFiltrationSucc` independence remain open.

Compiled bounded-to-integrable source update:
`INT-REWARD-BOUNDED` /
`ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE` is now available through
`BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
`BanditRLProof.Algorithms.ETCBoundedRewardSource`.  The declarations are
`ETC.centeredReward_integrable_of_mem_Icc` and
`ETC.centeredReward_integrable_of_boundedRewardTraceSource`.  They wrap
Mathlib `MeasureTheory.Integrable.of_mem_Icc`: a.e. measurability plus an
a.s. interval bound gives raw reward integrability, and the source-contract
wrapper uses `BoundedRewardTraceSource.meas` and `.bound`.

Compiled centered-reward zero-integral source update:
`ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE` is now available through
`BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
`BanditRLProof.Algorithms.ETCBoundedRewardSource`.  The declarations are
`ETC.centeredReward_integral_eq_zero_of_integral_eq_mean`,
`ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean`, and
`ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean`.
They prove that exact raw mean plus raw reward integrability gives
`integral (reward - mean) = 0`, with bounded-Icc and action-matched
`BoundedRewardTraceSource` wrappers for the ETC exploration horizon.  This
still does not prove full-history product-law independence, and it does not produce
`HasCondSubgaussianMGF`.

Compiled sub-Gaussian pairwise-tail producer update:
`ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` is now available through
`BanditRLProof.Algorithms.ETCPairwiseSubGaussianTail` and declaration
`ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds`.

```lean
theorem ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    {Idx : Type v}
    (idx : Finset Idx)
    (X : Fin K -> Idx -> Omega -> Real)
    (c : Fin K -> Idx -> NNReal)
    (eps : Fin K -> Real)
    -- plus non-best-arm independence, sub-Gaussian, event-subset, and tail
    -- domination hypotheses
    :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail
```

The proof is only `mu.mono` composed with
`Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun` and the supplied
tail domination inequality.  It does not instantiate reward differences, add
filtration, or prove final ETC regret.

Compiled empirical-mean event-subset bridge update:
`ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT` is now available through
`BanditRLProof.Algorithms.ETCEmpiricalMean` and declaration
`ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp`.
It states that a pointwise implication from the fixed-horizon reward-sum
comparison
`sumRewards bestArm <= sumRewards a`
to an abstract real finite-sum tail event yields the corresponding set
inclusion from
`ETC.empMeanAtExploration a >= ETC.empMeanAtExploration bestArm`:

```lean
theorem ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    {Idx : Type v}
    (idx : Finset Idx)
    (X : Idx -> Omega -> Real)
    (eps : Real)
    (himp :
      forall omega : Omega,
        sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            model.bestArm (spec.explorationPulls * K) <=
          sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            a (spec.explorationPulls * K) ->
        eps <= idx.sum (fun i => X i omega)) :
    Set.Subset
      {omega : Omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm (reward omega)
            model.bestArm}
      {omega : Omega | eps <= idx.sum (fun i => X i omega)}
```

It consumes
`ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos`.
It imports `Mathlib.Data.Real.Basic` for the real-valued tail event, but does
not construct centered reward-difference summands, prove independence,
sub-Gaussianity, filtration, or final ETC regret.

Compiled centered reward-difference Finset bridge update:
`ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET` is now available through
`BanditRLProof.Algorithms.ETCSumRewardsDiff` and declarations
`ETC.centeredPairwiseRewardDiff`, `ETC.centeredPairwiseGapThreshold`,
`ETC.sumRewards_le_imp_centered_pairwise_sum_ge`, and
`ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`.
It proves the deterministic bridge from the fixed-horizon
`sumRewards bestArm <= sumRewards a` comparison to the concrete centered
pairwise finite-sum event over `Finset.range (spec.explorationPulls * K)`.
It consumes the equal exploration-horizon pull counts and the existing
empirical-mean event-subset adapter.  It does not prove independence,
sub-Gaussianity, filtration, or final ETC regret.

Compiled centered-diff sub-Gaussian producer specialization update:
`ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` is now available through
`BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail` and declaration
`ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds`.
It instantiates the abstract sub-Gaussian producer with
`idx := Finset.range (spec.explorationPulls * K)`,
`X := ETC.centeredPairwiseRewardDiff`, and
`eps := ETC.centeredPairwiseGapThreshold`, discharging threshold
nonnegativity from `FiniteBanditModel.mean_le_bestArm_mean`.  It still leaves
the concrete reward-law independence and `HasSubgaussianMGF` witnesses as
explicit hypotheses.  The later independence transfer leaf discharges the
deterministic-transform part from trace-level reward-coordinate independence;
remaining work is the stochastic source law and sub-Gaussian witnesses.  Do
not pivot directly to filtration or final ETC regret.

Compiled centered-diff sub-Gaussian witness contract update:
`ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` is now available through
`BanditRLProof.Algorithms.ETCCenteredDiffSubGaussianWitnesses` and
declarations `ETC.CenteredDiffSubGaussianWitnesses` and
`ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses`.
The structure packages the exact fields required by the centered-diff producer:
`c : Fin K -> Nat -> NNReal`, non-best-arm independence, per-exploration-index
`HasSubgaussianMGF` facts, and tail RHS domination.  The consumer theorem turns
that package into `ETC.PairwiseEmpMeanTailContract`.  It still does not prove
the package from a concrete reward distribution, kernel, full policy
predictability, or conditional expectation.  The next narrow leaf should
derive either concrete reward-law/kernel conditional MGF witnesses or extend
the compiled reward-only past independence bridge to deterministic
action-history/full `History.historyFiltrationSucc` before using the
shifted-history adaptedness field, zero-summand MGF source, sampled-arm MGF
transfer, reward-level conditional source contract, and conditional
sub-Gaussian wrapper.

Compiled centered-diff canonical sub-Gaussian tail update:
`ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` is now available through
`BanditRLProof.Algorithms.ETCCenteredDiffCanonicalTail` and declarations
`ETC.centeredDiffSubGaussianTail`,
`ETC.centeredDiffSubGaussianWitnesses_of_indep_subG`, and
`ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG`.  This leaf fixes
the exact exponential tail budget from the independent sub-Gaussian route and
therefore discharges the witness package's tail-domination field
definitionally.  It still requires concrete non-best-arm `iIndepFun` and
per-exploration-index `HasSubgaussianMGF` witnesses for
`ETC.centeredPairwiseRewardDiff`.  The next narrow leaf should prove or import
those witness fields from a concrete reward-law assumption, or intentionally
split a conditional sub-Gaussian route.

Compiled canonical wrong-commit probability update:
`ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` is now available through
`BanditRLProof.Algorithms.ETCWrongCommitCanonicalTail` and declaration
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail`.
This leaf composes the canonical centered-diff tail contract with the concrete
argmax-oracle filtered-sum probability consumer.  It still requires concrete
non-best-arm `iIndepFun` and per-exploration-index `HasSubgaussianMGF`
witnesses for `ETC.centeredPairwiseRewardDiff`; it does not close filtration,
conditional expectation, expected regret, or the final ETC theorem.

Compiled centered-diff independence transfer update:
`ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS` is now available through
`BanditRLProof.Algorithms.ETCCenteredDiffRewardIndependence` and declaration
`ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward`.  This leaf
transfers time-coordinate `iIndepFun` for the raw reward trace to
`ETC.centeredPairwiseRewardDiff` via `ProbabilityTheory.iIndepFun.comp`.  At
this layer, the remaining source obligation was trace-level reward
independence, and the leaf did not prove any `HasSubgaussianMGF` witness.
The later infinite-product bounded-reward source layer below discharges this
for a fixed product-coordinate reward source.

Compiled reward-coordinate sub-Gaussian wrong-commit update:
`ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS` and
`ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND` are now available through
`BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`, with declarations
`ETC.centeredPairwiseRewardDiffVarianceProxy`,
`ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward`, and
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`.
This layer reduces the wrong-commit probability theorem to raw reward trace
time-coordinate independence and per-arm/time centered reward
`HasSubgaussianMGF` assumptions.  It still does not construct the stochastic
reward trace law, filtration, conditional expectation, expected regret, or the
final ETC theorem.

Compiled bounded-reward sub-Gaussian source update:
`ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` and
`ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND` are now available through
`BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`, with declarations
`ETC.centeredRewardBoundVarianceProxy`,
`ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean`, and
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered`.
This layer uses Mathlib's bounded-variable Hoeffding lemma to turn a.e.
interval bounds plus an exact mean identity into per-time centered reward
`HasSubgaussianMGF` witnesses, then composes those witnesses with the compiled
reward-law wrong-commit route.  The original bounded wrong-commit theorem is a
strong all-arm wrapper: it assumes bounds and exact means for every arm/time
coordinate.

Compiled action-matched bounded-reward source update:
`ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND`,
`ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND`, and
`ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT` are now available through
`BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
`BanditRLProof.Algorithms.ETCBoundedRewardSource`, with declarations
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG`,
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered`,
`ETC.BoundedRewardTraceSource`,
`ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource`, and
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource`.
This is the practical fixed-commit ETC source boundary: bounds and exact mean
identities are keyed to `ETC.actionWithCommit spec commitArm t`, the arm
actually pulled at time `t`.  It still does not construct the stochastic reward
trace law or prove trace-level reward-coordinate independence, a.e.
boundedness, or exact mean identities from an environment/kernel.

Compiled infinite-product bounded-reward source update:
`ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
`ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE` are now available through
`BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`, with declarations
`ETC.boundedRewardTraceSource_infinitePi_actionWithCommit` and
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`.
This layer instantiates the action-matched source contract for
`Measure.infinitePi coordLaw`, using Mathlib's coordinate independence and
projection-map APIs.  It is still fixed-commit and product-coordinate only: it
does not introduce random commit-arm laws, adaptive filtrations, conditional
expectations, expected-regret assembly, or the final ETC theorem.

Compiled pointwise wrong-commit regret assembly update:
`ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE` is now available through
`BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly`, with declaration
`ETC.pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap`.
This layer turns an `Omega`-indexed commit selector into a deterministic
exploration-budget plus suffix-penalty bound, where the suffix penalty vanishes
on the best-arm branch and is charged by an explicit `badGapBound` only on the
wrong-commit branch.  It does not integrate that bound or connect it to the
compiled wrong-commit probability inequality.

Compiled lower-integral wrong-commit regret assembly update:
`ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY` is now available through
`BanditRLProof.Algorithms.ETCExpectedRegretAssembly`, with declaration
`ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob`.
This layer lifts the pointwise wrong-commit regret bridge to an
`ENNReal.ofReal` lower-integral bound using wrong-event measurability and an
abstract upper bound `pWrong` on the wrong-commit event probability.  It is not
a Bochner/Rat-valued expected-regret theorem.  This abstract leaf itself does
not instantiate the concrete argmax/infinitePi probability supplier; the
separate concrete leaf below now does.

Compiled concrete argmax/infinitePi lower-integral regret assembly update:
`ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY` is now available
through `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`, with
declaration
`ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean`.
This layer wires the finite `argmaxCommitOracle`, coordinate empirical-mean
measurability, and the compiled infinite-product bounded-reward wrong-commit
probability theorem into the abstract lower-integral regret assembly.  It is
still an `ENNReal.ofReal` surrogate, not a Bochner/Rat-valued expected-regret
theorem, and it remains fixed-product/fixed-exploration rather than adaptive.

Compiled sum-gap suffix adapter update:
`ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY` is now
available through `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`,
with declaration
`ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean`.
This wrapper removes the explicit `badGapBound` and `hbadGap` parameters from
the concrete argmax/infinitePi lower-integral theorem by using the finite sum
of all model gaps as a conservative upper bound on every non-best gap.  It uses
`FiniteBanditModel.gap_nonneg` and Mathlib `Finset.single_le_sum`.  It is
conservative and remains an `ENNReal.ofReal` surrogate.

Compiled max-gap suffix adapter update:
`ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY` is now
available through `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`,
with declaration
`ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean`.
This wrapper removes the explicit `badGapBound` and `hbadGap` parameters from
the concrete argmax/infinitePi lower-integral theorem by using
`FiniteBanditModel.maxGap` as the suffix gap bound.  The local contract is
discharged by `FiniteBanditModel.gap_le_maxGap`.  It is still an
`ENNReal.ofReal` surrogate, not Bochner/Rat-valued expected regret.

Compiled fixed product-coordinate wrapper update:
`ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER` is now available through
`BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`, with named
declarations `ETC.fixedProductArgmaxCommit`, `ETC.fixedProductArgmaxAction`,
`ETC.fixedProductMaxGapLintegralRegretBound`, and
`ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean`.
This is polish over the fixed product-coordinate max-gap lower-integral route:
it names the selected argmax action trace and RHS budget, but remains an
`ENNReal.ofReal` surrogate and does not add filtration or conditional
concentration.
