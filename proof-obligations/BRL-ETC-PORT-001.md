# Proof Obligations: BRL-ETC-PORT-001

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ETC-CORE` | verify exploration-arm finite selector | ABRL core | `BanditRLProof.Algorithms.ETC` | `LOCAL-LEAF-ALGORITHM-WRAPPERS`, `MLIB-FINTYPE-FIN` | finite selector value proof | finite action count, nonzero exploration horizon | project-local | reviewer | `ETC.exploreArm_val`, `ETC.exploreArm_eq_of_mod_eq` | check | compiled |
| `ETC-COUNT` | prove round-robin pull-count arithmetic | `ETC.exploreArm`, `PullCountDecomposition` | pull count recursion, finite-action count partition, Nat modulo lemmas | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | induction on time plus finite-cycle arithmetic, with `finset_sum_pullCount_eq_time` as the global count budget | finite actions, positive arm count | project-local compiled partition plus mathlib-candidate arithmetic leaves | lower Lean | `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`, `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`, `finset_sum_pullCount_eq_time` | build | compiled |
| `ETC-COMMIT` | define empirical-mean argmax commit | finite history | finite argmax contract, reward sums | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS` | expose commit oracle before probability proof | finite arms, nonempty candidate set, denominator positivity | project-local wrapper | middle/lower | `ETC.argmaxCommitOracle`, `ETC.argmaxCommitOracle_choose_spec`, `ETC.explorationArgmaxCommit` | build | compiled |
| `ETC-CONC` | wrong-commit probability bound | sub-Gaussian cards, `MeasureFoundation`, `MeasurableSums`, `MeasurableLocalQuantities`, `MeasurableRegret`, `MeasurablePullCount`, `MeasurablePullCountCast`, `ExpectationFoundation`, `ExpectationSums`, `ExpectationPullCount`, `ExpectationWeightedPullCount` | concentration theorem cards plus measurable action-event/indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities | `LOCAL-LEAF-MEASURE-FOUNDATION`, `LOCAL-LEAF-MEASURABLE-SUMS`, `LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES`, `LOCAL-LEAF-MEASURABLE-REGRET`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST`, `LOCAL-LEAF-EXPECTATION-FOUNDATION`, `LOCAL-LEAF-EXPECTATION-SUMS`, `LOCAL-LEAF-EXPECTATION-PULLCOUNT`, `LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL` | reduce wrong commit to pairwise empirical-mean tail events after event, pull-indicator, selected-reward indicator, finite-sum, `sumRewards`, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities are explicit | measurability, lower-integral event measures, lower-integral finite sums, lower-integral pull counts, lower-integral weighted pull counts, integrability, independence/sub-Gaussian contract | theorem-card-only until imported or ported, with local measurable-event, indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count leaves compiled | retrieval | `measurableSet_actionTrace_eval_eq`, `measurable_actionTrace_eval_eq_indicator_const`, `measurable_actionTrace_eval_eq_indicator_reward`, `measurable_finset_sum_indicator_reward`, `measurable_sumRewards`, `measurable_pseudoRegret`, `measurable_pullCount`, `measurable_natCast_pullCount`, `lintegral_actionTrace_eval_eq_indicator_one`, `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`, `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`, `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` plus TBD tail declarations | memory/build | obligation |
| `REAL-MEAN-REGRET-PULLCOUNT` | exact-route Real scalar regret and pull-count expectation decomposition | Mathlib finite sums and Bochner integration | `BanditRLProof.RealMeanRegretPullCount`, `pullCount_eq_finset_filter_card`, `Finset.sum_fiberwise'`, `IntegrabilitySums.integrable_univ_sum`, `ExpectationBochnerSums.integral_univ_sum` | `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, `LML-BANDIT-REGRET-PULLCOUNT`, `LML-ETC-REGRET` | rewrite `n * iSup mean - sum mean(action)` as a time-indexed gap sum, group by arm fibers, then exchange the finite arm sum and Bochner integral | measurable sample space, arbitrary measure, `mean : Fin K -> Real`, per-arm Real-cast pull-count integrability; no kernel, probability, reward law, concentration, or tie premise | project-local over Mathlib; LML remains card-only | lower Lean | `realMeanRegret_eq_sum_gap_mul_pullCount`; `integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount` | build | compiled |
| `REAL-KERNEL-REGRET-PULLCOUNT` | stationary Real arm-kernel gap/regret and expected pull-count decomposition | Real mean leaf | `Mathlib.Probability.Kernel.Integral`, `BanditRLProof.RealKernelRegretPullCount` | `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `LOCAL-LEAF-REAL-MEAN-REGRET-PULLCOUNT`, `LML-BANDIT-REGRET-PULLCOUNT` | define kernel mean by the identity integral, specialize Real mean gap/regret, prove gap nonnegative by `le_ciSup`, and reuse deterministic/Bochner pull-count decompositions | `nu : Kernel (Fin K) Real`, arbitrary action-space measure, per-arm Real-cast pull-count integrability; only gap nonnegativity needs `Nonempty (Fin K)`; no Markov/probability/law/concentration/tie assumptions | project-local over Mathlib; LML remains card-only | lower Lean | `realKernelGap_nonneg`; `realKernelRegret_eq_sum_gap_mul_pullCount`; `integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount` | build | compiled |
| `REAL-ETC-EXPECTED-PULLCOUNT` | LML-shaped Real ETC per-arm expected pull count from a commit-fiber probability bound | deterministic ETC count and scalar pull-count measurability | `BanditRLProof.Algorithms.ETCExpectedPullCount`, Bochner indicator/set integral | `MLIB-MEASURE-INTEGRAL`, `LOCAL-LEAF-ETC-TRACE-COUNT`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST`, `LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT`, `LML-ETC-REGRET` | prove integrability, integrate the exact suffix count, normalize to `n - K*m`, and consume `mu.real {commit=a} <= p` | probability measure, measurable commit selector, `K*m <= n`; no reward law, empirical mean, MGF, concentration, best-arm, or tie premise | project-local over Mathlib; LML remains card-only | lower Lean | `ETC.integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_remaining_mul_commit_prob`; `ETC.integral_real_pullCount_actionWithCommit_choice_le_exploration_add_remaining_mul_of_commit_prob_le` | build | compiled |
| `ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT` | exact canonical per-arm commit-fiber exponential and expected pull-count bounds | canonical direct-MGF Rat arm-law fiber theorem and Real expected-count consumer | `BanditRLProof.Algorithms.ETCExactSubGaussianTail`, masked pairwise proxy, exact exploration counts, `Finset.filter`, `FieldSimp`, `Ring` | `LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-CANONICAL-PER-ARM-BOCHNER-REGRET`, `LOCAL-LEAF-ETC-REAL-EXPECTED-PULLCOUNT`, `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, `LML-ETC-REGRET` | evaluate proxy sum as `2*m*sigma2`, rewrite threshold as `m*gap`, normalize the exponent with a zero-proxy branch, then compose fiber concentration with expected count | `0<m`, `K*m<=n`, non-best arm, Rat probability arm laws, exact cast means, centered Real MGFs with common NNReal proxy, measurable context; canonical context-independent kernel internally derives successor conditional MGFs and transports them through exploration-prefix equality to `historyFiltrationSucc`; one-sided fixed-horizon single-arm event, not arbitrary adaptive kernels | project-local over Mathlib; LML remains card-only | lower Lean | `ETC.real_measure_explorationArgmaxCommit_eq_arm_le_exp_neg_explorationPulls_mul_gap_sq_div_four_mul_of_armLaws`; `ETC.integral_real_pullCount_explorationArgmaxAction_le_exploration_add_remaining_mul_exp_of_armLaws` | build | compiled |
| `ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET` | exact full finite-sum Real-kernel regret bound for canonical Rat arm laws | exact per-arm count leaf and Real kernel regret decomposition | `ETCRatArmLawRealKernel`, `Measure.map`, `Kernel.ofFunOfCountable`, `integral_map`, conditional `iSup`, finite-sum monotonicity | `LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT`, `LOCAL-LEAF-ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT`, `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `LML-ETC-REGRET` | construct cast-pushforward Markov kernel, identify means/gaps, apply kernel regret decomposition, zero best-arm term, insert non-best exact count bounds | positive exploration pulls, horizon fit, Rat probability laws, exact cast means, centered common-proxy MGFs, measurable canonical context; pushforward Real kernel over canonical Rat trajectory only | project-local over Mathlib; LML remains card-only | lower Lean | `ETC.realKernelGap_ratArmLawRealKernel_eq_modelGap`; `ETC.integral_realKernelRegret_explorationArgmaxAction_le_exact_sum_of_armLaws` | build | compiled |
| `ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT` | native Real exploration empirical means, measurable finite argmax action, and exact/upper expected pull-count consumer | deterministic ETC exploration counts and generic expected-count integration | `ETCRealEmpiricalMean`, measurable finite sums, finite indicator sums, strict-comparison events, measurable `ite`, `List.foldl` | `LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES`, `LOCAL-LEAF-ETC-TRACE-COUNT`, `LOCAL-LEAF-ETC-REAL-EXPECTED-PULLCOUNT`, `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, `LML-ETC-REGRET` | define Real means, prove fold maximality, prove selected-coordinate and fold measurability directly, instantiate count identity | timewise measurable Real rewards; probability measure and horizon fit for count endpoint; no reward-law/MGF/concentration/environment premise | project-local over Mathlib; LML remains card-only | lower Lean | `ETC.measurable_realExplorationArgmaxCommit`; `ETC.integral_real_pullCount_realExplorationArgmaxAction_eq_exploration_add_remaining_mul_commit_prob` | build | compiled |
| `ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET` | exact native Real finite-sum kernel-regret bound for an external reward/action process from finite-prefix or scheduled conditional laws | native Real `infinitePi` exact theorem and generic reward-prefix conditional-law uniqueness | `ETCRealPrefixLawTransport`, finite prefix extraction/zero extension, measurable prefix regret, `Measure.map_map`, `integral_map`, constant `Kernel.trajMeasure`, infinite-product projective-limit uniqueness | `LOCAL-LEAF-ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET`, `LOCAL-LEAF-ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT`, `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-SUBGAUSSIAN`, `LML-ETC-REGRET` | factor local ETC regret through `Fin (m*K)`, transport its integral by prefix-law equality, identify constant trajMeasure with `infinitePi`, derive prefix equality from zeroth map and successor `condDistrib`, and replace an external action by horizon-restricted a.e. equality | arbitrary measurable probability space, coordinate-measurable Real rewards, Markov Real arm kernel, common centered sub-Gaussian proxy, `0<m`, `K*m<=n`, scheduled zeroth/successor laws through exploration, and external/local action equality only for `t<n`; no StandardBorel sample space, action measurability, full law, or infinite action equality | project-local over Mathlib; exact LML source remains card-only | lower Lean | `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_prefixLaw_eq_infinitePi`; `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_initial_map_eq_condDistrib` | build | compiled |
| `ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET` | exact native Real finite-sum regret from action-selected initial and full pair-history successor feedback laws | native Real prefix-law theorem and generic selected-kernel/coarsening APIs | `ETCRealSourceAdapter`, `condDistrib_ae_eq_const_of_ae_eq_selected`, `map_eq_of_condDistrib_ae_eq_const`, `condDistrib_ae_eq_const_of_comp`, `contextIndependentOfActionLaws`, pair-history reward projection | `LOCAL-LEAF-ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET`, `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `LML-ETC-REGRET` | freeze selected feedback kernels with exploration actions, extract zeroth marginal, coarsen successor full histories to reward prefixes, consume exact theorem | arbitrary measurable probability space, measurable action/reward coordinates, Markov Real kernel, common centered MGF proxy, positive exploration, horizon fit, exploration action a.e. identities, initial/successor selected feedback laws, and local ETC horizon action equality; no sample-space standard-Borel/full law/independence/infinite action equality | project-local over Mathlib; pinned LML source remains card-only | lower Lean | `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib` | build | compiled |
| `ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET` | exact native Real finite-sum regret from selected feedback laws plus upstream-shaped exploration/commit/persistence behavior | source adapter and native Real argmax | `ETCRealArgmaxTie`, Mathlib `List.argmax`, `index_of_argmax`, `idxOf_finRange`, `Nat.find`, encode injectivity, `ETCRealSourceAdapter` | `LOCAL-LEAF-ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET`, `MLIB-FINSET-SUMS`, `LML-ETC-REGRET` | prove fold equals first list argmax, derive least-encode semantics, identify the Nat.find selector, assemble exploration/commit/persistence into action equality, consume exact source theorem | source-adapter contracts plus round-robin action laws, least-encoded local empirical-mean commit, and persistence; no caller-supplied horizon action equality or stronger probability laws | project-local over Mathlib; pinned LML source remains card-only | lower Lean | `ETC.realLeastEncodedArgmax_eq_realArgmaxCommit`; `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_leastEncodedCommit_persist` | build | compiled |
| `ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET` | exact native Real finite-sum regret from a source-shaped finite-history least-encoded commit law | least-encoded action/source endpoint and finite pair history | `ETCRealHistoryScore`, `Finset.Iic`/`range`, count/sum wrappers, `ae_all_iff` | `LOCAL-LEAF-ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET`, `MLIB-FINSET-SUMS`, `LML-ETC-REGRET` | identify inclusive history count/sum/mean with trace quantities at `n+1`, specialize `K*m-1`, rewrite exploration scores a.e., consume exact theorem | prior source contracts plus positive exploration, history-score commit, and persistence; no local-score or preassembled action-equality premise | project-local over Mathlib; pinned LML definitions remain source evidence | lower Lean | `ETC.realHistoryEmpMean_exploration_eq_realEmpMeanAtExploration`; exact `_of_historyLeastEncodedCommit_persist` endpoint | build | compiled |
| `ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET` | exact native Real finite-sum regret from a faithful local bundle of the LML stationary ETC sequence fields | history-score source endpoint | `ETCRealLMLCompat`, `Measure`, `Kernel`, `condDistrib`, finite pair histories, least-encoded argmax, context-independent action laws | `LOCAL-LEAF-ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET`, `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `LML-ETC-REGRET` | bundle the precise measurability, action-phase, and stationary feedback-law consequences; project fields into the compiled history-score theorem | probability measure, Markov Real arm kernel, common centered MGF proxy, positive exploration, horizon fit; no standard-Borel/full-law/independence/preassembled action equality | project-local faithful compatibility structure; actual LML remains card-only | lower Lean | `ETC.RealStationaryETCSequence`; `ETC.regret_le_of_realStationaryETCSequence` | build | compiled |
| `ETC-FINAL` | imported theorem over the actual upstream `Bandits.ETC.regret_le` symbols | all above | compiled local faithful field theorem plus a common toolchain/dependency | `LOCAL-LEAF-ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET`, `LML-ETC-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | make a task-level toolchain decision, import LML, and prove the imported source contract instantiates the local bundle | exact upstream symbols/toolchain; the mathematical concentration, law, score, tie, action, and field-consumer route is closed | blocked only on cross-toolchain imported-symbol identity | lower Lean | local compatibility theorem compiled; actual imported LML declaration TBD | build | partial |

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

## Current Route State: Canonical Fixed-Product Endpoint

`ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET` is compiled locally as
the theorem-level fixed-product Real endpoint:

```lean
theorem ETC.integral_real_pseudoRegret_explorationArgmaxAction_le_explorationMaxGapIntegralRegretBoundReal_of_infinitePi_bounded_exploreMean
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`,
  `ETC.actionWithCommit_eq_exploreArm_of_lt`,
  `ETC.fixedProductArgmaxAction`, and the fixed-product max-gap Bochner
  theorem.
- Proof route: instantiate the compiled fixed-product max-gap theorem at
  `baseCommitArm := model.bestArm`; transport each coordinate bound and mean
  identity through the exploration-phase equality; expose named canonical
  commit/action/RHS definitions with no public base commit arm.
- Regularity contracts: probability coordinate laws, fixed `spec` and `model`,
  suffix `r`, `lo`/`hi` indexed by `ETC.exploreArm`, positive exploration pulls,
  and exact exploration-coordinate mean identities.
- Retrieval evidence: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `SCN-STOCHASTIC-FINITE`,
  `LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-MAXGAP-ADAPTER`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-INDEPENDENCE`, and
  `MLIB-PROBABILITY-SUBGAUSSIAN`.  `WEAPON-TAIL-INEQUALITIES` is
  inspiration-only.
- Status: `leanCompiled`, with a public `Tests.Basic` canary.
- Failure policy: do not identify the product-coordinate theorem with
  `Bandits.ETC.regret_le`.  The remaining blocker is an action-dependent
  adaptive environment law and its conditional reward-law/predictability
  transport, not an exploration-count or denominator fact.

## Current Supporting Leaf: Exploration Prefix Congruence

`ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE` is compiled locally through
`BanditRLProof.Algorithms.ETCEmpiricalMean`:

```lean
theorem ETC.empMeanAtExploration_eq_of_eq_on_prefix
    (spec : ETC.Spec K) (commitArm : Fin K)
    (reward0 reward1 : RewardTrace Rat)
    (hprefix : forall t, t < spec.explorationPulls * K -> reward0 t = reward1 t)
    (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward0 a =
      ETC.empMeanAtExploration spec commitArm reward1 a
```

- Local APIs/imports: `ETC.empMeanAtExploration`,
  `sumRewards_eq_finset_filter_sum`, `Finset.sum_congr`, and
  `BanditRLProof.MathlibWrappers`.
- Proof route: unfold both finite reward sums, use the range-filter index to
  discharge every coordinate with `hprefix`, then rewrite the empirical means.
- Regularity contracts: only finite action type and coordinate equality on the
  half-open exploration horizon. No positivity, probability, measurability,
  integrability, filtration, or conditional-expectation hypothesis is used.
- Retrieval evidence: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `SCN-STOCHASTIC-FINITE`, `MLIB-FINSET-SUMS`, and
  `LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS`; `WEAPON-TAIL-INEQUALITIES` is
  inspiration-only.
- Status: `leanCompiled`, with an external `Tests.Basic` canary.
- Failure policy: a later history-completion proof must establish equality at
  all coordinates below `spec.explorationPulls * K` before applying this
  theorem. Do not use it to equate an arbitrary finite history to a full trace
  outside the observed horizon, and do not claim generated-policy alignment,
  an adaptive environment law, or `Bandits.ETC.regret_le` from this lemma.

## Current Supporting Leaf: Finite-History Score Reconstruction

`ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION` is compiled locally through
`BanditRLProof.HistoryFiltration` and
`BanditRLProof.Algorithms.ETCEmpiricalMean`:

```lean
def History.completeRewardTrace

theorem ETC.empMeanAtExploration_completeRewardTrace_eq_of_explorationHorizon_le
    (horizon_le : spec.explorationPulls * K <= t + 1) :
    ETC.empMeanAtExploration spec commitArm
      (History.completeRewardTrace t
        (History.finiteRewardHistoryOfTrace reward t) 0) a =
      ETC.empMeanAtExploration spec commitArm reward a
```

- Local APIs/imports: `History.finiteRewardHistoryOfTrace`,
  `History.completeRewardTrace`,
  `History.completeRewardTrace_finiteRewardHistoryOfTrace_apply_of_le`, and
  `ETC.empMeanAtExploration_eq_of_eq_on_prefix`.
- Proof route: each completed coordinate `s <= t` reduces definitionally to
  the original trace; `s < explorationPulls * K <= t + 1` yields `s <= t`, so
  the prior finite-prefix congruence theorem closes the score equality.
- Regularity contracts: a finite history state time `t` and the explicit
  horizon inclusion `spec.explorationPulls * K <= t + 1`. No positivity,
  probability, measurability, integrability, filtration, or conditional law is
  required.
- Retrieval evidence: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `SCN-STOCHASTIC-FINITE`, `MLIB-FINSET-SUMS`,
  `LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS`, and
  `LOCAL-LEAF-ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE`.
- Status: `leanCompiled`, with external `Tests.Basic` canaries for both the
  coordinate restoration and the ETC score wrapper.
- Failure policy: the zero completion is only an implementation device. Do not
  use it before the history contains the full exploration horizon, and do not
  infer an argmax action equality, policy measurability, adaptive environment
  law, or final regret theorem from this score reconstruction alone.

## Current Supporting Leaf: Generated Finite-History Policy Alignment

`ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT` is compiled locally through
`BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy`:

```lean
noncomputable def ETC.explorationArgmaxHistoryPolicy
noncomputable def ETC.explorationArgmaxGeneratedAction

theorem ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    ETC.explorationArgmaxGeneratedAction spec model =
      ETC.explorationArgmaxAction spec model
```

- Local APIs/imports: `History.completeRewardTrace`,
  `ETC.measurable_empMeanAtExploration_coordinates`,
  `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean`,
  `Policy.generatedActionTraceSucc`, and
  `ConditionalExpectationReward.generatedActionFromRewardHistory`.
- Proof route: the time-zero default is `ETC.exploreArm spec 0` and uses
  positive exploration pulls; successor actions explore when `t + 1 < m * K`.
  Otherwise the completion score theorem produces equality of the entire score
  vector, which rewrites the deterministic argmax choice.
- Regularity contracts: `0 < spec.explorationPulls`; Pi-space reward-coordinate
  measurability and finite score-vector argmax measurability discharge the
  `Policy.MeasurablePolicy` field. No probability measure, reward kernel,
  conditional expectation, concentration, or integrability contract is used.
- Retrieval evidence: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `SCN-STOCHASTIC-FINITE`, `LOCAL-LEAF-POLICY-MEASURABILITY`,
  `LOCAL-LEAF-ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION`,
  `MLIB-FINSET-SUMS`, and `MLIB-MEASURE-INTEGRAL`.
- Status: `leanCompiled`, with public `Tests.Basic` canaries for state
  measurability and function-level action equality.
- Failure policy: do not identify action equality with an adaptive environment
  model. The remaining transport must prove the action-dependent selected
  reward law for this generated trace, then feed it into the existing
  conditional-expectation/conditional-MGF consumers.

## Current Supporting Leaf: Canonical Generated ETC Trajectory Law

`ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW` is compiled locally
through `BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy`:

```lean
noncomputable def
  ETC.explorationArgmaxGeneratedActionPartialTrajectoryPairLawSource_trajMeasure
```

- Lean-facing statement: under an initial probability measure, a
  `RewardKernel.MarkovRewardKernel (Context × Fin K) Rat`, and measurable
  history context, the canonical `trajMeasure` packages
  `GeneratedActionPartialTrajectoryPairLawSource` for the finite-history ETC
  policy, its completed reward state, and identity reward trace.
- Local APIs/imports:
  `RewardKernel.historyStepKernelFamily`,
  `ConditionalExpectationReward.historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_trajMeasure`,
  `ETC.explorationArgmaxHistoryPolicy`, and
  `ETC.measurable_explorationArgmaxHistoryState`.
- Proof route: instantiate the existing canonical generated-action `trajMeasure`
  source constructor at the ETC policy/state. The earlier action-equality
  theorem identifies its generated trace with `ETC.explorationArgmaxAction`
  when exploration pulls are positive.
- Regularity contracts: initial probability measure, Markov reward kernel,
  measurable context extractor, finite/countable action; no fixed-product
  coordinate independence, finite-bandit mean identity, concentration, or
  integrability assumption.
- Retrieval evidence: `MLIB-PROBABILITY-KERNEL`,
  `MLIB-CONDITIONAL-EXPECTATION`, `LOCAL-LEAF-POLICY-MEASURABILITY`, and
  `LOCAL-LEAF-ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT`.
- Status: `leanCompiled`, with an external `Tests.Basic` source-instantiation
  canary.
- Failure policy: this proves the canonical kernel trajectory law only. Do not
  identify it with the fixed product-coordinate distribution or an arbitrary
  adaptive environment; those transport/identification obligations remain the
  principal blocker to the LML-compatible theorem.

## Current Supporting Leaf: Model-Mean Conditional MGF On Canonical ETC Trajectory

`ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN` is compiled
locally through `BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy`:

```lean
theorem
  ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure
```

- Lean-facing statement: the successor reward under the canonical kernel
  trajectory, minus `model.mean` of the arm chosen by the finite-history ETC
  policy, has `HasCondSubgaussianMGF` at history time `i` with requested proxy
  `c`.
- Local APIs/imports: canonical generated `partialTraj` route,
  `RewardKernel.CenteredRewardKernelLaw`,
  `ConditionalExpectationReward.historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure`,
  and finite score-vector policy measurability.
- Proof route: instantiate the generic canonical trajectory MGF theorem with
  `mean := fun _ arm => model.mean arm`; measurability follows from the finite
  arm map, and the remaining user-facing condition is the selected finite
  history variance ceiling.
- Regularity contracts: initial probability measure, Markov reward kernel,
  measurable context, centered kernel law, and selected-history variance
  ceiling. No coordinate independence, product-law identification, boundedness,
  tail-sum theorem, or regret decomposition is assumed.
- Retrieval evidence: `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-KERNEL`, and
  `LOCAL-LEAF-ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW`.
- Status: `leanCompiled`, with a public `Tests.Basic` instantiation canary.
- Failure policy: do not infer a variance ceiling, a concrete centered
  finite-bandit kernel law, product-coordinate independence, or an
  expected-regret tail bound.
  These are separate model/transport/concentration obligations.

## Current Supporting Leaf: Finite-Arm Laws To Markov Reward Kernel

`ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL` is compiled through
`BanditRLProof.RewardKernel`:

```lean
def RewardKernel.contextIndependentOfActionLaws
theorem RewardKernel.selectedMeasure_contextIndependentOfActionLaws
```

- Lean-facing statement: an action-indexed family of probability measures
  defines a `MarkovRewardKernel (Context × Action) Reward`, independent of
  Context, whose selected measure at `(context, action)` is `actionLaw action`.
- Local APIs/imports: `Mathlib.Probability.Kernel.Basic`,
  `Mathlib.Probability.Kernel.Composition.MapComap`,
  `ProbabilityTheory.Kernel.ofFunOfCountable`, `Kernel.comap`, and
  `RewardKernel.selectedMeasure`.
- Proof route: build the measurable kernel on the countable action space, pull
  it back along measurable `Prod.snd`, and construct `IsMarkovKernel` from the
  per-action probability witnesses. Selected-measure equality is definitional.
- Regularity contracts: measurable Context/Action/Reward spaces,
  `[Countable Action]`, `[MeasurableSingletonClass Action]`, and
  `forall action, IsProbabilityMeasure (actionLaw action)`. `Fin K` satisfies
  the countability part directly.
- Retrieval evidence: `MLIB-PROBABILITY-KERNEL`,
  `ProbabilityTheory.Kernel.ofFunOfCountable`, and
  `ProbabilityTheory.Kernel.comap`; no theorem-card proof is used.
- Status: `leanCompiled`, with a `Fin K` public `Tests.Basic` canary.
- Failure policy: do not infer model-mean identities, bounded support,
  centered sub-Gaussian laws, variance proxies, trajectory equality, or regret.
  The bounded centered-law route is compiled immediately below; unbounded or
  arm-specific-proxy laws and all trajectory transports remain separate.

## Current Supporting Leaf: Bounded Arm Laws To Canonical Conditional MGF

`ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF` is compiled through
`BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
noncomputable def ETC.finiteArmBoundedCenteredRewardKernelLaw
theorem ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_boundedArmLaws
```

- Lean-facing statement: per-arm probability laws with a common a.s. interval
  `[lo, hi]`, a.e. measurable Rat-to-Real reward casts, and raw integrals equal
  to `model.mean arm` construct the context-independent
  `CenteredRewardKernelLaw`. The same inputs directly yield the successor
  centered reward `HasCondSubgaussianMGF` under the canonical generated-history
  ETC trajectory at `Concentration.intervalVarianceProxy lo hi`.
- Local APIs/imports: `BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy`,
  `BanditRLProof.ConcentrationSubGaussian`,
  `RewardKernel.contextIndependentOfActionLaws`,
  `RewardKernel.selectedMeasure_contextIndependentOfActionLaws`,
  `MeasureTheory.Integrable.of_mem_Icc`, `MeasureTheory.integral_sub`, and
  `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`.
- Proof route: derive raw and centered integrability from the interval bound,
  prove the centered integral is zero from the exact arm mean, reuse the
  bounded Hoeffding MGF wrapper, package all three fields into the centered
  kernel law, then invoke the canonical ETC trajectory MGF theorem. The common
  interval makes the variance proxy constant, so its selected-history ceiling
  is discharged by `le_rfl`.
- Regularity contracts: per-arm probability measures, common a.s. interval,
  Rat-to-Real a.e. measurability, exact model means, initial probability
  measure, measurable history context, finite actions. No independence or
  fixed-product identification is assumed.
- Concentration ledger: random variable is successor reward minus selected
  `model.mean`; filtration is generated finite action/reward history; mean is
  conditionally zero via the centered kernel law; proxy is the common
  Hoeffding interval proxy; this leaf proves an MGF witness only, not a tail
  event, union bound, or uniform-in-time statement.
- Retrieval evidence: `MLIB-PROBABILITY-KERNEL`,
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-MEASURE-INTEGRAL`,
  `TXT-LATTIMORE-SZEPESVARI-2020`, and
  `WEAPON-TAIL-INEQUALITIES` as inspiration-only.
- Status: `leanCompiled`, with public builder/consumer canaries in
  `Tests.Basic`.
- Failure policy: do not identify the canonical `trajMeasure` with the fixed
  product-coordinate or arbitrary adaptive environment, and do not infer a
  time-zero MGF from arbitrary `mu0`, conditional sum tail, wrong-commit
  probability, or final regret theorem. The next concentration bridge must
  align `mu0` with the initial selected arm (or assume its centered MGF), then
  combine that zeroth witness with successor conditional witnesses.

## Current Supporting Leaf: Full Canonical Centered-Reward Sum Tail

`ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL` is compiled through
`BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
theorem RewardKernel.trajMeasure_map_eval_zero
theorem ETC.explorationArgmaxHistory_centeredRewardProcess_sum_tail_ennreal_of_boundedArmLaws
```

- Lean-facing statement: initialize the canonical trajectory with
  `armLaw (ETC.exploreArm spec 0)`. For the process whose time-zero term is the
  actual reward centered at that arm mean and whose successor terms are centered
  at the arm selected by the finite-history ETC policy, the measure of
  `eps <= sum (Finset.range n) Y` is bounded by the Mathlib Azuma-Hoeffding
  exponential RHS at the sum of the common interval proxies.
- Local APIs/imports: `Kernel.trajMeasure`, `Kernel.traj_map_frestrictLe`,
  `Kernel.partialTraj_self`, `Kernel.id_map`,
  `Measure.deterministic_comp_eq_map`, `HasSubgaussianMGF.of_map`,
  `generatedActionFromRewardHistory_centeredRewardSuccProcess_stronglyAdapted`,
  the bounded-arm successor conditional-MGF theorem, and
  `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`.
- Proof route: prove the zeroth trajectory marginal is the initial measure;
  transport the bounded arm MGF to coordinate zero; reuse the existing
  successor process's StronglyAdapted proof, replacing only its zero branch by
  the measurable actual centered reward; supply successor conditional MGF
  witnesses; invoke Mathlib's finite-sum tail theorem.
- Regularity contracts: finite arm probability laws, common a.s. interval,
  Rat-to-Real a.e. measurability, exact model means, measurable history context,
  and nonnegative `eps`. The initial law is not arbitrary: it is exactly the
  law of the time-zero exploration arm.
- Concentration ledger: process is the selected centered reward at every time;
  filtration is `History.historyFiltrationSucc`; time-zero witness is
  unconditional and successors are conditional; proxy is the common Hoeffding
  proxy; event is one-sided and finite-horizon, not two-sided, uniform-in-time,
  or union-bounded.
- Retrieval evidence: `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-MARTINGALE-STOCHASTIC`, `MLIB-PROBABILITY-KERNEL`,
  `TXT-LATTIMORE-SZEPESVARI-2020`, and `WEAPON-TAIL-INEQUALITIES`
  inspiration-only. `RewardKernel.trajMeasure_map_eval_zero` is recorded as a
  Mathlib candidate.
- Status: `leanCompiled`, with an external `Tests.Basic` canary and no
  theorem-card substitution.
- Failure policy: this is the tail of the total selected centered reward sum.
  ETC wrong-commit compares arm-specific empirical means, so do not treat this
  as the pairwise tail or final wrong-commit probability. The downstream
  canonical bounded-arm pairwise leaf below now connects the masked centered
  process to `ETC.empMeanAtExploration`; reuse that endpoint. Environment-law
  transport and regret remain separate afterward.

## Current Supporting Leaf: Canonical Bounded-Arm Pairwise Wrong Commit

`ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT` is compiled through
`BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
theorem ProbabilityTheory.HasCondSubgaussianMGF.of_measurableSpace_eq
theorem History.historyFiltrationSucc_eq_of_action_eq_on_prefix
theorem ETC.explorationArgmaxGeneratedAction_eq_actionWithCommit_of_lt
noncomputable def
  ETC.explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_boundedArmLaws
theorem ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_boundedArmLaws
theorem ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws
```

- Lean-facing endpoint: under the canonical reward-kernel `trajMeasure`
  initialized by `armLaw (ETC.exploreArm spec 0)`, the probability that
  `ETC.explorationArgmaxCommit spec model` differs from `model.bestArm` is at
  most the finite sum over non-best arms of `ETC.centeredDiffSubGaussianTail`
  with the common interval proxy.
- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`,
  `ETC.CenteredRewardCondSubGaussianWitnesses`,
  `ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`,
  `ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`,
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract`,
  `History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace`, and the
  prior bounded-arm successor MGF and zeroth-coordinate marginal declarations.
- Proof route: prove the generated ETC action equals any fixed-commit trace
  throughout the strict exploration prefix; identify shifted history
  filtrations at each predecessor time via their finite-pair-history comaps;
  transport the selected-reward conditional MGF through the resulting
  measurable-space equality; supply the time-zero MGF from the initial arm law;
  package reward-level then centered-diff witnesses; finally consume the
  existing empirical-mean event inclusion and non-best-arm union bound.
- Regularity contracts: `0 < spec.explorationPulls`; per-arm probability laws;
  common a.s. interval `[lo, hi]`; Rat-to-Real a.e. measurability; exact arm
  integrals equal `model.mean`; measurable history context; canonical initial
  law fixed to the first round-robin arm. No coordinate independence is used.
- Concentration ledger: the process is
  `ETC.centeredPairwiseRewardDiff spec model model.bestArm`; conditioning is the
  shifted finite action/reward history filtration; each contributing summand is
  either a selected centered reward, its negative for the best arm, or zero;
  the proxy is the corresponding masked common Hoeffding proxy; the event is a
  one-sided pairwise empirical-mean comparison at the fixed exploration
  horizon, then union-bounded over finitely many non-best arms. It is not
  two-sided, uniform-in-time, or an anytime confidence statement.
- Retrieval evidence: `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MARTINGALE-STOCHASTIC`, `TXT-LATTIMORE-SZEPESVARI-2020`,
  `SCN-STOCHASTIC-FINITE`,
  `LOCAL-LEAF-ETC-CENTERED-REWARD-COND-SUBGAUSS-WITNESS-CONTRACT`, and
  `LOCAL-LEAF-HISTORY-FILTRATION-FINITEPAIR-COMAP`.
  `WEAPON-TAIL-INEQUALITIES` is inspiration-only.
- Status: `leanCompiled`, with an external `Tests.Basic` canary. The
  measurable-space conditional-MGF transport is recorded as a Mathlib
  candidate; the prefix filtration equality remains project-local.
- Failure policy: do not replace the finite-prefix filtration equality by a
  global generated/fixed action equality, which is false after commitment. Do
  not use ordinary `rw` to transport `HasCondSubgaussianMGF`; its
  sub-sigma-algebra proof is dependent data and requires the compiled explicit
  transport theorem. This leaf produces an ENNReal probability bound only; the
  downstream canonical Bochner leaf below converts and consumes it. External
  environment-law transport remains separate.

## Current Supporting Leaf: Canonical Bounded-Arm Bochner Regret

`ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET` is compiled through
`BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
noncomputable def ETC.canonicalBoundedArmWrongCommitTailBudget
noncomputable def ETC.canonicalBoundedArmWrongCommitTailBudgetReal
noncomputable def ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal
theorem ETC.real_measure_explorationArgmaxCommit_ne_bestArm_le_canonicalBoundedArmWrongCommitTailBudgetReal
theorem ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal
```

- Lean-facing endpoint: for the canonical context-independent bounded finite-arm
  reward-kernel trajectory, the Bochner integral of Real-cast pseudo-regret of
  `ETC.explorationArgmaxGeneratedAction` through horizon
  `spec.explorationPulls * K + r` is bounded by the exploration gap sum plus
  `r * model.maxGap` times the Real canonical wrong-commit tail budget.
- Local APIs/imports:
  `ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws`,
  `ENNReal.toReal_mono`, `Measure.real`,
  `ETC.measurable_empMeanAtExploration_coordinates`,
  `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean`,
  `ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`,
  `ETC.integrable_real_pseudoRegret_actionWithCommit_choice_of_measurable_commit`,
  `ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob`,
  `FiniteBanditModel.gap_le_maxGap`, and
  `ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction`.
- Proof route: name the finite ENNReal wrong-commit tail and prove it is not
  infinite because every summand is `ENNReal.ofReal (Real.exp ...)`; convert
  the canonical probability theorem to a Real bound; prove coordinatewise
  empirical means measurable, hence the finite argmax commit and wrong event
  measurable; derive integrability of the finite-valued pseudo-regret function;
  invoke the generic Bochner assembly with `model.maxGap`; finally rewrite the
  fixed-commit argmax action as the generated finite-history action.
- Regularity contracts: `0 < spec.explorationPulls`; per-arm probability laws;
  common a.s. interval `[lo, hi]`; Rat-to-Real a.e. measurability; exact arm
  integrals equal `model.mean`; measurable context; finite suffix `r`.
  Coordinate independence is not assumed. The initial law is exactly the first
  exploration arm law and the ambient measure is the canonical
  `Kernel.trajMeasure`.
- Expectation ledger: the integrand is Real-cast finite-horizon pseudo-regret;
  measurability comes from the finite empirical-mean argmax and deterministic
  action trace; integrability follows from finite-range boundedness under the
  finite trajectory probability measure; the suffix uses the deterministic
  nonnegative bound `model.maxGap`; the probability multiplier is the finite
  Real wrong-commit tail budget.
- Retrieval evidence: `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
  `MLIB-ORDER-ALGEBRA`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `TXT-LATTIMORE-SZEPESVARI-2020`,
  `SCN-STOCHASTIC-FINITE`,
  `LOCAL-LEAF-ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY`, and
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT`.
  `WEAPON-TAIL-INEQUALITIES` is inspiration-only.
- Status: `leanCompiled`, with `Tests.Basic` public canaries for the named
  budgets, Real probability wrapper, and expected-regret theorem.
- Failure policy: this theorem is a genuine action-dependent canonical-kernel
  expected-regret result. Do not replace an external law by `trajMeasure`
  definitionally. The downstream leaf now gives the exact finite exploration-
  prefix pushforward contract sufficient to transport its integral.

## Current Supporting Leaf: External Exploration-Prefix Law Transport

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET` is compiled in
`BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
noncomputable def ETC.explorationArgmaxPrefixRegretReal
theorem ETC.measurable_explorationArgmaxPrefixRegretReal
theorem ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace
theorem ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace_generated
theorem ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_explorationPrefix_map_eq
```

- Lean-facing endpoint: for any probability measure `mu` on `RewardTrace Rat`,
  if `mu.map (finiteRewardHistoryOfTrace . (m*K-1))` equals the same
  pushforward of the canonical bounded-arm `trajMeasure`, then the canonical
  generated ETC Bochner regret bound holds under `mu`.
- Local APIs/imports: `BanditRLProof.MeasurableRegret`,
  `History.measurable_finiteRewardHistoryOfTrace`,
  `ETC.empMeanAtExploration_completeRewardTrace_eq_of_explorationHorizon_le`,
  `ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction`,
  `MeasureTheory.integral_map`, and the canonical Bochner endpoint.
- Proof route: define the regret integrand on a completed finite reward
  history; prove its measurability through the measurable empirical-mean
  argmax and `measurable_pseudoRegret`; prove pointwise factorization once
  `m*K <= (m*K-1)+1`; use `integral_map` twice and the assumed prefix-law
  equality; finish with the canonical theorem.
- Regularity contracts: an external probability law on `RewardTrace Rat`;
  `0 < explorationPulls`; canonical per-arm probability, common interval,
  cast measurability, exact mean, and context-measurability contracts; equality
  only of the exploration reward-prefix laws. No full infinite-trajectory or
  suffix reward-law equality is required.
- Retrieval evidence: exact upstream `LML-ETC-REGRET` source at seed
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`;
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`,
  `LOCAL-LEAF-ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION`,
  `LOCAL-LEAF-ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT`, and
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET`.
  `WEAPON-TAIL-INEQUALITIES` remains inspiration-only.
- Status: `leanCompiled`, with an external `Tests.Basic` instantiation canary.
- Failure policy: this is a transport consumer, not a proof of its `hprefix`
  hypothesis. The downstream conditional-law leaf now derives that identity;
  matching one-step arm marginals alone remains insufficient. Do not call this the exact LML theorem:
  upstream uses Real rewards and stationary kernels, arbitrary common
  sub-Gaussian laws, `measurableArgmax`, and per-arm gap-weighted expected pull
  counts. The current local RHS is the coarser bounded Rat/max-gap union bound.

## Current Supporting Leaf: External Conditional-Law Prefix Construction

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET` is compiled in
`BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
theorem RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib
theorem ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_condDistrib
```

- Lean-facing endpoint: on an arbitrary probability space `Omega`, a
  coordinate-measurable reward trace with initial law
  `armLaw (ETC.exploreArm spec 0)` and successor conditional law
  `stepKernel i` through the exploration prefix satisfies the same bounded ETC
  Bochner regret inequality as the canonical trajectory.
- Local APIs/imports: Mathlib
  `ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd`,
  `ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`,
  local `RewardKernel.trajMeasure_map_eval_zero`,
  `History.measurable_finiteRewardHistoryOfTrace`, `Measure.map_map`,
  `integral_map`, and the compiled external-prefix theorem.
- Proof route: induct on `n`; identify the joint `(prefix n, reward (n+1))`
  law using `condDistrib`; rewrite the canonical side by the trajMeasure
  compProd recurrence; glue the next coordinate with `IicProdIoc`; specialize
  at `n = explorationPulls*K-1`; consume the prefix-law transport and pull the
  integral from `Measure.map reward mu` back to `mu`.
- Regularity contracts: the generic theorem requires finite `mu`, probability
  `mu0`, coordinate measurability, and a nonempty standard Borel reward target.
  The ETC theorem specializes to an external probability space, bounded
  `Rat` arm laws with exact model means, measurable context, and positive
  exploration pulls. It assumes successor laws only for
  `i < explorationPulls*K-1`; no suffix law, full trajectory equality, or
  coordinate independence is required.
- Retrieval evidence: Mathlib `CondDistrib.lean` and
  `Kernel/IonescuTulcea/Traj.lean`; local cards `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, and
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET`.
  Exact LML source comparison remains at seed
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`; theorem cards and
  `WEAPON-TAIL-INEQUALITIES` are not local proofs.
- Status: `leanCompiled`; the formal module and `Tests.Basic` canary build.
  A requested independent subagent review failed because the local agent quota
  was exhausted, so declaration export, focused builds, and the full project
  check are the review fallback.
- Failure policy: if an external environment does not yet provide the stated
  `condDistrib` identities, keep this theorem intact and add a separate
  stationary/selected-arm law-identification adapter. Do not weaken the regret
  target or replace the ambient process definitionally by `trajMeasure`.

## Current Supporting Leaf: Scheduled Exploration-Arm Conditional Laws

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET`
is compiled in `BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
theorem ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt
theorem ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib
```

- Lean-facing endpoint: an external reward process inherits the bounded ETC
  Bochner regret bound when reward zero has law `armLaw (exploreArm spec 0)`
  and, for `i < explorationPulls*K-1`, reward `i+1` conditioned on its observed
  reward prefix has law `armLaw (exploreArm spec (i+1))`.
- Local APIs/imports: `ETC.explorationArgmaxHistoryPolicy`,
  `RewardKernel.historyStepKernelFamily_apply`,
  `RewardKernel.selectedMeasure_contextIndependentOfActionLaws`, and the
  compiled external-condDistrib theorem.
- Proof route: use `i < m*K-1` to obtain `i+1 < m*K`; unfold the deterministic
  exploration branch of the history policy and the context-independent
  selected reward measure; transport each external a.e. arm-law equality to
  the canonical step-kernel equality; consume the previous theorem.
- Regularity contracts: external probability space, coordinate-measurable
  `RewardTrace Rat`, initial and scheduled-arm conditional laws through
  exploration, positive exploration pulls, bounded per-arm probability laws,
  and exact model means. The public endpoint fixes the irrelevant context to
  `Unit` and exposes no context, reconstructed state, policy kernel, reward kernel, or trajectory measure.
  No suffix law, full trajectory equality, or independence is required.
- Retrieval evidence: local declarations
  `RewardKernel.historyStepKernelFamily_apply`,
  `RewardKernel.selectedMeasure_contextIndependentOfActionLaws`,
  `ETC.explorationArgmaxHistoryPolicy`, and
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET`;
  exact upstream comparison remains `LML-ETC-REGRET` at seed
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`.
- Status: `leanCompiled`, with direct step-kernel and exact expected-regret
  inequality canaries in `Tests.Basic`. Independent local review initially
  found the public context leak, weak `True` canary, and stale failure policy;
  all three were fixed, and the same reviewer reported no remaining findings.
- Failure policy: matching unconditional one-step arm marginals is not enough.
  A concrete environment or LML `IsAlgEnvSeq` adapter must prove the stated
  conditional laws. Keep the bounded Rat/max-gap theorem distinct from the
  exact Real/common-sub-Gaussian/per-arm LML theorem.

## Current Supporting Leaf: Full Action/Reward-History Conditional Laws

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET`
is compiled in `BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
theorem RewardKernel.condDistrib_ae_eq_const_of_comp
theorem RewardKernel.map_eq_of_condDistrib_ae_eq_const
theorem ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib
```

- Lean-facing endpoint: reward zero has the scheduled first-arm law
  conditionally on action zero; reward `i+1` has the scheduled arm law
  conditionally on `(finitePairHistoryOfTrace action reward i, action (i+1))`.
  These LML-shaped constant feedback laws imply the external bounded ETC
  Bochner regret inequality.
- Local APIs/imports: Mathlib
  `condDistrib_ae_eq_iff_measure_eq_compProd`, `Measure.compProd_const`,
  `Measure.map_prod_map`, `Measure.snd_map_prodMk`, `Measure.snd_prod`; local
  `History.measurable_finitePairHistoryOfTrace`,
  `History.measurable_pairHistoryRewardProjection`, and the scheduled-arm
  conditional-law theorem.
- Proof route: express the fine conditional law as a product joint law; map it
  by `(pairHistoryRewardProjection, id)` to obtain the coarse reward-prefix
  joint law; separately take the `snd` marginal of the time-zero joint law;
  consume the scheduled exploration-arm endpoint. The projection need not be
  injective because the conditional kernel is constant.
- Regularity contracts: external probability, timewise measurable action and
  reward traces, nonempty standard Borel Rat target inherited by the generic
  condDistrib lemmas, constant full-history scheduled-arm laws only before
  `m*K-1`, positive exploration pulls, and bounded exact-mean arm laws. No
  action-generation proof, suffix law, full trajectory equality, or
  independence is required.
- Retrieval evidence: exact source audit of LML seed
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, especially
  `IsAlgEnvSeq.hasCondDistrib_feedback_zero`,
  `IsAlgEnvSeq.hasCondDistrib_feedback`, `stationaryEnv`, and
  `ETC.arm_of_lt`; Mathlib source files `Kernel/CondDistrib.lean`,
  `Kernel/Composition/MeasureCompProd.lean`, and `Measure/Prod.lean`.
- Status: `leanCompiled`, with an exact `Tests.Basic` endpoint canary.
  Independent local review reported no findings and separately checked the
  product-map direction, non-injective coarsening, initial `snd` marginal,
  definitional reward-prefix projection, and LML-shaped status boundary.
- Failure policy: this is LML-shaped, not a direct LML import. At the seed,
  `stationaryEnv` supplies an action-dependent feedback kernel and
  `ETC.arm_of_lt` supplies only a.e. exploration action equality. The
  downstream action-dependent adapter now combines their dependency-light
  analogues into the constant kernels assumed here. Do not
  replace conditional laws by marginals or overstate Real/sub-Gaussian/per-arm
  theorem alignment.

## Current Supporting Leaf: Action-Dependent Full-History Kernels

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET`
is compiled in `BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`:

```lean
theorem RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
theorem ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib
```

- Lean-facing endpoint: reward feedback kernels select `armLaw` by action zero
  or by `Prod.snd` of the full-history/next-action condition. If those actions
  are a.e. the scheduled exploration arms, the bounded external ETC Bochner
  regret inequality follows.
- Local APIs/imports: `ae_map_iff`, `measurableSet_eq_fun`,
  `Kernel.ofFunOfCountable`, `RewardKernel.contextIndependentOfActionLaws`,
  and the compiled full-history constant-law theorem.
- Proof route: push `selected (fine omega) = selectedValue` from `mu` to
  `mu.map fine`; combine it with the raw condDistrib kernel equality and the
  pointwise selected-kernel identity; instantiate at `id` for action zero and
  `Prod.snd` for successors; consume the previous endpoint.
- Regularity contracts: finite/probability source, measurable equality on the
  action type, measurable fine condition and selector, timewise measurable
  action/reward traces, exploration action a.e. identities, action-selected
  feedback conditional laws only through exploration, positive exploration
  pulls, and bounded exact-mean Rat arm laws. No suffix law, full trajectory
  equality, or independence is required.
- Retrieval evidence: exact seed definitions of
  `IsAlgEnvSeq.hasCondDistrib_feedback(_zero)`, `stationaryEnv`, and
  `ETC.arm_of_lt`; Mathlib `ae_map_iff`; local context-independent arm-law
  kernel and full-history constant-law consumer.
- Status: `leanCompiled`, with an exact `Tests.Basic` endpoint canary.
- Review: the independent agent exhausted its quota before returning. Fallback
  evidence is the focused module/Test build, exported declarations,
  placeholder scan, syntax/index validation, and full project check.
- Failure policy: this closes the mathematical law adapter without importing
  LML's newer toolchain. A future direct wrapper should only translate its
  `HasCondDistrib` fields and action a.e. equalities; do not claim the exact
  theorem until Real/common-sub-Gaussian, argmax, and per-arm RHS layers compile.

## Current Supporting Leaf: Per-Arm Commit-Probability Assembly

- Lean statement:
  `ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob`.
- Local APIs/imports: the phase-split ETC regret bound, finite-valued commit
  integrability, `ExpectationBochnerSums.integral_univ_sum`,
  `integral_indicator`, and `setIntegral_const`.
- Proof route: partition the measurable finite commit selector into singleton
  fibers, integrate the resulting indicator sum, and combine it with the
  exploration budget through `integral_mono`.
- Regularity contracts: probability `mu` and measurable `commit`; fiber
  measurability and regret integrability are derived. No environment law or
  concentration assumption enters.
- Retrieval evidence: `LOCAL-LEAF-EXP-FINITE-SUM`,
  `LOCAL-LEAF-ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY`, the local
  phase-split theorem, and Mathlib Bochner set-integral APIs.
- Status: `leanCompiled`; focused module and `Tests.Basic` builds pass.
- Failure policy: the armwise canonical probability estimate and its Real
  termwise substitution are compiled downstream. Keep external-law transport
  and the exact LML model/argmax alignment separate rather than weakening this
  per-arm RHS.

## Current Supporting Leaf: Canonical Commit-Arm Pairwise Tail

- Lean statements:
  `ETC.argmaxCommitOracle_eq_arm_subset_empMean_ge_bestArm`,
  `ETC.prob_argmaxCommitOracle_eq_arm_le_pairwise_tail`,
  `ETC.prob_argmaxCommitOracle_eq_arm_le_pairwise_tail_of_contract`, and
  `ETC.explorationArgmaxHistory_prob_commit_eq_arm_le_pairwiseTail_of_boundedArmLaws`.
- Local APIs/imports: concrete argmax maximality,
  `PairwiseEmpMeanTailContract.bound`, `MeasureTheory.measure_mono`, and the
  canonical bounded-arm pairwise contract.
- Proof route: rewrite argmax maximality along `choose scores = a`, obtain the
  single comparison-event inclusion, apply measure monotonicity, consume the
  arm entry of the pairwise contract, then instantiate its bounded-arm
  generated-history producer.
- Concentration/regularity: masked centered pairwise reward difference adapted
  to the fixed `actionWithCommit` history filtration; generated-history
  conditional MGF witnesses are transported to it through exploration-prefix
  measurable-space equality. The proxy is the common interval proxy and the
  event is one-sided at the fixed exploration horizon, with no union. Positive
  exploration pulls, probability arm laws, common a.s. bounds, exact means,
  and measurable context remain explicit.
- Retrieval evidence: local argmax, pairwise contract, bounded-arm conditional
  MGF, and canonical `trajMeasure` declarations; no theorem-card-only result is
  used as proof.
- Status: `leanCompiled`; defining modules and exact `Tests.Basic` canaries pass.
- Failure policy: the Real conversion and termwise substitution now compile
  downstream. Keep external law transport and Real/common-sub-Gaussian/
  measurableArgmax alignment as separate layers.

## Current Supporting Leaf: Canonical Per-Arm Bochner Regret

- Lean statements: `ETC.canonicalBoundedArmPairwiseTailReal`,
  `ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal`,
  `ETC.real_measure_explorationArgmaxCommit_eq_arm_le_canonicalBoundedArmPairwiseTailReal`,
  and
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal`.
- Local APIs/imports: `ETCFiniteArmRewardLaw` imports the generated-history ETC
  policy, conditional sub-Gaussian witnesses, concentration APIs, and
  measurable regret; the proof consumes `ENNReal.toReal_mono`, the compiled
  per-arm Bochner assembly, `Finset.sum_le_sum`,
  `mul_le_mul_of_nonneg_left`, `gap_nonneg`, and `gap_bestArm`.
- Proof route: convert each finite exponential ENNReal tail to Real, invoke the
  generic armwise commit-fiber Bochner decomposition, eliminate the best-arm
  term, and multiply each non-best fiber bound by its nonnegative `r * gap a`
  coefficient before summing.
- Concentration/regularity: the random process remains the masked centered
  pairwise reward difference adapted to the fixed `actionWithCommit` history
  filtration after exploration-prefix conditional-MGF transport. The common
  interval proxy and one-sided fixed exploration horizon are unchanged and no
  union is taken. Positive exploration pulls, probability arm laws, common
  a.s. bounds, exact means, measurable context, and finite suffix `r` remain
  explicit.
- Retrieval evidence: compiled armwise ENNReal tail and generic per-arm
  Bochner leaves, plus Mathlib `ENNReal.toReal_mono` and finite-sum/order APIs;
  theorem cards and weapon-only routes are not used as proof.
- Status: `leanCompiled`; the defining module and exact external
  `Tests.Basic` canary pass.
- Failure policy: external exploration-prefix transport now compiles
  downstream. Keep conditional-law adapters, Real/common-sub-Gaussian support,
  and upstream measurable-argmax tie semantics as later leaves.

## Current Supporting Leaf: External Prefix-Law Per-Arm Bochner Regret

- Lean statements:
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_eq_of_explorationPrefix_map_eq`
  and
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq`.
- Local APIs/imports: the existing finite-prefix regret realization and
  generated-action factorization, `History.measurable_finiteRewardHistoryOfTrace`,
  `MeasureTheory.integral_map`, `integral_congr_ae`, and the canonical per-arm
  Bochner theorem, all from the current `ETCFiniteArmRewardLaw` import surface.
- Proof route: factor the regret integrand through
  `finiteRewardHistoryOfTrace` at `explorationPulls*K-1`, rewrite both integrals
  over their prefix pushforwards, use the supplied pushforward equality, then
  consume the canonical gap-weighted armwise theorem.
- Concentration/regularity: the underlying canonical tails remain the masked
  centered pairwise process on the fixed `actionWithCommit` history filtration
  after exploration-prefix conditional-MGF transport, with common interval
  proxy, one-sided fixed horizon, and no arm union. The transport itself needs
  an external probability law, positive exploration pulls, bounded exact-mean
  arm laws, measurable context, finite suffix `r`, and prefix-pushforward
  equality. It needs no full trajectory law, suffix law, coordinate
  independence, or separate commit-fiber law transport.
- Retrieval evidence: the compiled finite-history reconstruction and canonical
  per-arm leaves plus Mathlib map-integral APIs; theorem-card and weapon-only
  material remains route evidence, not proof.
- Status: `leanCompiled`; focused module and exact `Tests.Basic` canaries pass.
- Failure policy: the initial-marginal/successor-`condDistrib`, scheduled-arm,
  full-history constant-law, and action-dependent selected-kernel per-arm
  consumers all compile downstream. Direct LML integration,
  Real/common-sub-Gaussian support, and measurable-argmax alignment remain
  independent.

## Current Supporting Leaf: External Conditional-Law Per-Arm Bochner Regret

- Lean statement:
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_initial_map_eq_condDistrib`.
- Local APIs/imports: `RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib`,
  `Measure.map_map`, `Measure.isProbabilityMeasure_map`, `integral_map`, the
  finite-prefix regret measurability/factorization APIs, and the compiled
  external prefix-law per-arm endpoint, all on the existing
  `ETCFiniteArmRewardLaw` import surface.
- Proof route: map the coordinate-measurable reward trace to an external
  `RewardTrace Rat` probability law, derive equality with the canonical prefix
  law from `hzero` and successor `hcond`, apply the per-arm prefix theorem, then
  pull the regret integral back to `Omega` with `integral_map`.
- Concentration/regularity: inherited masked centered pairwise process on the
  fixed `actionWithCommit` history filtration after exploration-prefix MGF
  transport, common interval proxy, one-sided fixed horizon, and no arm union.
  External contracts are probability `mu`, coordinate-measurable rewards,
  positive exploration pulls, probability arm laws, common a.s. bounds, exact
  means, measurable context, finite suffix, time-zero marginal, and successor
  conditional laws only for `i < explorationPulls*K-1`. No suffix law, full
  trajectory equality, coordinate independence, or individual fiber law is
  assumed.
- Retrieval evidence: compiled finite-prefix uniqueness, per-arm prefix-law
  transport, and Mathlib measure-map/Bochner APIs; theorem-card and weapon-only
  material remains route evidence rather than proof.
- Status: `leanCompiled`; focused module and exact `Tests.Basic` canary pass.
- Failure policy: the stationary scheduled-arm, full-history constant-law,
  and action-dependent selected-kernel per-arm adapters all compile downstream.
  Direct LML integration, Real/common-sub-Gaussian support, and
  measurable-argmax alignment remain separate.

## Current Supporting Leaf: Scheduled-Arm Conditional-Law Per-Arm Bochner Regret

- Lean statement:
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib`.
- Local APIs/imports: the existing
  `ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt`, the
  compiled external per-arm initial-marginal/successor-`condDistrib` theorem,
  `filter_upwards`, and arithmetic discharge by `omega`, all on the existing
  `ETCFiniteArmRewardLaw` import surface.
- Proof route: fix the irrelevant context to `Unit`; before the exploration
  horizon rewrite `historyStepKernelFamily` to
  `armLaw (ETC.exploreArm spec (i+1))`; transport the caller's a.e.
  scheduled-arm law to the canonical step-kernel contract; consume the per-arm
  conditional-law theorem.
- Concentration/regularity: the inherited process remains the masked centered
  pairwise reward difference adapted to the fixed `actionWithCommit` history
  filtration after exploration-prefix MGF transport, with a common interval
  proxy, one-sided fixed horizon, and no arm union. The public contract needs
  an external probability space, coordinate-measurable Rat rewards, positive
  exploration pulls, probability arm laws, common a.s. bounds, exact model
  means, finite suffix `r`, the initial scheduled-arm law, and successor
  scheduled-arm conditional laws only for `i < explorationPulls*K-1`. It
  exposes no context, local state, policy, reward kernel, trajectory measure,
  suffix law, full trajectory equality, or independence.
- Retrieval evidence: compiled deterministic exploration step-kernel
  reduction and external per-arm conditional-law consumer; theorem-card and
  weapon-only material remains route evidence, not local proof.
- Status: `leanCompiled`; focused module build and an exact standalone
  `Tests.Basic` endpoint canary pass.
- Failure policy: the full action/reward-history constant-law and
  action-dependent selected-kernel per-arm adapters now compile downstream.
  Direct LML integration, Real/common-sub-Gaussian rewards, and
  measurable-argmax tie semantics remain separate leaves; do not reuse a
  max-gap conclusion as if it implied this stronger sum.

## Current Supporting Leaf: Full-History Constant-Law Per-Arm Bochner Regret

- Lean statement:
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib`.
- Local APIs/imports: `RewardKernel.map_eq_of_condDistrib_ae_eq_const`,
  `RewardKernel.condDistrib_ae_eq_const_of_comp`,
  `History.measurable_finitePairHistoryOfTrace`,
  `History.measurable_pairHistoryRewardProjection`, product measurability, and
  the compiled scheduled exploration-arm per-arm endpoint, all on the existing
  `ETCFiniteArmRewardLaw` import surface.
- Proof route: extract the reward-zero marginal from its constant conditional
  law given action zero; for every exploration successor, define the fine
  condition as `(finitePairHistory, nextAction)` and the coarse condition as
  the finite reward prefix; project by `pairHistoryRewardProjection`; coarsen
  the constant scheduled-arm law; consume the scheduled-arm per-arm theorem.
- Concentration/regularity: the inherited process remains the masked centered
  pairwise reward difference adapted to the fixed `actionWithCommit` history
  filtration after exploration-prefix MGF transport, with common interval
  proxy, one-sided fixed horizon, and no arm union. The external contract needs
  probability `mu`, timewise measurable action and Rat reward traces, positive
  exploration pulls, probability arm laws, common a.s. bounds, exact means,
  finite suffix `r`, a constant arm-zero conditional law given action zero,
  and constant scheduled-arm successor laws given the complete fine condition
  only for `i < explorationPulls*K-1`. It needs no injective projection,
  algorithm action-law proof, suffix feedback law, full trajectory equality,
  coordinate independence, or caller-visible local kernel.
- Retrieval evidence: compiled generic constant-law marginal/coarsening APIs,
  finite pair-history measurability/projection, and scheduled-arm per-arm
  consumer; theorem-card and weapon-only material remains route evidence, not
  local proof.
- Status: `leanCompiled`; the defining module and an exact standalone
  `Tests.Basic` endpoint canary pass.
- Failure policy: the action-dependent selected-kernel per-arm adapter now
  compiles downstream. Keep a direct LML import, Real/common-sub-Gaussian
  reward support, and measurable-argmax tie alignment as separate obligations.

## Current Supporting Leaf: Action-Dependent Full-History Per-Arm Bochner Regret

- Lean statement:
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib`.
- Local APIs/imports:
  `RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected`, Mathlib
  `ae_map_iff` and measurable equality, `Kernel.ofFunOfCountable`,
  `RewardKernel.contextIndependentOfActionLaws`, finite pair-history
  measurability, and the compiled full-history constant-law per-arm endpoint,
  all on the existing `ETCFiniteArmRewardLaw` import surface.
- Proof route: at time zero use selector `id` and the a.e. identity of action
  zero to turn `Kernel.ofFunOfCountable armLaw` into the constant scheduled-arm
  law; at each exploration successor use selector `Prod.snd` on the complete
  pair-history/next-action condition, push the a.e. scheduled action identity
  to its map measure, and reduce the context-independent selected kernel to the
  constant scheduled-arm law; consume the full-history per-arm theorem.
- Concentration/regularity: the inherited process remains the one-sided masked
  centered pairwise reward difference adapted to the fixed `actionWithCommit`
  history filtration after exploration-prefix MGF transport, with common
  interval proxy, fixed horizon, and no arm union. The external contract needs
  probability `mu`, timewise measurable action and Rat reward traces, positive
  exploration pulls, probability arm laws, common a.s. bounds, exact model
  means, finite suffix `r`, a.e. scheduled identities for action zero and
  exploration successors, and raw action-selected conditional kernels only
  through `i < explorationPulls*K-1`. It needs no suffix feedback law, full
  trajectory equality, coordinate independence, direct LML dependency, or
  caller-visible local trajectory kernel.
- Retrieval evidence: compiled generic selector-to-constant-law transport,
  Mathlib ae-map/measurability APIs, context-independent arm-law kernels,
  full-history per-arm consumer, and exact-seed `IsAlgEnvSeq`/`ETC.arm_of_lt`
  audit. The exact seed is evidence for the route, not a local imported proof.
- Status: `leanCompiled`; the defining module and an exact standalone
  `Tests.Basic` endpoint canary pass.
- Failure policy: the dependency-light bounded-Rat per-arm law route is now
  closed. A direct newer-toolchain `IsAlgEnvSeq`/`HasCondDistrib` wrapper is
  optional integration work. The next mathematical port must preserve this
  per-arm RHS while replacing bounded Rat arm laws by Real/common-sub-Gaussian
  laws and aligning upstream measurable-argmax tie semantics; do not claim the
  exact LML theorem before those contracts compile.

## Current Supporting Leaf: Common-Sub-Gaussian Pairwise Tail Contract

- Lean statements:
  `ETC.finiteArmCenteredRewardKernelLaw_of_hasSubgaussianMGF`,
  `ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_armLaws`,
  `ETC.explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_armLaws`,
  and `ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_armLaws`.
- Local APIs/imports: existing `ETCFiniteArmRewardLaw` imports;
  `HasSubgaussianMGF.integrable`, `HasSubgaussianMGF.of_map`,
  `RewardKernel.trajMeasure_map_eval_zero`, canonical generated-history
  successor conditional MGF, exploration-prefix filtration equality,
  `HasCondSubgaussianMGF.of_measurableSpace_eq`, and the centered-reward to
  centered-difference witness adapter.
- Proof route: build the context-independent centered kernel law directly from
  each arm's common-proxy MGF and exact mean; map the initial arm witness to
  coordinate zero; obtain successor conditional MGFs from the canonical
  trajectory theorem; transport them to the fixed `actionWithCommit`
  filtration during exploration; consume the existing masked pairwise tail
  constructor.
- Regularity contracts: per-arm probability laws on `Rat`, exact integrals
  equal to `model.mean`, direct centered `HasSubgaussianMGF` at one
  `sigma2 : NNReal`, measurable history context, and positive exploration
  pulls. The resulting process is one-sided, fixed-horizon, masked by the
  candidate/best-arm pulls, and takes no arm union.
- Retrieval evidence: exact LML seed common-proxy MGF hypothesis; Mathlib
  sub-Gaussian integrability/map APIs; local kernel, trajectory marginal,
  conditional-MGF transport, and pairwise witness declarations. The theorem
  card remains source evidence rather than an imported proof.
- Status: `leanCompiled`; focused module build and exact external
  `Tests.Basic` canary pass.
- Failure policy: bounded support is removed only from the canonical
  concentration contract. Reward/model values remain `Rat`; commit-fiber
  probability, per-arm Bochner regret, external conditional-law transport,
  Real rewards, and upstream tie semantics remain downstream. Do not report
  this leaf as `Bandits.ETC.regret_le`.

## Current Supporting Leaf: Common-Sub-Gaussian Canonical Per-Arm Bochner Regret

- Lean statements:
  `ETC.explorationArgmaxHistory_prob_commit_eq_arm_le_pairwiseTail_of_armLaws`,
  `ETC.canonicalSubGaussianArmPairwiseTailReal`,
  `ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal`,
  `ETC.real_measure_explorationArgmaxCommit_eq_arm_le_canonicalSubGaussianArmPairwiseTailReal`,
  and
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal`.
- Local APIs/imports: existing `ETCFiniteArmRewardLaw` imports; direct-MGF
  `PairwiseEmpMeanTailContract`, concrete argmax-fiber probability consumer,
  `ENNReal.toReal_mono`, measurable finite commit selector, generic per-arm
  Bochner assembly, `Finset.sum_le_sum`, gap nonnegativity, and `gap_bestArm`.
- Proof route: bound every non-best concrete commit fiber by its corresponding
  masked pairwise tail; convert the finite ENNReal exponential to Real;
  multiply by the nonnegative `r * gap a` coefficient; sum termwise; remove
  the best-arm term; rewrite the canonical action as the generated-history ETC
  action.
- Regularity contracts: per-arm probability laws on `Rat`, exact integrals
  equal to `model.mean`, direct centered arm MGFs at one common
  `sigma2 : NNReal`, measurable context, positive exploration pulls, and
  finite suffix `r`. No bounded support, max-gap collapse, arm union,
  coordinate independence, or full trajectory transport is assumed.
- Retrieval evidence: exact LML common-proxy/per-arm RHS route; compiled
  direct-MGF pairwise contract; local concrete commit-fiber consumer; Mathlib
  finite tail conversion and Bochner/Finset APIs. The theorem card remains
  evidence for the target rather than an imported theorem.
- Status: `leanCompiled`; focused module build and exact `Tests.Basic`
  endpoint canary pass.
- Failure policy: external exploration-prefix, generic conditional-law, and
  scheduled-arm consumers now compile downstream. This remains a `Rat`
  theorem; the full-history constant-law consumer now compiles, while the
  action-dependent selected-kernel direct-MGF adapter, Real reward/model
  support, exact LML constants/pull-count surface, and upstream argmax tie
  semantics remain open. Do not report it as
  `Bandits.ETC.regret_le`.

## Current Supporting Leaf: Common-Sub-Gaussian External Scheduled-Arm Per-Arm Bochner Regret

- Lean statements:
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq`,
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_initial_map_eq_condDistrib`,
  and
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib`.
- Local APIs/imports: existing `ETCFiniteArmRewardLaw` imports; canonical
  direct-MGF per-arm theorem, finite-prefix regret factorization,
  `RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib`,
  `Measure.map_map`, `Measure.integral_map`, and
  `ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt`.
- Proof route: transport the canonical integral through equality of the first
  `spec.explorationPulls * K` reward pushforwards; derive that equality by
  finite-prefix conditional-law uniqueness; then rewrite the canonical step
  kernel during exploration to the stationary scheduled arm law with
  `Context := Unit`.
- Regularity contracts: arbitrary external probability `mu`, coordinate-
  measurable `RewardTrace Rat`, per-arm probability laws with exact model
  means, direct centered `HasSubgaussianMGF` witnesses at one common
  `sigma2 : NNReal`, positive exploration pulls, finite suffix `r`, the
  scheduled arm-zero marginal, and successor scheduled-arm `condDistrib`
  identities only through exploration. No bounded support, arm union,
  suffix/full trajectory law, independence, individual commit-fiber
  transport, or caller-visible local kernel/state/context is assumed.
- Retrieval evidence: compiled canonical direct-MGF endpoint, generic finite-
  prefix uniqueness, Mathlib map composition and integral-map APIs, and the
  compiled exploration-step-kernel reduction. The LML card is target evidence,
  not an imported proof.
- Status: `leanCompiled`; focused module and exact `Tests.Basic` scheduled-
  endpoint canary builds pass.
- Failure policy: the full action/reward-history constant-law consumer now
  compiles downstream, followed by the action-dependent adapter and native
  Real exact prefix/conditional-law route and selected feedback-law adapter.
  This Rat leaf remains non-final; horizon action equality and argmax ties
  remain. Do not report it as `Bandits.ETC.regret_le`.

## Current Supporting Leaf: Common-Sub-Gaussian External Full-History Per-Arm Bochner Regret

- Lean statement:
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib`.
- Local APIs/imports: existing `ETCFiniteArmRewardLaw` imports;
  `RewardKernel.map_eq_of_condDistrib_ae_eq_const`,
  `RewardKernel.condDistrib_ae_eq_const_of_comp`, finite pair-history
  measurability, `History.measurable_pairHistoryRewardProjection`, and the
  external scheduled-arm direct-MGF endpoint.
- Proof route: recover the scheduled arm-zero marginal from its constant
  conditional law given action zero; project every constant successor law
  given complete finite action/reward history and next action to the reward-
  only prefix; consume the scheduled-arm direct-MGF theorem without changing
  its gap-weighted armwise RHS.
- Regularity contracts: arbitrary external probability `mu`, timewise
  measurable action and `Rat` reward traces, per-arm probability laws with
  exact model means, direct centered `HasSubgaussianMGF` at one common
  `sigma2 : NNReal`, positive exploration pulls, finite suffix `r`, the
  initial constant conditional law, and constant scheduled-arm successor laws
  only through exploration. No bounded support, arm union, injectivity of the
  history projection, algorithm action-generation law, suffix/full trajectory
  law, independence, or caller-visible local trajectory kernel is assumed.
- Retrieval evidence: compiled generic constant-law marginal/coarsening APIs,
  finite pair-history projection/measurability, the scheduled-arm direct-MGF
  theorem, and the exact LML feedback conditioning-variable shape. The LML
  theorem card remains target evidence, not a local proof.
- Status: `leanCompiled`; focused module and exact external `Tests.Basic`
  canary builds pass.
- Failure policy: the action-dependent selected-kernel direct-MGF adapter now
  compiles downstream, closing the dependency-light `Rat` law-transport route.
  Native Real exact constants, counts, product law, and external conditional-
  law transport also compile downstream, followed by least-encoded tie and
  action assembly. Faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.

## Current Supporting Leaf: Common-Sub-Gaussian External Action-Dependent Per-Arm Bochner Regret

- Lean statement:
  `ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib`.
- Local APIs/imports: existing `ETCFiniteArmRewardLaw` imports;
  `RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected`,
  `ProbabilityTheory.Kernel.ofFunOfCountable`,
  `RewardKernel.contextIndependentOfActionLaws`, finite pair-history
  measurability, and the full-history direct-MGF consumer.
- Proof route: push the action-zero a.e. identity to its conditioning law and
  turn the selected initial kernel into the first scheduled arm law; for each
  exploration successor, push the next-action a.e. identity to the complete
  pair-history/next-action conditioning law, turn the selected context-
  independent kernel into the scheduled arm law, and consume the full-history
  direct-MGF theorem without changing its armwise RHS.
- Regularity contracts: arbitrary external probability `mu`, timewise
  measurable action and `Rat` reward traces, per-arm probability laws with
  exact model means, direct centered `HasSubgaussianMGF` at one common
  `sigma2 : NNReal`, positive exploration pulls, finite suffix `r`, scheduled
  action-zero and exploration-successor a.e. identities, and raw action-
  selected conditional laws only through exploration. No bounded support, arm
  union, suffix/full trajectory law, independence, direct LML dependency, or
  caller-visible local trajectory kernel is assumed.
- Retrieval evidence: compiled selector-to-constant-law theorem, Mathlib
  `ae_map_iff`/measurable equality machinery, countable action kernel,
  context-independent arm-law kernel, full-history direct-MGF endpoint, and
  exact LML stationary feedback/action-law shape. The LML theorem card remains
  target evidence rather than an imported proof.
- Status: `leanCompiled`; focused module and exact external `Tests.Basic`
  canary builds pass.
- Failure policy: dependency-light direct common-sub-Gaussian `Rat` law
  transport is closed. Next theorem work must address the actual remaining
  Real reward/model, exact constants/pull-count, and argmax tie mismatches, or
  add a direct newer-toolchain LML wrapper without claiming those mismatches
  are solved.

## Native Real Prefix-Law Transport Obligation

`ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET` is discharged by
`BanditRLProof.Algorithms.ETCRealPrefixLawTransport`. The strongest declaration
is
`ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_initial_map_eq_condDistrib`.
It exposes only the scheduled zeroth reward marginal, scheduled successor
conditional laws through exploration, coordinate measurability, and
finite-horizon a.e. action agreement. Its proof factors the complete exact
regret integrand through `Fin (m*K)`, transports the integral by `Measure.map`,
uses `RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib`, and
identifies constant `Kernel.trajMeasure` with `Measure.infinitePi` through
Mathlib projective-limit uniqueness.

- Regularity: arbitrary measurable probability space, Markov Real arm kernel,
  common centered sub-Gaussian proxy, `0 < m`, `K*m <= n`, and no sample-space
  standard-Borel, external-action measurability, full-law, or infinite-action
  equality premise.
- Retrieval evidence: exact LML `IsAlgEnvSeq` and ETC theorem source shape,
  Mathlib measure/kernel/projective-limit APIs, the compiled native Real
  infinite-product theorem, and generic prefix conditional-law uniqueness.
- Status: `leanCompiled`; focused build and two public canaries pass.
- Failure policy: this obligation is closed. Any next proof must consume the
  upstream `IsAlgEnvSeq` fields and settle the tie rule, not strengthen the law
  assumptions or recreate concentration.

## Native Real Action-Dependent Source Obligation

`ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET` is discharged in
`BanditRLProof.Algorithms.ETCRealSourceAdapter`. Its theorem consumes the exact
shape of upstream initial and successor feedback laws: reward zero conditioned
on action zero, and reward `i+1` conditioned on the complete finite pair
history plus action `i+1`, with the stationary action-selected arm kernel.

The proof uses exploration action a.e. equalities to freeze each selected
kernel, `map_eq_of_condDistrib_ae_eq_const` for the zeroth marginal, and
`condDistrib_ae_eq_const_of_comp` for pair-history-to-reward-prefix coarsening.
It then invokes the native Real exact theorem. Status is `leanCompiled` with an
external canary. The pinned LML source audit confirms these are the
`IsAlgEnvSeq.hasCondDistrib_feedback_zero` and
`IsAlgEnvSeq.hasCondDistrib_feedback` shapes under `stationaryEnv`.

Failure policy: feedback-law source mapping is closed, and the downstream
history-score wrapper and faithful local field consumer now compile. Only
actual cross-toolchain LML symbol import remains; do not reopen this law
transport.

## Native Real Least-Encoded Action Obligation

`ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET` is discharged in
`BanditRLProof.Algorithms.ETCRealArgmaxTie`. Mathlib's first-occurrence
`List.argmax`, `index_of_argmax`, and `idxOf_finRange` prove that the local
strict fold is the least encoded maximizing arm. A specialized `Nat.find`
construction matching the pinned LML selector is then proved equal to that
fold. The action theorem combines round-robin exploration through `K*m-1`,
least-encoded commit at `K*m`, and persistence afterwards, and the strongest
consumer invokes the exact source-law theorem without assuming `hactionETC`.

Status is `leanCompiled`; the focused module and public selector/exact-regret
canaries pass. The downstream history-score obligation now closes the source
score mapping. Remaining blocker classification is actual LML symbol/field
compatibility, not concentration, tie semantics, or finite-history arithmetic.

## Native Real History-Score Source Obligation

`ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET` is discharged in
`BanditRLProof.Algorithms.ETCRealHistoryScore`. It mirrors the pinned source's
inclusive `pullCount'`, `sumRewards'`, and `empMean'` finite-pair-history
surface, proves those quantities equal trace count/sum/mean at `n+1`, and then
specializes `n = K*m-1` under round-robin exploration.

The strongest theorem accepts the commit law directly with the finite-history
score. It combines all exploration action equalities into one a.e. event,
rewrites the score vector pointwise, and invokes the least-encoded exact-regret
endpoint. The regularity contract is unchanged apart from replacing a local-
score commit hypothesis with its source-shaped finite-history version; no
standard-Borel, full-law, independence, or stronger action assumption appears.

Status is `leanCompiled` with external score and exact-regret canaries.
Retrieval evidence is pinned LML `Learning.history`, `pullCount'`,
`sumRewards'`, `empMean'`, `ETC.arm_mul`, Mathlib `Finset.Iic` finite sums, and
the prior least-encoded leaf. Failure policy: finite-history score mapping is
closed, and the local faithful field compatibility consumer compiles
downstream. Only a true cross-toolchain import of the concrete LML symbols
remains; record that dependency boundary rather than hiding it behind stronger
mathematical assumptions.

## Native Real LML Field Compatibility Obligation

`ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET` is discharged in
`BanditRLProof.Algorithms.ETCRealLMLCompat`. The local proposition
`ETC.RealStationaryETCSequence` packages the exact source consequences used by
the route: action/reward measurability, `arm_of_lt`, history-score `arm_mul`,
`arm_of_ge`, and the stationary initial/successor feedback `condDistrib` laws.
`ETC.regret_le_of_realStationaryETCSequence` projects those fields into the
compiled history-score endpoint and returns the exact LML-shaped finite sum.

Regularity is a probability measure, Markov Real arm kernel, common centered
sub-Gaussian proxy, positive exploration, and horizon fit. No standard-Borel
sample space, full trajectory law, independence, local-score premise, or
preassembled action equality is introduced. Retrieval evidence is the pinned
LML `IsAlgEnvSeq`, `stationaryEnv`, ETC action lemmas, and `regret_le`, plus the
toolchain audit: ABRL uses Lean/mathlib `v4.29.1`, while the pinned LML checkout
uses Lean `v4.32.0-rc1` and mathlib commit
`9ca31d8b72cf8c317e49c301bfdbfbe91fc49136`.

Status is `leanCompiled` with a focused build and public theorem canary.
Failure policy: this closes the mathematical field-consumer boundary, but it
does not import or identify the actual upstream symbols. A future direct-import
leaf must make an explicit repository-wide toolchain decision; do not claim
`Bandits.ETC.regret_le` is imported under the current gate.
