# Completion Gap Audit

This audit answers a blunt question: how far is ABRL from fully reproducing the
classic bandit textbook proof weapons and the Mathlib-level foundations they
depend on?

Short answer: ABRL is still early.  The harness, memory indexes, source cards,
proof weapons, a dependency-light finite bookkeeping layer, the first
Mathlib-backed deterministic `Finset.range` wrapper layer, and the first
deterministic regret decomposition consumer exist.  The Mathlib-heavy
measure/probability/concentration/optimization layers are mostly retrieval
cards and proof obligations, not compiled local theorem ports.

## Current Evidence

Current local evidence:

| Artifact | Count | Meaning |
| --- | ---: | --- |
| LML theorem cards | 6 | external Lean theorem-card routes, not local proofs |
| Mathlib retrieval cards | 17 | import/search routes for reusable leaves |
| textbook cards | 3 | Bubeck-Cesa-Bianchi, Lattimore-Szepesvari, Slivkins |
| paper cards | 18 | algorithm/frontier source routes |
| scenario cards | 18 | current bandit/RL taxonomy |
| proof weapon cards | 8 | upper-agent route inspiration only |
| compiled local finite-bookkeeping leaves | 37 | local dependency-light leaves, including pull-count prefix congruence and the `List.range` pull-count, reward-sum, filtered reward-sum, and pseudo-regret bridges |
| compiled local finite-bandit model-invariant leaves | 6 | `FiniteBanditModel.gap_bestArm`, `FiniteBanditModel.mean_le_bestArm_mean`, `FiniteBanditModel.gap_nonneg`, `FiniteBanditModel.maxGap`, `FiniteBanditModel.gap_le_maxGap`, and `FiniteBanditModel.maxGap_nonneg` |
| compiled local Mathlib finite-wrapper leaves | 3 | `pullCount_eq_finset_filter_card`, `sumRewards_eq_finset_filter_sum`, and `pseudoRegret_eq_finset_sum` |
| compiled local regret-decomposition leaves | 1 | `pseudoRegret_eq_finset_sum_gap_mul_pullCount` |
| compiled local regret-count-bound leaves | 3 | Rat-valued, Nat-valued, and uniform Nat count-bound-to-regret scaffolds |
| compiled local pull-count decomposition leaves | 1 | `finset_sum_pullCount_eq_time` |
| compiled local measure-foundation leaves | 3 | `measurableSet_actionTrace_eval_eq`, `measurable_actionTrace_eval_eq_indicator_const`, `measurable_actionTrace_eval_eq_indicator_reward` |
| compiled local probability-union leaves | 1 | `ProbabilityUnionBound.measure_biUnion_finset_le`, `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`, and `ProbabilityUnionBound.measure_iUnion_fintype_le_sum`, Mathlib-backed finite-union outer-measure wrappers for explicit `Finset` and `[Fintype]` event families, including nonempty-`Finset` equal-share `delta/card` normalization; no event measurability or probability-measure assumption |
| compiled local UCB tail-summability leaves | 1 | `UCBSummability.finiteHorizonBadEvent`, `UCBSummability.measure_finiteHorizonBadEvent_le_sum`, and `UCBSummability.measure_finiteHorizonBadEvent_le_tail_sum`, an abstract finite-arm finite-horizon bad-event summability wrapper consuming per-arm/per-time ENNReal tail bounds; no UCB log/sqrt tail producer or final regret theorem |
| compiled local UCB confidence-algebra/event leaves | 16 | `UCB.confidenceScore`, `UCB.meanGap`, `UCB.meanGap_le_two_radius_of_confidenceScore_max`, `UCB.not_two_radius_lt_meanGap_of_confidenceScore_max`, `UCB.upperConfidenceBad`, `UCB.lowerConfidenceBad`, `UCB.confidenceBadEvent`, `UCB.meanGap_le_two_radius_of_not_confidenceBadEvent`, `UCB.measure_confidenceBadEvent_le_sum_upper_lower`, `UCB.measurableSet_upperConfidenceBad`, `UCB.measurableSet_lowerConfidenceBad`, `UCB.measurableSet_confidenceBadEvent`, `UCB.confidenceBadEventAt`, `UCB.measurableSet_confidenceBadEventAt`, `UCB.finiteHorizonConfidenceBadEvent`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_sum_upper_lower`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_tail_sum`, `UCB.not_confidenceBadEventAt_of_not_finiteHorizonConfidenceBadEvent`, `UCB.meanGap_le_two_radius_of_not_finiteHorizonConfidenceBadEvent`, `UCB.mem_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap_of_score_max`, `UCB.scoreMaxEvent_subset_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap`, `UCB.upperConfidenceBad_subset_absDeviation`, `UCB.lowerConfidenceBad_subset_absDeviation`, `UCB.measure_upperConfidenceBad_le_absDeviation`, `UCB.measure_lowerConfidenceBad_le_absDeviation`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_absDeviation_tail_sum`, `UCB.chebyshevAbsDeviationTail`, `UCB.measure_absDeviation_le_chebyshev_tail`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_chebyshev_tail_sum`, `UCB.subGaussianOneSidedDeviationTail`, `UCB.measure_upperConfidenceBad_le_subGaussian_tail`, `UCB.measure_lowerConfidenceBad_le_subGaussian_tail`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_oneSided_tail_sum`, `UCB.subGaussianOneSidedDeviationTail_le_exp_neg_budget`, `UCB.measure_upperConfidenceBad_le_subGaussian_exp_neg_budget`, `UCB.measure_lowerConfidenceBad_le_subGaussian_exp_neg_budget`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_exp_neg_budget_sum`, `UCB.subGaussianBudgetRadius`, `UCB.subGaussianBudgetRadius_nonneg`, `UCB.subGaussianBudgetRadius_sq_domination`, `UCB.subGaussianOneSidedDeviationTail_budgetRadius_le_exp_neg_budget`, `UCB.measure_upperConfidenceBad_le_subGaussian_budgetRadius`, `UCB.measure_lowerConfidenceBad_le_subGaussian_budgetRadius`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_budgetRadius_sum`, `UCB.exp_neg_log_eq_inv`, `UCB.subGaussianLogBudgetRadius`, `UCB.subGaussianLogBudgetRadius_apply`, `UCB.subGaussianLogBudgetRadius_nonneg`, `UCB.subGaussianLogBudgetRadius_sq_domination`, `UCB.subGaussianOneSidedDeviationTail_logBudgetRadius_le_inv_scale`, `UCB.measure_upperConfidenceBad_le_subGaussian_logBudgetRadius`, `UCB.measure_lowerConfidenceBad_le_subGaussian_logBudgetRadius`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_logBudgetRadius_inv_scale_sum`, `UCB.subGaussianConstantLogBudgetRadius`, `UCB.subGaussianConstantLogBudgetRadius_apply`, `UCB.subGaussianConstantLogBudgetRadius_nonneg`, `UCB.subGaussianConstantLogBudgetRadius_sq_domination`, `UCB.constant_invScale_double_sum`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_constantLogBudgetRadius_card`, `UCB.constant_invScale_double_sum_le_of_real`, `UCB.textbookDeltaScale`, `UCB.textbookDeltaScale_pos`, `UCB.textbookDeltaScale_total_inv_budget_eq_delta`, `UCB.constant_invScale_double_sum_textbookDeltaScale_le_delta`, `UCB.subGaussianTextbookDeltaRadius`, `UCB.subGaussianTextbookDeltaRadius_apply`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_textbookDeltaRadius_delta`, `UCB.measure_scoreMaxEvent_le_subGaussian_textbookDeltaRadius_delta_of_gap`, `UCB.subGaussianAbsDeviationTail`, `UCB.measure_absDeviation_le_subGaussian_tail`, and `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_tail_sum`, the deterministic and event-level good-event/index-maximality consumers showing `gap <= 2 * chosenRadius` plus single-time and finite-horizon confidence bad-event union-bound, measurability, finite-horizon good-event-to-gap consumer plus large-gap score-max bad-event subset, abstract tail-budget, absolute-deviation tail-adapter, finite-variance Chebyshev tail producer, one-sided sub-Gaussian upper/lower confidence-failure producer, one-sided radius-budget simplification to `exp(-budget)` under `0 < proxy` and `2 * proxy * budget <= radius^2`, concrete square-root budget radius instantiation using `sqrt (2 * proxy * budget)`, schedule-agnostic logarithmic budget radius instantiation using `sqrt (2 * proxy * log scale)` with inverse-scale tails under `0 < scale`, constant-scale inverse-tail double-sum folding into `T` and `Fintype.card Arm` nsmul, textbook finite-horizon delta-scale allocation `2 * T * |Arm| / delta` with `delta` confidence-bad-event and large-gap score-max event bounds, and abstract two-sided sub-Gaussian absolute-deviation producer wrappers; no concrete empirical-mean measurability, expected pull-count theorem, or final regret theorem |
| compiled local UCB selected-action bridge leaves | 1 | `UCB.selectedEvent_subset_scoreMaxEvent_of_action_score_max`, `UCB.measure_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta`, `UCB.selectedEventOn_subset_finiteHorizonConfidenceBadEvent_of_action_score_max`, and `UCB.measure_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta`, the abstract action-trace bridge saying selected arms with a UCB score-maximality certificate are contained in the score-max event, and finite-time-set large-gap selected-arm events are covered by the same finite-horizon confidence bad event, so they inherit the textbook `delta` probability budget; no concrete UCB argmax/tie-breaking policy, empirical-mean construction, pull-count summation, or final regret theorem |
| compiled local UCB concrete score-argmax leaves | 1 | `UCB.scoreArgmax`, `UCB.scoreArgmax_spec`, `UCB.confidenceScoreArgmaxAction`, `UCB.confidenceScoreArgmaxAction_score_max`, `UCB.confidenceScoreArgmaxAction_score_max_of_selected`, `UCB.measure_confidenceScoreArgmax_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta`, and `UCB.measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta`, a concrete finite-arm Real score argmax over `Fin K` that supplies the selected-action score-max certificate and specializes the single-time/finite-time-set large-gap textbook `delta` wrappers; no empirical-mean construction from reward histories, recursive adaptive action trace, pull-count summation, or final regret theorem |
| compiled practical selected-policy random-width UCB consumers | 1 | `UCB.selectedPolicySuccessorEmpiricalMeanAt`, `UCB.selectedPolicySuccessorRadiusAt`, `UCB.selectedPolicySuccessorIndexAt`, `UCB.SelectedPolicySuccessorInitializedScoreMaxSource`, `UCB.SelectedPolicySuccessorInitializedScoreMaxSource.meanGap_le_two_radius_of_not_badEvent`, and `UCB.measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, preserving the sample-dependent realized-count width and converting the practical simultaneous confidence event into an initialized-time large-gap selection probability bound; concrete generated UCB source/initialization, pull-count expectation, and regret remain open |
| compiled local UCB count-budget leaves | 1 | `UCB.sum_measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_card_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_selectedLargeGapCountOn_le_card_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_horizon_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_free_or_delta_sum`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_freeBudget_add_horizon_delta`, `UCB.freeTimes_indicator_sum_le_card`, `UCB.selectedSmallPullCount_sum_eq_min_pullCount`, `UCB.selectedSmallPullCount_sum_le_threshold`, `UCB.selectedSmallPullCount_indicator_sum_le_threshold`, `UCB.lintegral_selectedSmallPullCount_indicator_sum_le_threshold`, `UCB.selectedPullCount_sum_eq_pullCount`, `UCB.selectedPullCount_indicator_sum_eq_natCast_pullCount`, `UCB.selectedPullCount_indicator_sum_eq_selectedSmall_add_selectedLargePullCount`, `UCB.natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum`, `UCB.measurableSet_selectedLargePullCount`, `UCB.lintegral_selectedLargePullCount_indicator_sum_eq_sum_measure`, `UCB.measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_subGaussian_textbookDeltaRadius_delta`, `UCB.sum_measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_horizon_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_selectedLargePullCount_indicator_sum_le_horizon_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_threshold_add_horizon_delta_of_selectedLargePullCount`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusRecursiveSampleCount_add_horizon_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta`, `UCB.lintegral_historyAction_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta`, `UCB.lintegral_generatedActionTrace_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta`, `UCB.identityActionPolicy`, `UCB.confidenceScoreArgmaxGeneratedState`, `UCB.confidenceScoreArgmaxGeneratedTrace`, `UCB.lintegral_confidenceScoreArgmaxGeneratedTrace_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_freeCard_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadiusChargedTimes`, `UCB.subGaussianTextbookDeltaRadiusFreeTimes`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusFreeCard_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadiusFreeTimes_card_le_threshold`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_large_gap_of_lt_half_meanGap`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusHalfGapThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_sq_lt`, `UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_eight_mul_lt_sq`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusEightProxyLogThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_lt_gap_sq_div`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusProxyThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_le_variance_div_count`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_count_large_of_threshold_lt_bound`, and `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountLowerBound_add_horizon_delta`, a count-facing bridge from concrete finite-arm score-argmax large-gap selected-event probabilities to a finite-time selected-indicator lower-integral bound `|times| * delta`, a `Finset.range T` recursive `pullCount` budget `T * delta` under an all-horizon large-gap contract, a threshold/suffix-shaped split charging explicit free times by `1` while charging all other horizon times by `delta`, an abstract free-time budget consumer yielding `freeBudget + T * delta`, a cardinality wrapper yielding `freeTimes.card + T * delta`, a selected-small pathwise budget proving selected occurrences with prior `pullCount < B` sum to `min (pullCount T) B` and hence at most `B`, a probability-facing lower-integral selected-small budget with the same `B` bound, a selected-small/selected-large-count decomposition, a pointwise ENNReal budget `pullCount <= B + selectedLargeCount`, selected-large-count event measurability under explicit `OpensMeasurableSpace Nat`, selected-large-count finite-sum and lower-integral `T * delta` wrappers from a pointwise large-count-to-large-gap source, a recursive sample-count adapter from `proxy <= varianceProxy / pullCount` plus the real threshold certificate into the concrete `B + T * delta` wrapper, a source-count wrapper that accepts a history-derived `sampleCount` aligned with recursive `pullCount` on selected-large events, a history-action wrapper transferring the same budget to an externally generated trace agreeing with score argmax throughout the horizon, a generated-policy trace wrapper discharging score-argmax measurability from `Policy.generatedActionTrace` state measurability plus pointwise equality, an identity-policy concrete score-argmax generated-trace wrapper discharging the generated-trace equality contract definitionally, concrete textbook-radius large-gap/free-time Finsets instantiating that split, a threshold-cardinality consumer yielding `B + T * delta`, a standard half-gap threshold adapter, square/eight-proxy-log sufficient-condition consumers, a proxy-small threshold consumer under positive log scale, a sample-count threshold consumer from `proxy <= varianceProxy / count`, and a lower-bound-on-count consumer reducing this to a global threshold `B` plus `B <= count`; concrete proxy/count source from empirical rewards, empirical-mean construction, adaptive trace, and final regret theorem remain open |
| compiled local EXP3 potential leaves | 1 | `Exp3Potential.potential`, `Exp3Potential.updatedWeight`, `Exp3Potential.updatedPotential`, updated-potential unfolding, nonnegativity preservation, one-step potential-increment algebra, and finite-horizon telescoping; the downstream deterministic Hedge theorem now compiles |
| compiled local EXP3 deterministic Hedge regret leaves | 1 | `Exp3.cumulativeLoss`, normalized exponential weights, the global `exp(-x) <= 1-x+x^2` bound for `x >= 0`, the one-step log-potential bound, `Exp3.hedge_regret_le_log_card_div_add_eta_mul_mixedSquaredLoss_of_nonneg`, its bounded compatibility wrapper, and `Exp3.hedge_regret_le_log_card_div_add_eta_mul_horizon`; the pathwise second-order theorem now accepts arbitrary nonnegative estimated losses under `eta > 0` |
| compiled local EXP3 importance-weighted moment leaves | 1 | `Exp3.importanceWeightedLoss`, mixed estimate/square definitions, armwise finite-sum identity, pathwise selected-loss cancellation, probability-weighted mixed-loss equality, exact weighted mixed-square identity `sum_a loss(a)^2`, and the `[0,1]` bound by `arms.card`; requires nonzero sampling mass on support, with conditional and generated-process consumers compiled below |
| compiled local EXP3 conditional-moment transport leaves | 1 | `Exp3.FiniteActionDistribution`, finite Dirac action measure/integral wrappers, generic `condDistrib`-to-finite-sum Bochner transport, and specialized armwise/mixed first- and second-moment integral identities; consumes explicit policy/law and score regularity premises |
| compiled local EXP3 generated-action-process leaves | 1 | `Exp3.MeasurableFiniteActionDistribution`, `Exp3.finiteActionKernel`, finite/probability process-measure instances, canonical history-policy `compProd` measure, preserved history marginal, a.e. sampled-action `condDistrib` law, and three canonical moment consumers; its downstream score-regularity producer now discharges the explicit score premises |
| compiled local EXP3 score-regularity leaves | 1 | measurable supported `[0,1]` losses plus `0 < epsilon <= prob` yield armwise/mixed score measurability, pointwise bounds `1/epsilon`, `1/epsilon`, `(1/epsilon)^2`, generated-law integrability, and three canonical consumers without manual `hprob`/`hscore`/`hIntegrable`; generic and concrete sampled-score recursive trajectories compile downstream |
| compiled local EXP3 exploration-mixed recursive-trajectory leaves | 1 | any measurable cumulative score on inclusive finite action/loss histories generates positive exponential weights, normalized and uniformly explored probabilities with floor `gamma / arms.card`, a stochastic `HistoryAlgorithm`, a complete Mathlib-backed adaptive action/loss trajectory, and the exact successor-action `condDistrib`; the concrete sampled-score instantiation compiles downstream |
| compiled local EXP3 sampled-history-score recursive-trajectory leaves | 1 | `Exp3.sampledHistoryScore` recursively adds each observed chosen-action Real loss divided by the exact preceding exploration-mixed probability, proves score measurability and the concrete floor, constructs the stochastic algorithm and complete trajectory, and proves `Exp3.sampledImportanceWeightedTrajectoryMeasure_condDistrib_action` without external `score/hscore`; the predictable-adversary bridge now compiles downstream |
| compiled local EXP3 predictable-adversary leaves | 1 | jointly measurable pre-action initial/successor `[0,1]` loss vectors, deterministic chosen-coordinate Dirac feedback kernels, and the concrete sampled EXP3 action `condDistrib` given `(Env,prefix)` compile; the downstream observed-moment leaf now closes successor reward support and one-round moments |
| compiled local EXP3 predictable expected-regret route | 6 | global next-pair law and conditioning, finite-horizon observed moments, sampled-score/Hedge coupling, predictable-law a.e. control, exploration bias, adaptive pure-q transport, integrability, the unoptimized generated-trajectory theorem, deterministic `4 gamma T` simplification, the large-horizon `4 sqrt(|A| T log|A|)` corollary, realized selected-loss expectation transport, and the all-horizon clipped-rate `min(T, 4 sqrt(|A| T log|A|))` theorem all compile |
| compiled local FTRL one-step leaves | 1 | `FTRL.linearLoss`, `FTRL.finiteSimplex`, `FTRL.regularizedObjective`, `FTRL.IsRegularizedMinimizer`, and the generic/simplex one-step inequalities; consumes explicit minimizer and feasibility certificates under `0 < eta`, with no convexity, minimizer-existence, Tsallis, stability/penalty, or regret theorem |
| compiled local Tsallis regularizer leaves | 1 | `Tsallis.powerSum`, `Tsallis.entropy`, `Tsallis.negEntropyRegularizer`, denominator nonzero from `alpha != 1`, nonnegative `Real.rpow` power sum on `FTRL.finiteSimplex`, and the finite-simplex well-definedness package; no convexity, stability/penalty, self-bounding, learning-rate, or regret theorem |
| compiled local finite-history leaves | 1 | `History.FiniteActionHistory`, `History.FiniteRewardHistory`, `History.FiniteHistory`, `History.FinitePairHistory`, finite trace-restriction maps over `Finset.Iic`, pair-coordinate action/reward trace restriction, pair-history successor extension `History.extendPairHistorySucc`, coordinate evaluation measurability, reward projection from finite `(Action x Reward)` pair histories, measurable successor extension, and measurable finite-history restriction from timewise measurable action/reward traces; this is a product-measurability surface, not a filtration, kernel law, conditional expectation, or trajectory theorem |
| compiled local history-filtration leaves | 11 | `History.historyGenerators`, `History.historyGenerators_mono`, `History.historyMeasurableSpace`, `History.historyMeasurableSpace_mono`, `History.historyMeasurableSpace_le`, `History.historyFiltration`, `History.historyFiltration_apply`, `History.historyFiltrationSucc`, `History.historyFiltrationSucc_apply`, `History.measurableSet_action_mem_historyFiltration`, and `History.measurableSet_reward_mem_historyFiltration`, the action/reward past singleton-event history filtration canary plus the one-step shifted generated history filtration |
| compiled local history-filtration finite-pair comap bridge leaves | 1 | `History.measurable_finitePairHistoryOfTrace_mem_historyFiltration_of_lt`, `History.historyFiltration_succ_eq_comap_finitePairHistoryOfTrace`, and `History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace`, a countable/discrete bridge showing finite pair histories are measurable at later generated-history filtration levels, that `History.historyFiltration ... (n + 1)` is exactly the comap of `History.finitePairHistoryOfTrace ... n`, and that the shifted `History.historyFiltrationSucc ... n` has the same comap form; this aligns the generated filtration with Mathlib finite-prefix conditioning surfaces, but it is not a reward-law, `condExpKernel`, `partialTraj`, trajectory transport, or final theorem |
| compiled local adapted-coordinate leaves | 2 | `History.measurable_action_mem_historyFiltration_of_lt` and `History.measurable_reward_mem_historyFiltration_of_lt`, countable/discrete past-coordinate measurability canaries against `History.historyFiltration`; these are not full policy-predictability or conditional reward-law theorems |
| compiled local policy-measurability leaves | 2 | `Policy.MeasurablePolicy`, `Policy.measurable_action_of_measurable_state`, `Policy.measurable_action_mem_filtration_of_measurable_state`, `Policy.measurable_action_mem_historyFiltration_of_measurable_state`, `Policy.generatedActionTrace`, `Policy.measurable_generatedActionTrace_eval_of_measurable_state`, `Policy.measurable_generatedActionTrace_eval_mem_filtration_of_measurable_state`, `Policy.measurable_generatedActionTrace_eval_mem_historyFiltration_of_measurable_state`, `Policy.generatedActionTraceSucc`, `Policy.generatedActionTraceSucc_succ_eq`, `Policy.measurable_generatedActionTraceSucc_eval_of_measurable_state`, and `Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state`, measurable policy/state composition plus policy-generated and shifted policy-generated action trace coordinate-measurability surfaces; these are not kernel-law or trajectory-law theorems |
| compiled local reward-kernel leaves | 8 | `RewardKernel.MarkovRewardKernel`, `RewardKernel.ofKernel`, selected-measure probability and event-probability measurability wrappers, constant/deterministic reward-kernel constructors, context/action plus policy/state reward-kernel lookup wrappers, one-step `RewardKernel.composePolicy` composition, deterministic `RewardKernel.policyActionKernel`, one-step `RewardKernel.composePolicyActionReward` product kernels, selected-reward marginal wrappers for one-step and history-step action/reward kernels, measure-level `Prod.snd` pushforward reward-marginal equalities and `Prod.fst` deterministic action-Dirac equalities for those action/reward kernels, `RewardKernel.CenteredRewardKernelLaw`, centered-reward law transfer through policy-composed and finite reward-history step kernels, `RewardKernel.partialTrajectoryKernel` finite-prefix reward-history assembly, `RewardKernel.actionRewardPartialTrajectoryKernel` finite-prefix action/reward pair trajectory assembly via Mathlib `partialTraj`, one-step `partialTraj` next-coordinate marginal wrappers `RewardKernel.partialTrajectoryKernel_succ_next_map*` / `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map*`, full one-step/history-step fixed-action pushforward wrappers `RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk` / `RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk`, `ConditionalExpectationReward.pair_map_eq_map_prod_mk_of_action_ae_eq_const_reward_map_eq`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_condExpKernel_map_trajMeasure_of_selectedAction_ae_selectedMeasure`, and the full-prefix frozen-extension wrapper `RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply`; this is not a `condExpKernel` identification, posterior kernel, infinite trajectory law, or final adaptive-regret construction |
| compiled local posterior-kernel leaves | 2 | `PosteriorKernel.MarkovPosteriorKernel`, selector constructors and measurability wrappers, plus `PosteriorKernel.canonicalPosterior`, `PosteriorKernel.canonicalJointMeasure`, `PosteriorKernel.canonicalPosterior_kernel_ae_eq_condDistrib_of_pair_map_eq`, and its canonical-product specialization. The second leaf uses Mathlib `posterior`, `compProd_posterior_eq_map_swap`, `Measure.snd_compProd`, and `condDistrib` uniqueness to produce the environment-given-history posterior law from an exact pair pushforward; arbitrary `BayesianPosteriorSurface` values still have no Bayes-law field, and actual algorithm-history pair-law construction remains separate |
| compiled local Thompson posterior-action identity leaves | 1 | `Thompson.PosteriorActionIdentityLedger`, `Thompson.PosteriorActionIdentityLedger.actionKernel_apply_eq_posteriorBest_map`, and `Thompson.PosteriorActionIdentityLedger.actionKernel_apply_singleton_eq_posteriorBest_preimage`, a source contract and event/singleton consumers for the probability-matching identity between a Thompson action kernel and the posterior pushforward by a measurable best-action map; this consumes the identity and is not Bayes-rule identification, posterior sampler construction, LML import, or Bayesian regret |
| compiled local Thompson posterior best-action measurability leaves | 1 | `Thompson.bestAction_measurable_of_countable_env` and `Thompson.PosteriorActionIdentityLedger.ofCountableEnv`, a Mathlib `measurable_of_countable` wrapper and ledger constructor that discharge best-action measurability for finite/countable environment spaces; this still assumes the event-level posterior action law and is not Bayes-rule identification, posterior sampler construction, LML import, noncountable argmax measurability, or Bayesian regret |
| compiled local Thompson posterior-action conditional-law leaves | 1 | `Thompson.PosteriorActionIdentityLedger.ofPosteriorMap`, `Thompson.PosteriorActionIdentityLedger.actionKernel_eq_posterior_map`, `Thompson.BayesianPosteriorActionSource`, and `Thompson.condDistrib_action_ae_eq_bestAction_of_posteriorMap`, a Mathlib `condDistrib` transport from an action law equal to `posterior.map bestAction` plus a posterior/environment conditional-law identity to the conditional law of the random best action; this is the local counterpart of pinned LML `Bandits.TS.hasCondDistrib_action`, but it still consumes the concrete Bayesian posterior identity and is not a Bayes-density proof, literal LML import, regret decomposition, concentration argument, or Bayesian regret theorem |
| compiled local Thompson canonical posterior pair-law leaves | 1 | `Thompson.condDistrib_action_ae_eq_bestAction_of_bayesianPairMap` and `Thompson.condDistrib_action_ae_eq_bestAction_of_canonicalPriorLikelihood` consume the compiled canonical posterior producer, so the posterior/environment conditional-law identity is no longer assumed. The arbitrary-source theorem requires the exact environment/history pair pushforward and the Thompson next-action conditional law; the canonical product theorem discharges the pair law. The canonical one-step sampler discharges both laws in the next leaf; recursive TS trajectory transport, regret decomposition, concentration, and final Bayesian regret remain open |
| compiled local Thompson canonical sampler probability-matching leaves | 1 | `Thompson.canonicalActionKernel`, `Thompson.canonicalSamplerMeasure`, `Thompson.map_compProd_comap_snd`, both canonical sampler marginal identities, `Thompson.canonicalSampler_condDistrib_action_ae_eq_actionKernel`, and `Thompson.canonicalSampler_condDistrib_action_ae_eq_bestAction` construct the canonical one-step TS joint law and prove probability matching without pair-law or action-law premises. The route uses the canonical posterior, `Kernel.map`/`comap`, `Measure.fst_compProd`, finite-measure product extensionality, and `condDistrib` uniqueness; it is not yet a recursive TS process, algorithm-density transport, regret decomposition, concentration proof, or Bayesian regret theorem |
| compiled local Thompson reference-posterior policy sampler leaves | 1 | `Thompson.referencePosterior`, `Thompson.referenceActionKernel`, `Thompson.policySamplerMeasure`, `Thompson.map_compProd_comap_history`, the sampler marginal/conditional-law/posterior-preservation lemmas, and `Thompson.finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_posterior_invariance` implement LML's fixed-reference-posterior policy boundary. The actual action law is constructed by `compProd`, including the finite action/reward-prefix specialization; the only remaining law premise is reference-versus-actual posterior invariance. This is not the algorithm-density proof, a recursively coupled TS trace, regret decomposition, concentration, literal LML import, or final Bayesian regret |
| compiled local Thompson algorithm-density posterior-invariance leaves | 1 | `Thompson.compProd_withDensity_left`, `Thompson.AlgorithmDensityPosteriorSource`, `Thompson.referencePosterior_ae_eq_condDistrib_of_algorithmDensitySource`, and the generic/finite-pair `...of_algorithmDensitySource` probability-matching endpoints compile the measure-theoretic core of LML's change-of-algorithm route. One measurable history density must explain both the actual history marginal and actual history/environment joint pushforward; commuting that density through the reference posterior `compProd` and applying `condDistrib` uniqueness produces posterior invariance, which is consumed directly by the constructed action sampler. This does not construct the two density laws from a concrete recursive TS process, couple one global trace, port LML structures literally, decompose regret, prove concentration, or close Bayesian regret |
| compiled local canonical trajectory conditional-law leaves | 5 | `RewardKernel.actionRewardHistoryStepKernelFamily_condDistrib_trajMeasure`, the Mathlib `trajMeasure`/`condDistrib` specialization proving the next action/reward pair conditioned on the finite prefix is a.e. the configured history-step kernel on the canonical Ionescu-Tulcea trajectory measure; `RewardKernel.actionRewardHistoryStepKernelFamily_action_condDistrib_trajMeasure`, the `Prod.fst` action-marginal projection via Mathlib `condDistrib_comp`; `RewardKernel.actionRewardHistoryStepKernelFamily_selectedAction_condDistrib_trajMeasure`, the policy-selected action Dirac form via `RewardKernel.actionRewardHistoryStepKernelFamily_action_map`; `RewardKernel.actionRewardHistoryStepKernelFamily_reward_condDistrib_trajMeasure`, the `Prod.snd` reward-marginal projection via Mathlib `condDistrib_comp`; and `RewardKernel.actionRewardHistoryStepKernelFamily_selectedMeasure_condDistrib_trajMeasure`, the selected context/action reward-law form via `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`; these narrow the `COND-EXPECT-REWARD` law-identification route but do not transport an arbitrary ambient `Omega`/`condExpKernel` or `History.historyFiltrationSucc` |
| compiled local Thompson measurable trajectory, global sampler, regret-decomposition, clipped-score, stationary arm-stream, and deterministic support leaves | 6 | `ThompsonMeasurableTrajectory` builds genuine `Env -> PairTrace` kernels and proves projected successor laws and pointwise canonical equality. `ThompsonRecursiveSampler` defines the non-circular uniform-reference Thompson `HistoryAlgorithm`, discharges finite-action absolute continuity, and proves actual-trajectory probability matching. `ThompsonBayesRegretDecomposition` proves score-expectation matching and the LML-shaped finite-horizon decomposition. `ThompsonClippedUCBScore` implements the pinned score and discharges score/mean integrability. `ThompsonStationaryReward` represents stationary reward kernels by independent latent arm streams, proves all-time deterministic trajectory support, and transports arbitrary-action adaptive-count upper/lower tails to a fixed-environment actual augmented trajectory kernel. No supplied posterior/sampler/AC/support premise remains; augmented-prior mixing, measurable clipped-confidence events, the two concentration terms, and final Bayesian regret remain open |
| compiled local conditional-expectation kernel bridge leaves | 208 | `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_zero`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_condExpKernel_integral_eq_zero`, `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_integral_eq`, `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq`, `ConditionalExpectationReward.centeredReward_succ_frozenPast_ae_of_history_frozen`, `ConditionalExpectationReward.condExpKernel_event_real_eq_indicator_of_measurableSet`, `ConditionalExpectationReward.condExpKernel_ae_eq_const_of_countable_measurable`, `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq`, `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq`, `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq`, `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc`, `Policy.generatedActionTraceSucc`, `Policy.generatedActionTraceSucc_succ_eq`, `Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq`, `ConditionalExpectationReward.condExpKernel_pair_map_eq_map_prod_mk_of_action_ae_reward_map_eq`, `ConditionalExpectationReward.random_pair_condExpKernel_map_eq_actual_action_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_action_eq`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_reward_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_reward_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`, `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource`, `ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource_rawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionActualRewardMapSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_generatedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairCenteredSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairCenteredSource`, `ConditionalExpectationReward.generatedActionFromRewardHistory`, `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`, `ConditionalExpectationReward.GeneratedActionPartialTrajectoryPairLawSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_partialTrajectoryKernel_extend_map_eq`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_action_ae_eq_policy_reward_map_eq`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_randomPairDefinitionalMapSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairCenteredSource`, `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalCenteredSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_boundedCenteredSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairBoundedCenteredSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairBoundedCenteredSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawMeanBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.rawReward_succ_aemeasurable_of_measurable_reward`, `ConditionalExpectationReward.generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.selectedMean_succ_aemeasurable_of_measurable_mean`, `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.selectedMean_succ_bound_of_mean_range_bound`, `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.rawReward_succ_bound_of_reward_range_bound`, `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_reward_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_reward_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_historyVarianceSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_varianceCeiling_le`, `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_measurable`, `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable`, `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_historyFiltrationSucc`, `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_measurable`, `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_coordinate_measurable`, `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_historyFiltrationSucc`, `ConditionalExpectationReward.finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen`, `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc`, `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, and `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, and `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk`, `RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`, and `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`, narrow wrappers converting trim-a.e. zero conditional-kernel integrals into ordinary conditional mean-zero facts, an explicit law/integral-equality consumer, a reward-coordinate pushforward-map consumer with a frozen-past condition via Mathlib `integral_map`, a deterministic frozen-history-to-centered-target a.e. bridge, a conditional-kernel frozen-past route for conditioning-measurable events/countable variables/finite reward histories, a concrete finite-history measurability hookup for coordinate-measurable reward prefixes plus generated `History.historyFiltrationSucc`, a finite action/reward pair-history frozen-past hookup under `[Countable Action]`, a successor-extension bridge decomposing the `i+1` pair trace into a frozen old prefix plus random next pair under generated `condExpKernel`, a `Measure.map_congr` pushforward form of that successor decomposition, map-law consumer specializations that discharge the frozen-past side condition from those hooks, an action/reward pair-law marginalization consumer via `Prod.snd`, a generated-history specialization that supplies next-coordinate and reward-prefix measurability from `History.historyFiltrationSucc`, a concrete finite trace pair-history/reward-projection specialization, a projection-measurability hookup that derives projected pairContext/pairState measurability from reward-history context/state measurability, a named `History.finitePairHistoryOfTrace` specialization aligned with the pair-coordinate `partialTraj` surface, a partialTraj finite-pair-trace consumer plus reusable projection adapter that reduces an explicit extended finite pair-trace `condExpKernel` law through the `partialTraj` next-coordinate marginal into the pair-map route, a direct history-step next-pair reward-map adapter that projects an explicit next-pair law through `Prod.snd` into the actual-action reward-coordinate law, a full finite-pair-trace reward-map adapter that projects the same law through `Prod.snd` into the actual-action reward-coordinate law, an extension-map partialTraj consumer with a reusable extension-to-full-trace law adapter that narrows the remaining law assumption to the frozen-prefix extension map while still exposing the whole-trace law, an extension-map reward-map adapter that lifts that narrower law back to the full trace law and projects it to the actual-action reward-coordinate law, a pairmap-to-extension law builder that derives that extension-map law from an explicit next-pair condExpKernel law plus the RewardKernel full-extension wrapper, a split-law builder that derives the next-pair law from a conditional action a.e. equality plus a reward-coordinate selected-measure law, a random-pair history-step law adapter that canonicalizes a generated-action random next-pair source law into the RewardKernel.actionRewardHistoryStepKernelFamily shape, an action-freezing hookup that turns countable `F i`-measurable next actions plus trim-a.e. policy equality into that conditional action a.e. equality, a generated-history action-side hookup that derives the action side from visible finite pair histories, measurable pairState, and pointwise policy-generation equality, and a shifted generated-trace source that supplies that pointwise equality from `Policy.generatedActionTraceSucc`, plus a generated-action actual/random-pair reward-law hookup that marginalizes an actual-action pair-product law to the actual-action reward-coordinate map law, or first freezes a fully random next-pair law with `Measure.map_congr`, then rewrites it to the policy-selected action, feeds the split-law builder, pushes the result through the extension-map `partialTraj` route, exposes reusable full finite-pair-trace partialTraj law adapters for reward-coordinate, actual-action pair-product, and fully random next-pair law shapes, and consumes them for succ-indexed conditional mean-zero under integrability; the generated actual reward-coordinate source contract packages only the actual next-action reward map law as a reusable source, that actual reward-coordinate source now also exposes a source-level canonical history-step pair-law consumer by lifting reward-history context/state through History.pairHistoryRewardProjection, the generated definitional actual reward-coordinate source removes explicit action-trace and `haction` inputs from that source by reusing `generatedActionFromRewardHistory`, that definitional actual reward-coordinate source now also exposes a source-level canonical history-step pair-law consumer over generatedActionFromRewardHistory, a standalone full finite-pair-trace `partialTraj` consumer over generatedActionFromRewardHistory, and an independently indexed integrability-based source-level conditional mean-zero consumer, the generated partialTraj pair-law source contract packages the exact full finite-pair source field, feeds it into the definitional generated random-pair source, and now also projects it into the selected-reward finite-pair-history source, the same source can now be constructed from split generated-history next-pair laws through the action a.e. plus selected-reward map builder, and for generatedActionFromRewardHistory the action side is discharged automatically so the selected reward-coordinate law alone constructs that source, the existing definitional random-pair source now also converts into that partialTraj source by projection, the practical definitional raw-range source now projects its packaged definitional map source and context measurability into the same partialTraj source surface, and the same source plus raw/mean range regularity and either a global variance ceiling, a coarser uniform proxy, selected-history variance ceilings, or a coarser selected-history proxy now directly yields exact- or coarser-proxy succ-indexed conditional MGF witnesses, the generated random-pair source contract packages this remaining law assumption as a reusable source with full-trace consumers, an independently indexed integrability-based conditional mean-zero consumer, and an independently indexed raw-range conditional mean-zero consumer, the generated random-pair source now also exposes a source-level canonical history-step pair-law consumer by lifting reward-history context/state through `History.pairHistoryRewardProjection`, the random-pair source can now be weakened into the actual reward-map source by action freezing and `Prod.snd` marginalization, the centered random-pair source now exposes its packaged random-pair map source directly and can also be projected into that weaker actual reward-map source through its packaged map source and state measurability, the bounded-centered random-pair source now exposes its packaged random-pair map source directly and has the same projection into the actual reward-map source while keeping a.e. measurability and interval-bound evidence for integrability consumers, the definitional generated-action map source defines the action trace as the shifted policy-generated trace over finite reward histories, derives timewise action measurability from measurable state extractors plus reward traces, and can now be constructed from a policy-selected reward-coordinate selected-measure law through the frozen-prefix extension-map route, and that bare source route now directly consumes raw/mean range regularity into succ-indexed conditional mean-zero and, with a global variance ceiling or selected-history variance ceilings, into exact- or coarser-proxy succ-indexed conditional MGF witnesses; the definitional generated-action map source now also exposes a canonical history-step pair-law consumer without explicit action or `haction` parameters, and the generated centered-source contract additionally packages context/state measurability, the centered reward-kernel law, and per-step ambient integrability so the mean-zero consumer no longer needs a separate `h_integrable`; the centered random-pair source now also exposes a canonical history-step pair-law consumer while preserving centered law and integrability fields; the definitional centered-source contract removes explicit action-trace and `haction` inputs from that centered layer using `generatedActionFromRewardHistory` plus the definitional map source; the definitional centered source now also exposes the canonical history-step pair-law consumer over `generatedActionFromRewardHistory`; that definitional centered source now also exposes its packaged ambient integrability as a named theorem and projects into the explicit generated random-pair map source through its packaged definitional map source, into the weaker definitional actual reward-map source through the same package, and into the explicit generated actual reward-map source through the definitional actual-map projection; the generated bounded-centered source contract derives centered-source integrability from per-step a.e. measurability plus a.e. interval bounds through Mathlib `Integrable.of_mem_Icc`, and the bounded-centered source now also exposes the canonical history-step pair law through the centered-source route; the generated raw/mean bounded source contract derives centered a.e. measurability and centered interval bounds from separate raw reward and selected mean evidence, exposes the same canonical history-step pair law through the bounded-centered route, exposes its packaged random-pair map source directly, exposes the same projection into the weaker actual reward-map source, then reuses the bounded-centered route; the generated raw-bound/mean-bounded source contract derives raw reward Rat-to-Real a.e. measurability from existing timewise reward trace measurability, exposes the canonical history-step pair law through the raw/mean bounded route, exposes its packaged random-pair map source directly, exposes the same projection into the weaker actual reward-map source, then reuses the raw/mean bounded route; the generated raw-bound/measurable-mean source contract derives selected mean Rat-to-Real a.e. measurability from a measurable mean surface composed with finite reward histories, context/state extractors, and the measurable policy action, now has an independently indexed source-level conditional mean-zero consumer, exposes its packaged random-pair map source directly, exposes the canonical history-step pair law through the raw-bound/mean-bounded route, exposes the same projection into the weaker actual reward-map source, then reuses the raw-bound/mean-bounded route; the generated raw-bound/measurable-mean-range source contract derives selected mean a.e. interval bounds from deterministic pointwise mean range bounds, now has an independently indexed source-level conditional mean-zero consumer, exposes its packaged random-pair map source directly, exposes the canonical history-step pair law through the raw-bound/measurable-mean route, exposes the same projection into the weaker actual reward-map source, then reuses the raw-bound/measurable-mean route; the generated raw-range/measurable-mean-range source contract derives raw reward a.e. interval bounds from deterministic pointwise reward range bounds, now has an independently indexed source-level conditional mean-zero consumer, exposes the canonical history-step pair law through the raw-bound/measurable-mean-range route, exposes the same projection into the weaker actual reward-map source, then reuses the raw-bound/measurable-mean-range route; the generated definitional raw-range/measurable-mean-range source removes explicit action-trace and `haction` inputs from the practical top layer by reusing `generatedActionFromRewardHistory` plus the definitional map source, the actual-action and policy-selected reward-coordinate raw-range routes now directly consume those laws into succ-indexed conditional mean-zero, and the definitional actual reward-map source now directly consumes raw/mean range regularity into succ-indexed conditional mean-zero, exposes the canonical history-step pair law over `generatedActionFromRewardHistory`, exposes a direct projection into the explicit generated random-pair map source, exposes centered successor reward a.e. measurability and centered interval bounds directly, packages those fields into the bounded centered source over `generatedActionFromRewardHistory`, lowers that package into the integrability-based centered source, packages the same evidence into the definitional centered source, exposes the same projection into the weaker definitional actual reward-map source, also exposes the explicit generated-action actual reward-map projection through the definitional actual-map source, constructs the base definitional raw-range/measurable-mean-range source from actual-action and policy-selected reward-coordinate selected-measure laws without adding variance assumptions, and now consumes the actual-action and policy-selected reward-coordinate selected-measure laws plus selected-history variance ceilings into conditional MGF witnesses, consumes the actual-action or policy-selected reward-coordinate selected-measure law, the full finite-pair partialTraj law, the frozen-prefix extension-map partialTraj law, and the canonical history-step next-pair law, plus a selected-history variance ceiling at any coarser deterministic proxy c satisfying varianceCeiling i <= c, consumes the actual-action or policy-selected reward-coordinate selected-measure law, the full finite-pair partialTraj law, the frozen-prefix extension-map partialTraj law, and the canonical history-step next-pair law plus a uniform variance ceiling at any coarser deterministic proxy c satisfying varianceCeiling <= c, constructs the packaged uniform-variance source from the actual-action or policy-selected reward-coordinate selected-measure law, constructs the packaged history-variance source from the actual-action or policy-selected reward-coordinate selected-measure law, projects a packaged uniform-variance source to its base raw-range/measurable-mean-range bounded source, lowers it to the explicit generated random-pair map source, lowers it to the generated full finite-pair partialTraj source, consumes it into the canonical history-step pair law, lowers it to the weaker definitional actual reward-map source, lowers it to the explicit generated actual reward-map source, and lowers it to the bounded centered-source, integrability-based centered-source, and definitional centered-source interfaces, projects a packaged selected-history-variance source to the same base interface, lowers it to the explicit generated random-pair map source, lowers it to the generated full finite-pair partialTraj source, consumes it into the canonical history-step pair law, lowers it to the weaker definitional actual reward-map source, lowers it to the explicit generated actual reward-map source, and lowers it to the bounded centered-source, integrability-based centered-source, and definitional centered-source interfaces, consumes a packaged uniform-variance source through the selected-history variance-source conditional MGF interface with constant ceiling, consumes a packaged uniform-variance source through any coarser deterministic proxy c satisfying varianceCeiling <= c, and consumes a packaged selected-history variance source through any coarser deterministic proxy c satisfying varianceCeiling i <= c; this does not construct the pair/reward-law source, the ambient trajectory-to-`condExpKernel` identification, or final adaptive theorem |
| compiled local selected-reward finite-pair comap source/theorem wrappers | 1 | `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_reward_map_eq_selected_policy`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_trim_reward_map_eq_selected_policy`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_comap_reward_map_eq_selected_policy`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_comap_trim_reward_map_eq_selected_policy`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_comap_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_comap_trim_reward_map_eq_selected_policy`, wrappers turning a selected-reward `condExpKernel.map` law conditioned on the finite pair-prefix comap sigma-algebra into both `GeneratedActionSelectedRewardFinitePairHistoryLawSource`, the full `GeneratedActionPartialTrajectoryPairLawSource`, and the theorem-card-shaped full finite-pair `partialTraj`/`condExpKernel` law via `History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace`; this now accepts either the generated-history trim filter or the comap-trim filter at the selected-source, partialTraj-source, and theorem-wrapper layers and still consumes, rather than proves, the selected-reward law or ambient trajectory transport |
| compiled local partialTraj/comap raw-range source constructors | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_comap_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_comap_trim_reward_map_eq_selected_policy`, source constructors that package measurable mean, centered reward-kernel law, and raw/mean range regularity from either an explicit generated full finite-pair `partialTraj` source or the finite-pair comap selected-reward law that constructs that source; the selected-reward law can now be supplied at either the generated-history trim surface or the direct comap-trim surface, and this still assumes the selected-reward law and does not prove ambient trajectory transport |
| compiled local partialTraj source mean-zero consumers | 1 | `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeBounded`, a source-level consumer that takes `GeneratedActionPartialTrajectoryPairLawSource` plus raw/mean range regularity and returns ordinary succ-indexed conditional mean-zero for the centered generated reward; this still consumes, rather than proves, the full finite-pair `partialTraj`/`condExpKernel` law and does not add variance/MGF evidence |
| compiled local partialTraj/comap uniform-variance source constructors | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_comap_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_comap_trim_reward_map_eq_selected_policy`, source constructors that package raw/mean range regularity and a global variance ceiling from either an explicit generated full finite-pair `partialTraj` source or the finite-pair comap selected-reward law that constructs that source; the selected-reward law can now be supplied at either the generated-history trim surface or the direct comap-trim surface, and this still assumes the selected-reward law and variance ceiling and does not prove ambient trajectory transport |
| compiled local partialTraj/comap history-variance source constructors | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_comap_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_comap_trim_reward_map_eq_selected_policy`, source constructors that package raw/mean range regularity and selected-history variance ceilings from either an explicit generated full finite-pair `partialTraj` source or the finite-pair comap selected-reward law that constructs that source; the selected-reward law can now be supplied at either the generated-history trim surface or the direct comap-trim surface, and this still assumes the selected-reward law and selected-history ceiling contract and does not prove ambient trajectory transport |
| compiled local condDistrib-to-condExpKernel bridge leaves | 1 | `ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable`, a Mathlib-backed countable-target bridge turning an a.e. `condDistrib X Y mu = kernel` law into an a.e. `condExpKernel mu (comap Y)` pushforward law by `X`; this narrows the canonical trajectory-law-to-consumer route but still consumes, rather than constructs, the trajectory law |
| compiled local canonical trajMeasure pair condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_condExpKernel_map_trajMeasure`, a specialization showing that on the canonical Mathlib `trajMeasure`, `condExpKernel` conditioned on the finite pair prefix and pushed forward by the next `(Action, Reward)` coordinate is a.e. `RewardKernel.actionRewardHistoryStepKernelFamily` at that prefix; this gives the downstream next-pair consumers a canonical source but still does not transport an arbitrary generated process |
| compiled local canonical trajMeasure split-route pair condExpKernel-map leaves | 1 | `ConditionalExpectationReward.pair_map_eq_map_prod_mk_of_action_ae_eq_const_reward_map_eq` and `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_condExpKernel_map_trajMeasure_of_selectedAction_ae_selectedMeasure`, a split-route reconstruction of the canonical next-pair law from selected-action conditional a.e. equality and selected-reward map law under separate `Countable Action` and `Countable Reward`; this validates the split route on canonical `trajMeasure`, not ambient transport |
| compiled local ambient split-product condExpKernel leaves | 1 | `ConditionalExpectationReward.condExpKernel_pair_map_eq_map_prod_mk_of_action_ae_reward_map_eq` and `ConditionalExpectationReward.random_pair_condExpKernel_map_eq_actual_action_of_generatedActionTraceSucc_reward_map_eq_actual_action`, an ambient split-product adapter that turns conditional action a.e. equality plus a reward-coordinate selected-measure law into the fully random next-pair product pushforward, with a generated `History.historyFiltrationSucc` specialization from `Policy.generatedActionTraceSucc`; this still assumes the reward-coordinate law and does not identify the ambient trajectory law |
| compiled local actual-to-random source-conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionActualRewardMapSource`, a source wrapper upgrading `GeneratedActionActualRewardMapSource` plus state measurability into `GeneratedActionRandomPairMapSource` through the ambient split-product condExpKernel law; this still assumes the actual-action reward-coordinate law and ambient trajectory-to-`condExpKernel` identification |
| compiled local definitional actual-to-generated-random source-conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionDefinitionalActualRewardMapSource`, a source wrapper upgrading `GeneratedActionDefinitionalActualRewardMapSource` into the explicit generated-action `GeneratedActionRandomPairMapSource` over `generatedActionFromRewardHistory` by lowering through the actual-to-random source conversion; this still assumes the definitional actual-action reward-coordinate law and ambient trajectory-to-`condExpKernel` identification |
| compiled local explicit centered map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairCenteredSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit centered generated random-pair source; this still assumes the packaged random next-pair law and centered-source regularity fields |
| compiled local explicit bounded-centered map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairBoundedCenteredSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit bounded centered generated random-pair source; this still assumes the packaged random next-pair law and bounded-centered source regularity fields |
| compiled local explicit raw/mean map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawMeanBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward/selected-mean bounded source; this still assumes the packaged random next-pair law and source regularity fields |
| compiled local explicit raw-bound/mean-bounded map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeanBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward-bound/selected-mean bounded source; this still assumes the packaged random next-pair law and source regularity fields |
| compiled local explicit raw-bound/measurable-mean map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward-bound/measurable-selected-mean bounded source; this still assumes the packaged random next-pair law and source regularity fields |
| compiled local explicit raw-bound/measurable-mean-range map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward-bound/measurable-mean-range bounded source; this still assumes the packaged random next-pair law and source regularity fields |
| compiled local explicit raw-range map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward-range/measurable-mean-range bounded source; this still assumes the packaged random next-pair law and top-layer regularity fields |
| compiled local uniform variance to raw-range bounded source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_uniformVarianceBoundedSource`, a projection wrapper exposing the packaged practical raw-range/measurable-mean-range bounded base source from the uniform-variance source; this still assumes the packaged random next-pair law, raw/mean range regularity, and global variance ceiling |
| compiled local uniform variance to random-pair map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the explicit generated random-pair map source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to partialTraj source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into `GeneratedActionPartialTrajectoryPairLawSource`; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to history-step pair-law consumer leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource`, a source-consumer wrapper lowering the packaged uniform-variance source through its generated random-pair map source into the canonical `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to definitional actual reward-map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the weaker definitional generated actual-action reward-coordinate source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to actual reward-map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the explicit generated actual-action reward-map source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to definitional centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the definitional centered-source interface; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local history variance to raw-range bounded source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_historyVarianceBoundedSource`, a projection wrapper exposing the packaged practical raw-range/measurable-mean-range bounded base source from the selected-history-variance source; this still assumes the packaged random next-pair law, raw/mean range regularity, and selected-history variance ceilings |
| compiled local history variance to random-pair map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the explicit generated random-pair map source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to partialTraj source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into `GeneratedActionPartialTrajectoryPairLawSource`; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to history-step pair-law consumer leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource`, a source-consumer wrapper lowering the packaged selected-history-variance source through its generated random-pair map source into the canonical `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to definitional actual reward-map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the weaker definitional generated actual-action reward-coordinate source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to actual reward-map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the explicit generated actual-action reward-map source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local uniform variance to bounded centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the bounded centered-source interface over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its bounded centered-source projection into the integrability-based centered-source interface over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local history variance to bounded centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the bounded centered-source interface over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its bounded centered-source projection into the integrability-based centered-source interface over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to definitional centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the definitional centered-source interface; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local canonical trajMeasure action condExpKernel-map leaves | 3 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_action_condExpKernel_map_trajMeasure`, the `Prod.fst` projection of the canonical next-pair `condExpKernel` law requiring the countable pair target; `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_actionMarginal_condExpKernel_map_trajMeasure`, the direct countable-`Action` route giving the `Prod.fst` marginal of the history-step kernel; and `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedAction_condExpKernel_map_trajMeasure`, the selected-action Dirac form built from that marginal law and `RewardKernel.actionRewardHistoryStepKernelFamily_action_map`; these are canonical `trajMeasure` laws, not ambient `Omega`/`History.historyFiltrationSucc` transport theorems |
| compiled local canonical trajMeasure selected-action condExpKernel-a.e. leaves | 1 | `ConditionalExpectationReward.eventuallyEq_const_of_map_eq_dirac` and `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedAction_condExpKernel_ae_trajMeasure`, a Dirac-pushforward-to-a.e.-constant helper plus the canonical selected-action law in the `Filter.EventuallyEq` shape consumed by the next-pair split-law builder; this is still a canonical `trajMeasure` theorem, not ambient `Omega`/`History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure extension condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_condExpKernel_map_trajMeasure`, the extension-map form of the canonical next-pair law: pushing the canonical `condExpKernel` next-pair law through `History.extendPairHistorySucc` yields the one-step `RewardKernel.actionRewardPartialTrajectoryKernel` surface; this aligns with extension-map consumers but still does not prove ambient `History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure full-prefix condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_prefix_condExpKernel_map_trajMeasure`, the full finite-prefix form of the canonical `trajMeasure` law: the extension-map law plus `condExpKernel` frozen-prefix evidence rewrites the pushforward to `Preorder.frestrictLe (n + 1)` and recovers the one-step `RewardKernel.actionRewardPartialTrajectoryKernel`; this gives a stronger canonical full-prefix source but still does not prove ambient `History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure finite-pair-history condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_finitePairHistoryOfTrace_condExpKernel_map_trajMeasure`, a notation-alignment wrapper restating the canonical full-prefix law with `History.finitePairHistoryOfTrace` for the old and successor pair prefixes; this matches the project theorem-card shape but still does not prove ambient `Omega`/`History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure condExpKernel reward-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_reward_condExpKernel_map_trajMeasure`, a specialization showing that on the canonical Mathlib `trajMeasure`, `condExpKernel` conditioned on the finite pair prefix and pushed forward by the next reward coordinate is a.e. the reward marginal of `RewardKernel.actionRewardHistoryStepKernelFamily`; this is not an ambient `Omega`/`History.historyFiltrationSucc` transport theorem |
| compiled local canonical trajMeasure selected-reward condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure`, the selected context/action reward-measure form of the canonical `trajMeasure` `condExpKernel` next-reward law; this gives downstream selected-policy consumers a direct canonical source but still does not transport an arbitrary generated process |
| compiled local reward-only canonical trajMeasure selected-reward condExpKernel-map leaves | 1 | `RewardKernel.instIsMarkovKernel_historyStepKernelFamily` exposes the already-proved reward-history step-family Markov property to Mathlib, and `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure` applies `Kernel.condDistrib_trajMeasure` plus the local countable-target bridge to prove the selected-reward conditional pushforward law at the finite reward prefix; generated finite-pair alignment, trim-selected-source construction, ambient `IdentDistrib` transport, and recursive `condDistrib` source construction are compiled downstream |
| compiled local reward-only generated finite-pair conditioning leaves | 1 | `ConditionalExpectationReward.comap_finitePairHistoryOfTrace_generatedActionFromRewardHistory_eq_comap_finiteRewardHistoryOfTrace` proves equality of the generated finite-pair and reward-prefix comaps, `ConditionalExpectationReward.historyFiltrationSucc_generatedActionFromRewardHistory_eq_comap_finiteRewardHistoryOfTrace` rewrites the shifted filtration, and `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_generatedActionFromRewardHistory_finitePairHistoryOfTrace` exposes the ordinary canonical selected-reward law on the generated finite-pair surface; the sound trim companion is compiled in the downstream canonical selected-source leaf |
| compiled local reward-only trim-selected-source leaves | 1 | `ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable_trim` lifts the countable-target bridge to the conditioning trim through measurable singleton probabilities, `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_trim` specializes it to reward-only `trajMeasure`, `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_generatedActionFromRewardHistory_finitePairHistoryOfTrace_trim` transports it to generated finite-pair conditioning, and `ConditionalExpectationReward.historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_trajMeasure` constructs the selected source without a selected-reward source assumption; canonical, ambient `IdentDistrib`, and recursive-`condDistrib` full `partialTraj` routes are compiled downstream |
| compiled local ambient IdentDistrib selected-reward transport leaves | 1 | `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_of_identDistrib_trajMeasure_trim` transports the canonical finite-prefix/next-reward joint `compProd` factorization through complete reward-trace `IdentDistrib`, uses disintegration uniqueness to identify the ambient conditional law, and derives the trim selected-reward `condExpKernel.map` equality; `ConditionalExpectationReward.historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_of_identDistrib_trajMeasure` rewrites generated pair-prefix conditioning and constructs the ambient selected source, which the existing converter sends to the full generated `partialTraj` source. The adjacent recursive leaf now constructs the required complete-trace law from initial and successor conditional laws; ambient mean-zero/MGF/tail wrappers remain separate |
| compiled local ambient recursive-condDistrib partialTraj-source leaves | 1 | `RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib`, promoted to foundation module `BanditRLProof.RewardTraceLaw`, derives the complete reward-trace law from the initial marginal and every successor `condDistrib` given its finite prefix. `ConditionalExpectationReward.historyStepKernelFamily_identDistrib_trajMeasure_of_condDistrib` specializes this to the policy/reward history-step family; `historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_of_condDistrib` and `historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_of_condDistrib` then construct the ambient selected and full generated `partialTraj` sources. The caller still must prove the recursive conditional laws; direct ambient MGF and finite-sum tail consumers are compiled in the adjacent concentration leaf |
| compiled local ambient recursive-condDistrib centered finite-sum tail leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource` consumes any generated full `partialTraj` source, measurable mean, `CenteredRewardKernelLaw`, and selected-history variance domination into `HasCondSubgaussianMGF`, deriving exponential integrability without raw/mean range bounds. `historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_of_condDistrib` supplies that source from recursive laws, and `historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_of_condDistrib` derives ambient probability from the initial pushforward, proves strong adaptedness, and obtains the ENNReal Azuma-Hoeffding bound for centered rewards `1..n-1`. Arm/sample-count confidence specialization and concrete production of recursive laws remain open |
| compiled local reward-only canonical generated partialTraj law leaves | 1 | `ConditionalExpectationReward.historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_trajMeasure` converts the canonical trim-aware selected source into `GeneratedActionPartialTrajectoryPairLawSource`, and `ConditionalExpectationReward.historyStepKernelFamily_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_trajMeasure` proves the theorem-shaped successor finite pair-prefix `condExpKernel.map` equality to `RewardKernel.actionRewardPartialTrajectoryKernel`; no ambient selected-reward, random-pair, or partialTraj source hypothesis remains, but the arbitrary-ambient theorem card, regularity packages, and final adaptive theorem remain open |
| compiled local reward-only canonical centered mean-zero leaves | 1 | `ConditionalExpectationReward.historyStepKernelFamily_centeredReward_succ_condExp_eq_zero_trajMeasure` combines the canonical full generated partialTraj law with `RewardKernel.CenteredRewardKernelLaw` and explicit ambient centered-reward integrability to prove successor conditional expectation zero under generated finite-pair history; it deliberately avoids pointwise raw bounds on every `Nat -> Rat` trace, and its conditional-MGF consumer is compiled downstream while ambient integrability production and arbitrary ambient transport remain open |
| compiled local condExpKernel conditional-MGF integrated-transfer leaves | 1 | `ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq` now derives global exponential integrability from trim-a.e. target `HasSubgaussianMGF` laws: `Measure.integrable_comp_iff` combines target-wise integrability with the common MGF bound, `StronglyMeasurable.integral_kernel` supplies inner-integral measurability, and `Integrable.of_bound` uses finiteness of the trim measure; the strengthening propagates through history-step and generated-history consumers but still assumes centered measurability, the conditional pushforward law, and deterministic variance domination |
| compiled local reward-only canonical centered conditional-MGF leaves | 1 | `ConditionalExpectationReward.historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure` combines the canonical full generated partialTraj law, measurable mean, a deterministic finite-history variance ceiling, and the integrated target-law transfer to prove `ProbabilityTheory.HasCondSubgaussianMGF` for the successor centered reward under generated finite-pair history; it has no ambient `h_integrable_exp` or law-source hypothesis, and its canonical finite-sum tail consumer is compiled downstream, while arbitrary ambient transport and final regret remain open |
| compiled local reward-only canonical centered finite-sum tail leaves | 1 | `ConditionalExpectationReward.generatedActionFromRewardHistory_centeredRewardSuccProcess_stronglyAdapted` proves the zero-initialized successor centered-reward process strongly adapted to generated `historyFiltrationSucc`, and `ConditionalExpectationReward.historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_trajMeasure` combines that fact, zero-index sub-Gaussianity, the canonical successor conditional-MGF witnesses, and `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted` into an ENNReal Azuma-Hoeffding bound for the `Finset.range n` sum covering centered rewards `1..n-1`; empirical-mean/confidence specialization and final bandit theorems remain open |
| compiled local canonical trajMeasure selected-reward finite-pair-history condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_finitePairHistoryOfTrace_condExpKernel_map_trajMeasure`, a notation-alignment wrapper restating the canonical selected-reward next-reward law with `History.finitePairHistoryOfTrace` as the finite pair prefix; this matches project history notation but still does not prove ambient `Omega`/`History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure selected-reward reward-history condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_rewardHistoryOfTrace_condExpKernel_map_trajMeasure`, a projection wrapper specializing the finite-pair-history selected-reward law to pair context/state maps built from `History.pairHistoryRewardProjection`, so the RHS is stated with `History.finiteRewardHistoryOfTrace`; this remains canonical `trajMeasure` only |
| compiled local generated selected-reward finite-pair-history source-contract leaves | 1 | `ConditionalExpectationReward.GeneratedActionSelectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_finitePairHistory_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_selectedRewardFinitePairHistoryLawSource`, an ambient generated selected-reward law source and adapter that feeds the existing full finite-pair `partialTraj` source route; it stores and consumes the reward-law field rather than proving ambient trajectory transport |
| compiled local generated selected-reward finite-pair-history partialTraj source-projection leaves | 1 | `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_selectedRewardFinitePairHistoryLawSource`, a direct projection from the generated selected-reward finite-pair-history source to the theorem-card-shaped full `finitePairHistoryOfTrace` partialTraj/condExpKernel law over `generatedActionFromRewardHistory`; it still consumes the selected-reward law field rather than proving ambient trajectory transport |
| compiled local definitional actual-reward source to selected finite-pair-history source leaves | 1 | `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_definitionalActualRewardMapSource`, a source conversion from the definitional actual-action reward-coordinate source into the generated selected-reward finite-pair-history source by unfolding `generatedActionFromRewardHistory` and projecting finite pair histories to reward histories; it still consumes the actual-action reward-coordinate law |
| compiled local practical raw-range source to selected finite-pair-history source leaves | 1 | `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_uniformVarianceBoundedSource`, and `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_historyVarianceBoundedSource`, source-conversion wrappers projecting the practical definitional raw-range/measurable-mean-range generated random next-pair package and its uniform/history variance wrappers into `GeneratedActionSelectedRewardFinitePairHistoryLawSource` through the full finite-pair `partialTraj` source projection; they still assume the packaged random next-pair law and do not prove ambient trajectory transport |
| compiled local practical source via selected finite-pair-history conditional-MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le`, route-specific wrappers showing the practical raw-range source and its uniform/history variance packages reach conditional mean-zero and conditional MGF by first constructing `GeneratedActionSelectedRewardFinitePairHistoryLawSource`; they still assume the packaged random next-pair law and variance/proxy contracts |
| compiled local generated selected-reward finite-pair-history source/comap mean-zero leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded`, and `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded`, direct consumers from either the generated selected-reward finite-pair-history source or the finite-pair comap selected-reward law plus raw/mean range regularity into ordinary succ-indexed conditional mean-zero; they still assume the selected-reward law field |
| compiled local generated selected-reward finite-pair-history source conditional-MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, direct consumers from the generated selected-reward finite-pair-history source plus raw/mean range regularity into succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witnesses under global, coarser global, selected-history, or coarser selected-history variance proxies; they still assume the selected-reward law field and variance/proxy contracts |
| compiled local generated selected-reward finite-pair-history source/comap uniform-variance MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded` and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, direct consumers from the finite-pair comap selected-reward law plus raw/mean range regularity and a global variance ceiling into the succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness by constructing the full finite-pair `partialTraj` source internally; the route now accepts either the generated-history trim filter or the direct comap-trim filter and still assumes the selected-reward law and does not prove ambient trajectory transport |
| compiled local generated selected-reward finite-pair-history source/comap uniform larger-proxy MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le` and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, direct consumers from the finite-pair comap selected-reward law plus raw/mean range regularity, a global variance ceiling, and `varianceCeiling <= c` into the succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness at coarser proxy `c`; the route now accepts either the generated-history trim filter or the direct comap-trim filter and still assumes the selected-reward law, variance ceiling, and proxy-domination contract |
| compiled local generated selected-reward finite-pair-history source/comap history-variance MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded` and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, direct consumers from the finite-pair comap selected-reward law plus raw/mean range regularity and selected-history variance ceilings into the succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness at proxy `varianceCeiling i` by constructing the full finite-pair `partialTraj` source internally; the route now accepts either the generated-history trim filter or the direct comap-trim filter and still assumes the selected-reward law and does not prove ambient trajectory transport |
| compiled local generated selected-reward finite-pair-history source/comap history-variance larger-proxy MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le` and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, direct consumers from the finite-pair comap selected-reward law plus raw/mean range regularity, selected-history variance ceilings, and `varianceCeiling i <= c` into the succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness at coarser proxy `c`; the route now accepts either the generated-history trim filter or the direct comap-trim filter and still assumes the selected-reward law, selected-history ceiling, and proxy-domination contract |
| compiled local measurable-sum leaves | 1 | `measurable_finset_sum_indicator_reward` |
| compiled local measurable-local-quantity leaves | 1 | `measurable_sumRewards` |
| compiled local measurable-regret leaves | 1 | `measurable_pseudoRegret` |
| compiled local measurable-pullcount leaves | 1 | `measurable_pullCount` |
| compiled local measurable-pullcount-cast leaves | 1 | `measurable_natCast_pullCount` |
| compiled local Rat measurability leaves | 1 | `measurable_rat_div_const`, a Rat division-by-constant wrapper under `[MeasurableSingletonClass Rat]` |
| compiled local integrability-sum leaves | 1 | `IntegrabilitySums.integrable_finset_sum` and `IntegrabilitySums.integrable_univ_sum`, Mathlib-backed finite-sum integrability wrappers for explicit `Finset` and finite-arm `Finset.univ` term families; this is not Bochner expectation linearity |
| compiled local Bochner expectation-sum leaves | 1 | `ExpectationBochnerSums.integral_finset_sum` and `ExpectationBochnerSums.integral_univ_sum`, Mathlib-backed finite-sum Bochner integral wrappers under per-term integrability; the bandit-specific expected-regret decomposition is tracked separately |
| compiled local Bochner/Real expected-regret pull-count leaves | 1 | `integrable_real_pseudoRegret_of_integrable_pullCount` and `integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount`, Real-valued Bochner pseudo-regret integrability and expectation decomposition into finite gap-weighted expected pull counts under explicit per-arm pull-count integrability; this is not a Rat-valued expectation theorem, ENNReal lower-integral surrogate, concentration result, or final algorithm theorem |
| compiled local Real mean-regret pull-count leaves | 1 | `realMeanGap`, `realMeanRegret`, `realMeanRegret_eq_sum_gap_mul_pullCount`, and `integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount`, the LML-aligned Real scalar regret and Bochner expected pull-count decomposition; its kernel specialization compiles downstream, while ETC concentration/constants and argmax semantics remain separate |
| compiled local Real kernel-regret pull-count leaves | 1 | `realKernelMean`, `realKernelGap`, `realKernelRegret`, `realKernelGap_nonneg`, `realKernelRegret_eq_sum_gap_mul_pullCount`, and `integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount`, the stationary Real arm-kernel identity-integral specialization; Real ETC expected-count concentration/constants and argmax semantics remain separate |
| compiled local expectation-foundation leaves | 1 | `lintegral_actionTrace_eval_eq_indicator_one` |
| compiled local expectation-sum leaves | 1 | `lintegral_finset_sum_actionTrace_eval_eq_indicator_one` |
| compiled local expectation-pullcount leaves | 1 | `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq` |
| compiled local expectation-weighted-pullcount leaves | 1 | `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` |
| compiled local expectation-pullcount-bound leaves | 1 | `lintegral_natCast_pullCount_le_time` |
| compiled local expectation-weighted-pullcount-bound leaves | 1 | `lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` |
| compiled local expectation-finite-bandit-bound leaves | 1 | `lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` |
| compiled local expectation-finite-bandit-model-bound leaves | 1 | `lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time` |
| compiled local expectation-pseudo-regret-ofReal-bound leaves | 1 | `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg` |
| compiled local expectation-pseudo-regret-rat-bound leaves | 2 | explicit Rat-gap adapter plus model-derived no-explicit-`hgap` adapter |
| compiled local scalar-ENNReal leaves | 1 | `ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg` |
| compiled local scalar-pseudo-regret leaves | 1 | `ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg` |
| compiled local independence foundation leaves | 1 | `IndependenceFoundation.iIndepFun_infinitePi_coord` and `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`, the Mathlib-backed infinite-product coordinate-transform independence wrapper and time-indexed reward-trace specialization |
| compiled local concentration leaves | 9 | `Concentration.intervalVarianceProxy`, `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`, `Concentration.subGaussian_sum_tail_of_iIndepFun`, `Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun`, `Concentration.condSubGaussian_sum_tail_of_stronglyAdapted`, `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`, `Concentration.variance_chebyshev_tail`, `Concentration.evariance_chebyshev_tail`, and `Concentration.variance_sum_of_pairwise_indep`, the generic bounded-centered Hoeffding MGF source, the Mathlib-backed independent and strongly adapted conditional sub-Gaussian finite-prefix tail wrappers and ENNReal-valued boundary adapters, plus the Mathlib-backed Chebyshev/evariance and pairwise-independent finite-sum variance wrappers |
| compiled local algorithm-wrapper leaves | 4 | thin ETC/UCB wrappers, including ETC round-robin periodicity and modular selector characterization |
| compiled local ETC trace leaves | 3 | fixed-commit phase-switching trace boundaries for exploration, commit, and best-arm commit phases |
| compiled local ETC trace-count leaves | 9 | exploration-prefix transfer, configured exploration-horizon count, exploration-horizon Nat denominator-positivity, Rat-cast denominator-positivity, Rat-cast nonzero denominator, one-step post-commit recurrence, closed-form post-exploration suffix count, and commit-arm/non-commit-arm suffix corollaries for the fixed-commit ETC trace |
| compiled local ETC empirical-mean leaves | 3 | `ETC.empMeanAtExploration`, `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls`, `ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos`, and `ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp`, the deterministic fixed-commit exploration-horizon empirical-mean API, positive-denominator finite-sum comparison bridge, and event-shape adapter into abstract fixed-horizon sumRewards tail events |
| compiled local ETC centered-diff finite-sum bridge leaves | 1 | `ETC.centeredPairwiseRewardDiff`, `ETC.centeredPairwiseGapThreshold`, `ETC.sumRewards_le_imp_centered_pairwise_sum_ge`, and `ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`, the deterministic bridge from fixed-horizon sumRewards comparison to the concrete centered pairwise reward-difference finite-sum event |
| compiled local ETC centered-diff witness-contract leaves | 1 | `ETC.CenteredDiffSubGaussianWitnesses` and `ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses`, the exact reward-law witness package consumed by the centered-diff sub-Gaussian producer |
| compiled local ETC conditional witness-contract leaves | 2 | `ETC.CenteredDiffCondSubGaussianWitnesses`, `ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`, `ETC.CenteredRewardCondSubGaussianWitnesses`, and `ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`, the conditional centered-diff witness package plus the reward-level source contract that constructs it from sampled centered-reward conditional MGF witnesses; independence plus unconditional centered-reward sub-Gaussianity supplies the fixed-action conditional MGF bridge, and bounded/source assembly is now compiled separately |
| compiled local ETC strongly-adapted history leaves | 1 | `ETC.measurable_centeredPairwiseRewardDiff_historyFiltrationSucc` and `ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc`, the shifted generated-history adaptedness field for fixed-commit ETC centered pairwise reward differences; it does not derive conditional MGF or mean-zero witnesses |
| compiled local ETC conditional MGF source leaves | 4 | `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_action_miss`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_centeredReward`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_centeredReward`, `ETC.hasCondSubgaussianMGF_of_indep_comap`, and `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`, the zero-summand MGF source, sampled-arm transfer, action-case assembly from sampled centered-reward conditional MGF witnesses, and independence-based conditional MGF bridge from unconditional centered-reward sub-Gaussianity; fixed-action bounded/source assembly is tracked in the bounded-source conditional route row |
| compiled local ETC bounded-source conditional route leaves | 4 | `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`, `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_boundedRewardTraceSource`, `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource`, `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian`, `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail`, `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian`, `ETC.centeredRewardCondSubGaussianWitnesses_of_infinitePi_bounded_actionMean_canonicalTail`, `ETC.pairwiseEmpMeanTailContract_of_infinitePi_bounded_actionMean_condSubGaussian_canonicalTail`, and `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian`, the fixed `actionWithCommit` bounded-source assembly from `BoundedRewardTraceSource` to conditional mean-zero, reward-level conditional witnesses, pairwise tail contracts, and argmax wrong-commit probability consumers, including the canonical-tail no-`htail` variant and its infinitePi specialization |
| compiled local ETC conditional mean-zero source leaves | 2 | `ETC.centeredReward_condExp_eq_zero_of_indep`, `ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`, and `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`, the Mathlib `condExp_indep_eq` wrapper, shifted-history specialization, succ-indexed Mathlib tail shape, direct reward-coordinate iIndepFun plus full fixed-action history conditional mean-zero wrapper under an explicit zero-integral side condition, and bounded-source wrapper that supplies that side condition from `BoundedRewardTraceSource` |
| compiled local martingale-difference witness leaves | 2 | `MartingaleDiff.SuccMartingaleDifference`, `MartingaleDiff.SuccMartingaleDifference.toPrefix`, `MartingaleDiff.SuccMartingaleDifference.stronglyAdapted'`, `MartingaleDiff.SuccMartingaleDifference.integrable'`, `MartingaleDiff.SuccMartingaleDifference.condExp_succ_ae_eq_zero`, `MartingaleDiff.SuccMartingaleDifferencePrefix`, `MartingaleDiff.SuccMartingaleDifferencePrefix.stronglyAdapted'`, `MartingaleDiff.SuccMartingaleDifferencePrefix.integrable_of_lt`, `MartingaleDiff.SuccMartingaleDifferencePrefix.condExp_succ_ae_eq_zero`, `MartingaleDiff.centeredRewardProcess`, `MartingaleDiff.succMartingaleDifference_centeredRewardProcess_of_condExp`, `MartingaleDiff.succMartingaleDifferencePrefix_centeredRewardProcess_of_condExp`, `MartingaleDiff.partialSumsSucc`, `MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference`, `MartingaleDiff.martingale_partialSumsSucc_centeredRewardProcess_of_condExp`, `ETC.measurable_centeredReward_actionWithCommit_historyFiltrationSucc`, `ETC.stronglyAdapted_centeredReward_actionWithCommit_historyFiltrationSucc`, `ETC.centeredReward_actionWithCommit_integrable_of_boundedRewardTraceSource`, and `ETC.centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource`, the global and finite-prefix martingale-difference witness contracts, centered reward process builders from adaptedness/integrability/conditional-mean-zero contracts, abstract Mathlib partial-sum `Martingale` wrappers, and fixed deterministic `actionWithCommit` bounded-source centered-reward instance; broad adaptive-policy reward-law construction remains open |
| compiled local stopping-time foundation leaves | 1 | `Budget.budgetExhaustionTime`, `Budget.isStoppingTime_budgetExhaustionTime_of_adapted`, and `Budget.measurableSet_budgetExhaustionTime_le_of_adapted`, the Mathlib `hittingAfter` wrapper showing an adapted `Nat`-valued accumulated-resource process reaches a budget at a stopping time, plus the level-`n` measurability event; this is not a BwK model, optional-stopping theorem, or resource-constrained regret proof |
| compiled local ETC reward-only past independence leaves | 1 | `ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward` and `ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi`, the reward-coordinate iIndepFun bridge proving centered reward at `i + 1` is independent of the reward-only past coordinate sigma-algebra generated by `j <= i`, plus the infinite-product specialization |
| compiled local ETC fixed-action history independence leaves | 1 | `ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup`, `ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`, and `ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi`, the deterministic action-generator inclusion and full fixed `actionWithCommit` `History.historyFiltrationSucc` independence bridge for future centered rewards |
| compiled local ETC bounded-to-integrable source leaves | 1 | `ETC.centeredReward_integrable_of_mem_Icc` and `ETC.centeredReward_integrable_of_boundedRewardTraceSource`, the Mathlib `Integrable.of_mem_Icc` wrapper and action-matched `BoundedRewardTraceSource` wrapper turning bounded rewards into raw reward integrability |
| compiled local ETC centered-reward zero-integral source leaves | 1 | `ETC.centeredReward_integral_eq_zero_of_integral_eq_mean`, `ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean`, and `ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean`, the exact raw-mean plus integrability source, bounded-Icc source, and action-matched `BoundedRewardTraceSource` wrapper for the centered reward zero-integral side condition |
| compiled local ETC centered-diff canonical-tail leaves | 1 | `ETC.centeredDiffSubGaussianTail`, `ETC.centeredDiffSubGaussianWitnesses_of_indep_subG`, and `ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG`, the canonical exponential tail helper for the independent sub-Gaussian centered-diff route |
| compiled local ETC empirical-mean measurability leaves | 4 | `ETC.measurable_sumRewards_actionWithCommit_exploration`, `ETC.measurable_empMeanAtExploration_of_measurable_div_const`, `ETC.measurable_empMeanAtExploration`, and `ETC.measurable_empMeanAtExploration_coordinates`, the numerator bridge, explicit-division wrapper, no-`hdiv_const` wrapper, and coordinate-shaped wrapper |
| compiled local ETC count leaves | 4 | first-cycle count, add-`K` recurrence, `m * K` count, and configured exploration-horizon count |
| compiled local ETC regret leaves | 9 | exploration-only, fixed-commit exploration-horizon, suffix count-budget, coarse suffix, phase-split equality, optimal-commit no-extra-suffix, optimal-commit suffix bound, phase-split suffix-gap bound, and pointwise wrong-commit suffix-penalty assembly scaffolds |
| compiled local ETC measurability leaves | 8 | `ETC.measurableSet_commitArm_ne_bestArm`, `ETC.measurable_empMeanVector_of_forall_measurable`, `ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`, `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean`, `ETC.measurableSet_commitOracle_ne_bestArm`, `ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`, `ETC.measurableSet_empMean_ge_empMean`, and `ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`, the wrong-commit event, Mathlib Pi-space empirical-mean vector, countable score-vector oracle-choice, coordinatewise empirical-mean-to-oracle-choice composition, oracle-selected wrong-commit, coordinatewise empirical-mean-to-oracle-wrong-event composition, pairwise empirical-mean comparison, and finite existential wrong-mean event measurability leaves |
| compiled local ETC event-reduction leaves | 2 | `ETC.wrong_commit_subset_exists_empMean_ge_bestArm` and `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`, the pure wrong-commit set-inclusion leaf and the abstract commit-oracle argmax consumer |
| compiled local ETC probability-wrapper leaves | 20 | `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`, `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`, `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`, `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`, `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`, `ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail`, `ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`, `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`, `ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian`, and `ETC.real_measure_fixedProductArgmaxCommit_ne_bestArm_le_fixedProductWrongCommitTailBudgetReal_of_infinitePi_bounded_actionMean`, the arbitrary-measure monotonicity, finite-union upper-bound, final elementary assembly, abstract pairwise-tail consumer, if-zeroed nonbest pairwise-tail consumer, filtered-sum tail-consumer wrapper, oracle-specialized pairwise-tail consumers, canonical centered-diff wrong-commit bound, reward-coordinate-law wrong-commit bound, strong all-arm bounded-reward wrong-commit bound, action-matched wrong-commit bounds, source-contract wrong-commit wrapper, bounded-source conditional-route probability wrappers, fixed product-coordinate source wrong-commit wrappers, and the fixed-product `Measure.real` probability bridge |
| compiled local ETC concentration-bridge leaves | 6 | `ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds`, `ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds`, `ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`, `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward`, `ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean`, and `ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource`, the abstract sub-Gaussian producer surface, the concrete centered-diff independent and conditional specializations for `ETC.PairwiseEmpMeanTailContract`, the deterministic transfer from centered reward sub-Gaussianity to centered pairwise reward-difference sub-Gaussianity, the Mathlib Hoeffding-lemma source from bounded rewards plus exact mean identities, and the action-matched source-contract consumer for that centered reward sub-Gaussian witness |
| compiled local ETC reward-law transfer/source leaves | 26 | `ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward`, `ETC.centeredPairwiseRewardDiffVarianceProxy`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`, `ETC.centeredRewardBoundVarianceProxy`, `ETC.centeredReward_integrable_of_mem_Icc`, `ETC.centeredReward_integral_eq_zero_of_integral_eq_mean`, `ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean`, `ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward`, `ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup`, `ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`, `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered`, `ETC.BoundedRewardTraceSource`, `ETC.centeredReward_integrable_of_boundedRewardTraceSource`, `ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean`, `ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource`, `ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi`, `ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi`, `ETC.boundedRewardTraceSource_infinitePi_actionWithCommit`, and `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`, the deterministic transfer from reward-trace time-coordinate independence, the action-case variance proxy, integrability and zero-integral source wrappers, reward-only and full fixed-action history independence bridges plus succ-indexed conditional mean-zero/conditional MGF shapes, bounded-source conditional mean-zero, wrong-commit bounds under centered reward sub-Gaussian witnesses and bounded rewards, the action-matched variants keyed to the actually pulled arm, the bounded-reward variance proxy, the compiled action-matched source-contract package plus consumers, and the concrete fixed product-coordinate source |
| compiled local ETC lower-integral regret assembly leaves | 7 | `ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob`, `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean`, `ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductBadGapLintegralRegretBound_of_infinitePi_bounded_actionMean`, `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean`, `ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductSumGapLintegralRegretBound_of_infinitePi_bounded_actionMean`, `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean`, and `ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean`, the abstract, concrete argmax/infinitePi, polished fixed product-coordinate bad-gap, conservative sum-gap-adapted, polished fixed product-coordinate sum-gap, sharper max-gap-adapted, and polished fixed product-coordinate max-gap `ENNReal.ofReal` lower-integral bridges from wrong-commit probability control to an ETC regret surrogate |
| compiled local ETC Bochner expected-regret assembly leaves | 19 | the abstract/fixed-product/canonical bounded endpoints, complete dependency-light max-gap/per-arm bounded transports, canonical direct-MGF per-arm endpoint, its equal-prefix/external-`condDistrib`/scheduled-arm/full-history/action-dependent selected-kernel transport, and the Real per-arm count-to-commit-probability expected-count endpoint; dependency-light direct-MGF `Rat` law transport, Real kernel scalar bookkeeping, and expected-count integration are closed, while direct LML integration, the concrete Real commit-fiber exponential probability producer, and argmax alignment remain open |
| ETC wrong-commit design cards | 1 | `ETC-WRONG-COMMIT-PROBABILITY-DESIGN`, a theorem-card-only event-reduction route, not a local proof |
| scanned local Lean declarations | 1237 | definitions, structures, and theorems in `BanditRLProof/` after the Real ETC expected pull-count refresh |

The compiled local layer currently covers:

- finite action traces;
- pull counts, segment counts, and a dependency-light `List.range` finite-prefix bridge;
- reward sums, one segment-stability lemma, a dependency-light `List.range`
  fold bridge, and a filtered-list bridge under an explicit right-zero law;
- rational finite-arm mean models;
- a local best-arm dominance invariant showing every arm mean is at most the
  selected `bestArm` mean;
- model-derived Rat gap nonnegativity and finite max-gap invariants for
  `FiniteBanditModel.gap`;
- pseudo-regret zero/segment leaves and a dependency-light `List.range` fold bridge;
- a Mathlib-backed `pullCount` wrapper as filtered `Finset.range` cardinality;
- a Mathlib-backed selected reward-sum wrapper as a filtered `Finset.range` sum
  under `[AddCommMonoid Reward]`;
- a Mathlib-backed pseudo-regret wrapper as a `Finset.range` sum of gaps;
- a deterministic pseudo-regret decomposition as an arm-indexed sum of
  `gap * pullCount`;
- a deterministic scaffold converting per-arm pull-count upper bounds into a
  gap-weighted pseudo-regret upper bound;
- a Nat-count convenience adapter for algorithmic count lemmas that produce
  `pullCount <= B` with `B : Fin K -> Nat`;
- a uniform Nat-count adapter turning `forall a, pullCount a n <= B` into a
  `pseudoRegret <= (sum gaps) * B` bound;
- a deterministic finite-action count partition showing pull counts sum to the
  time horizon;
- first measure-foundation canaries showing measurable action evaluations yield
  measurable action-equality events and measurable constant-valued pull
  indicators;
- finite action/reward history product objects over `Finset.Iic` prefixes,
  with measurable coordinate projections and measurable trace-restriction maps
  from timewise measurable action/reward traces;
- a first expectation/integration canary showing the `ENNReal` lower integral
  of an action-equality pull-event indicator equals the event measure;
- an `ENNReal` lower-integral finite-sum bridge for action-equality pull-event
  indicators;
- an `ENNReal` lower-integral identity connecting scalar-casted recursive
  `pullCount` to the finite sum of action-event measures;
- an `ENNReal` lower-integral finite-arm weighted pull-count bridge,
  converting `sum_a gap a * pullCount a n` to weighted action-event measures;
- an `ENNReal` probability-measure pull-count budget bound, showing the
  lower integral of a scalar-casted pull count is at most the horizon;
- an `ENNReal` probability-measure weighted pull-count budget bound, showing
  a finite weighted lower-integral pull-count sum is bounded by its weighted
  horizon budget;
- a `Fin K`/`Finset.univ` specialization of that weighted probability budget
  bound for finite-arm algorithm theorem scaffolds;
- an `ENNReal.ofReal` surrogate model-gap wrapper bound for
  `FiniteBanditModel.gap : Fin K -> Rat`, explicitly before any faithfulness
  or Bochner expected-regret claim;
- a scalar `ENNReal.ofReal` faithfulness leaf for finite sums of nonnegative
  real weights times natural counts;
- a pointwise scalar/model pseudo-regret faithfulness bridge from Rat-valued
  pseudo-regret to the `ENNReal.ofReal` weighted pull-count expression under an
  explicit gap nonnegativity hypothesis;
- an `ENNReal.ofReal` lower-integral pseudo-regret bound under explicit gap
  nonnegativity, before any Rat-valued or Bochner expected-regret claim;
- a Rat-level gap nonnegativity contract adapter for that lower-integral bound,
  retained as a generic explicit-`hgap` route;
- a no-explicit-`hgap` `ENNReal.ofReal` lower-integral pseudo-regret bound
  using `FiniteBanditModel.gap_nonneg`;
- a Real-valued Bochner expected-regret decomposition, under explicit per-arm
  Real-cast pull-count integrability, from pseudo-regret to the finite sum of
  Real-cast gaps times expected pull counts;
- thin ETC and UCB wrapper lemmas, including ETC round-robin periodicity.
- fixed-commit ETC phase-switching trace boundaries, with exploration-prefix
  agreement to the pure round-robin selector, post-horizon agreement to the
  supplied commit arm, and best-arm agreement when the commit arm is selected
  best arm.
- an exploration-prefix pull-count transfer from the fixed-commit ETC trace to
  the pure round-robin exploration trace.
- a configured exploration-horizon pull-count theorem for the fixed-commit ETC
  trace.
- a deterministic exploration-horizon positive pull-count theorem for the
  fixed-commit ETC trace under `0 < spec.explorationPulls`, serving as the
  first Nat-level denominator-positivity leaf for later empirical means.
- a Rat-cast exploration-horizon positive pull-count theorem for the
  fixed-commit ETC trace, serving as the first rational denominator adapter for
  later empirical means.
- a Rat-cast exploration-horizon nonzero pull-count theorem for the
  fixed-commit ETC trace, serving as the first rational nonzero-denominator
  adapter for later empirical means.
- a one-step post-commit pull-count recurrence for the fixed-commit ETC trace.
- a closed-form post-exploration suffix pull-count theorem for the fixed-commit
  ETC trace.
- a non-commit-arm post-exploration suffix pull-count stability corollary for
  the fixed-commit ETC trace.
- a commit-arm post-exploration suffix pull-count corollary for the
  fixed-commit ETC trace.
- deterministic pseudo-regret scaffolds for the fixed-commit ETC trace through
  the exploration horizon, suffix count-budget, coarse suffix, phase-split
  equality, optimal-commit no-extra-suffix equality, optimal-commit suffix
  bound, and phase-split suffix-gap bound.
- the first ETC wrong-commit event measurability canary:
  `ETC.measurableSet_commitArm_ne_bestArm`.
- the pure ETC wrong-commit event-reduction set inclusion:
  `ETC.wrong_commit_subset_exists_empMean_ge_bestArm`.
- the arbitrary-measure wrapper for the wrong-commit event reduction:
  `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`.
- the pairwise empirical-mean comparison-event measurability canary:
  `ETC.measurableSet_empMean_ge_empMean`.
- the finite existential wrong-mean event measurability wrapper:
  `ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`.
- the reusable finite-union probability/outer-measure wrappers:
  `ProbabilityUnionBound.measure_biUnion_finset_le`,
  `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`, and
  `ProbabilityUnionBound.measure_iUnion_fintype_le_sum`.
- the abstract finite-horizon UCB bad-event summability wrapper:
  `UCBSummability.finiteHorizonBadEvent`,
  `UCBSummability.measure_finiteHorizonBadEvent_le_sum`, and
  `UCBSummability.measure_finiteHorizonBadEvent_le_tail_sum`.
- the deterministic finite-action EXP3 potential surface:
  `Exp3Potential.potential`, `Exp3Potential.updatedWeight`,
  `Exp3Potential.updatedPotential_sub_potential_eq_sum_weight_mul_exp_sub_one`,
  and `Exp3Potential.potentialProcess_telescope_sum_range`.
- the deterministic FTRL one-step surface:
  `FTRL.linearLoss`, `FTRL.finiteSimplex`,
  `FTRL.regularizedObjective`,
  `FTRL.linearLoss_sub_le_regularizer_sub_div_of_isRegularizedMinimizer`,
  and `FTRL.linearLoss_sub_le_regularizer_sub_div_of_simplex_minimizer`.
- the deterministic finite-simplex Tsallis regularizer surface:
  `Tsallis.powerSum`, `Tsallis.entropy`,
  `Tsallis.negEntropyRegularizer`,
  `Tsallis.powerSum_nonneg_of_finiteSimplex`, and
  `Tsallis.negEntropyRegularizer_wellDefined_on_finiteSimplex`.
- the finite-union probability wrapper for the wrong-mean event:
  `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`.
- the final elementary probability assembly from wrong commit to the finite
  guarded wrong-mean-event sum:
  `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`.
- the abstract pairwise-tail consumer wrapper from wrong commit to a finite sum
  of non-best pairwise tail bounds:
  `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`.
- the if-zeroed nonbest pairwise-tail consumer wrapper from wrong commit to a
  finite sum whose selected best-arm summand is forced to zero:
  `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`.
- the filtered-sum pairwise-tail consumer wrapper from wrong commit to an
  explicit filtered finite sum over non-best arms:
  `ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail`.
- a theorem-card-only wrong-commit probability design reducing non-best commit
  to empirical-mean comparison events, awaiting argmax wiring, actual pairwise
  tail proofs, filtration, and final ETC theorem assembly.
- a fixed-commit ETC empirical-mean measurability wrapper under an explicit
  Rat division-by-constant measurability contract, before deciding the Mathlib
  division import/wrapper route.
- a Rat division-by-constant measurability wrapper under
  `[MeasurableSingletonClass Rat]`, before consuming it to remove the explicit
  `hdiv_const` argument from the ETC empirical-mean theorem.
- a no-`hdiv_const` fixed-commit ETC empirical-mean measurability theorem that
  consumes the Rat wrapper under `[MeasurableSingletonClass Rat]`.

The compiled local layer does not yet cover:

- full policy predictability, conditional reward-law transfer, posterior
  kernels, infinite action/reward trajectory laws, and conditional expectation
  contracts;
- most probability theorem contracts beyond action equality events, indicators,
  finite sums, local quantities, finite-sum Bochner wrappers, the Real-valued
  expected-regret pull-count decomposition, and lower-integral canaries;
- sub-Gaussian, Hoeffding, Chernoff, variance, or martingale tail proofs;
- probability-facing pull-count decompositions beyond the explicit Bochner/Real
  integrability contract;
- Rat-valued expected regret and algorithm-specific expected-regret theorem
  routes beyond the current Real-valued Bochner decomposition and
  `ENNReal.ofReal` lower-integral surrogate;
- imported or ported LML UCB/ETC/Thompson theorems;
- EXP3 estimator/log/regret, KL-UCB, Tsallis-INF/FTRL, OFUL/LinUCB, BwK,
  pure exploration, RL/MDP final theorem surfaces;
- full Markdown/LaTeX exports for closed textbook theorems.

## Distance By Layer

The table below is an engineering audit, not a mathematical impossibility
claim.  `compiled` means the local Lean gate proves it now.  `carded` means the
source or retrieval route exists.  `missing` means the route still needs leaf
statements, imports, or local proofs.

| Layer | Current status | What remains |
| --- | --- | --- |
| Harness and memory workflow | mostly compiled/tooling | add richer population operations and reviewer audits |
| Source/paper/scenario map | broad card coverage | keep current with new papers and check every source route |
| Proof weapons | carded | must be decomposed per task; not proof certificates |
| Finite bookkeeping and model invariants | first Mathlib wrapper layer, best-arm dominance, gap nonnegativity, no-explicit-`hgap` lower-integral bound, deterministic count-bound scaffold, Nat-count adapter, and uniform Nat adapter compiled | reviewer-check before choosing ETC-specific counts or Bochner/integrability |
| Regret decomposition | deterministic pull-count identity and Real-valued Bochner expected-regret pull-count identity compiled | Rat-valued expectation, probability-facing expectation APIs, and algorithm-specific regret decompositions still need separate contracts |
| Measure/probability foundation | event/measurability, finite action/reward history product measurability, pair-coordinate trace-prefix measurability, pair-history successor extension measurability, singleton-history filtration, policy/state measurability, policy-generated action trace coordinate measurability, reward-kernel selected-measure measurability, posterior-kernel selector measurability, Thompson posterior-action identity ledger consumers, finite/countable posterior best-action measurability wrapper, one-step policy/reward Markov-kernel composition, selected-reward event and `Measure.map` marginal wrappers, kernel-level centered-reward law transfer, finite-prefix reward-history `partialTraj` assembly, finite-prefix action/reward pair trajectory kernels, one-step `partialTraj` next-coordinate marginal wrappers, the full-prefix frozen-extension `partialTraj` wrapper, explicit conditional-kernel integral and pushforward-map consumers, frozen-history-to-centered-target bridge, conditional-kernel frozen-past route for conditioning-measurable events/countable variables/finite reward histories, finite-history measurability hookup for coordinate-measurable reward prefixes and generated `History.historyFiltrationSucc`, finite action/reward pair-history frozen-past hookup under `[Countable Action]`, successor-extension decomposition of the generated conditional pair trace, `Measure.map_congr` pushforward form of that decomposition, map-law consumer specializations that discharge the frozen-past side condition from those hooks, action/reward pair-law marginalization into the reward-coordinate map-law consumer, generated-history/concrete trace-pair/projection-measurability/named finite-pair-trace specializations of that pair-law route, the partialTraj finite-pair-trace consumer and reusable next-pair projection adapter, the direct history-step next-pair reward-map adapter, the full finite-pair-trace reward-map adapter, the extension-map partialTraj consumer and extension-to-full-trace law adapter, the extension-map reward-map adapter, the pairmap-to-extension partialTraj law builder, the next-pair split-law builder, the action-freezing policy hookup for the split-law action side, the generated-history action-side hookup for visible finite pair histories, the shifted generated-trace source for pointwise policy generation, the generated-action actual/random-pair reward-law hookup through full finite-pair-trace law adapters and the conditional mean-zero route, the generated random-pair law source contract package, random-pair-to-actual-reward-map source conversion, plus centered-source regularity package and consumers, finite-sum Bochner wrappers, the Real-valued expected-regret pull-count decomposition, and lower-integral canaries compiled | pair/reward law construction, integrability source for the adaptive generated route, `partialTraj`/history-to-`condExpKernel` action/reward pair-law identification, Bayes-rule/regular-conditional posterior identification, posterior action-law construction/import, infinite trajectory laws, and full conditional-expectation contracts |
| Kernels/posteriors | reward-kernel contract, posterior-kernel contract, Thompson posterior-action identity ledger, finite/countable posterior best-action measurability wrapper, one-step policy/reward kernel composition, selected reward event and `Measure.map` marginal wrappers, kernel-level centered-reward law transfer, finite-prefix reward-history `partialTraj`, finite-prefix action/reward pair trajectory-kernel surfaces, one-step `partialTraj` next-coordinate marginal wrappers, the full-prefix frozen-extension `partialTraj` wrapper, the conditional-expectation partialTraj finite-pair-trace consumer, reusable next-pair projection adapter, direct history-step next-pair reward-map adapter, full finite-pair-trace reward-map adapter, extension-map reward-map adapter, and extension-to-full-trace law adapter, the pairmap-to-extension partialTraj law builder, the action-freezing policy hookup for the next-pair split-law action side, the generated-history action-side hookup for visible finite pair histories, the shifted generated-trace source for pointwise policy generation, the generated-action actual/random-pair reward-law hookup through full finite-pair-trace law adapters and the conditional mean-zero route, the generated random-pair source contract package, source-level canonical history-step pair-law consumer, random-pair-to-actual-reward-map source conversion, definitional source-level canonical history-step pair-law consumer, centered-source canonical pair-law consumer, definitional centered-source canonical pair-law consumer, and centered-source regularity package, explicit history-step conditional-kernel consumer surfaces, and reward-coordinate pushforward-map consumers compiled | conditional distributions, construction of the generated random-pair law source, `condExpKernel` reward-law identification, Bayes-rule posterior identification, posterior action-law construction/import, and Bayesian regret |
| Concentration/tails | independent and strongly adapted conditional Mathlib import wrappers, Chebyshev/evariance wrappers, finite union bounds, and abstract finite-horizon UCB bad-event summability compiled | UCB empirical-mean concentration instantiation, ETC pairwise reward-difference conditional instantiation polish, and asymptotic/series simplifications |
| UCB/ETC textbook routes | wrappers plus theorem cards, with abstract finite-horizon UCB bad-event summability, deterministic/event-level UCB confidence-radius consumers, finite-arm confidence bad-event union bound, confidence-event measurability, finite-horizon confidence-event union assembly, finite-horizon good-event gap and large-gap subset consumers, abstract upper/lower tail-budget consumption, absolute-deviation concentration-event adapter, finite-variance Chebyshev UCB tail producer, abstract centered empirical-mean sub-Gaussian UCB tail producer, square-root radius-budget wrapper, schedule-agnostic logarithmic radius wrapper, constant-scale finite-horizon tail-budget folding, textbook delta confidence-budget and large-gap score-max probability wrappers, selected-action single-time/finite-time-set large-gap delta bridges, concrete finite-arm confidence-score argmax wrappers, finite-time selected-count lower-integral budget wrappers, an all-horizon recursive pull-count budget wrapper, a threshold/suffix-shaped pull-count split, an abstract free-time budget consumer, a free-time cardinality consumer, selected-small pathwise and lower-integral pull-count budgets, selected-small/selected-large count decomposition, selected-large-count `T * delta` wrappers, recursive sample-count UCB count adapter, a source-count wrapper for history-derived sample counts, a history-action transfer wrapper, a generated-policy trace wrapper, an identity-policy concrete score-argmax generated-trace wrapper, a concrete textbook-radius split instantiation, a threshold-cardinality consumer, a half-gap threshold adapter, square/eight-proxy-log threshold consumers, a proxy-small threshold consumer, a sample-count threshold consumer, and a lower-bound-on-count consumer now compiled | concrete empirical-mean construction from reward histories, recursive adaptive UCB action trace, concrete proxy/count source from empirical rewards, and final regret; ETC expected-regret assembly remains separate |
| Thompson sampling | posterior-action ledger, canonical/reference samplers, posterior-invariance and recursive density transport, measurable environment-indexed trajectories, global uniform-reference recursive sampler coupling, premise-free actual-trajectory probability matching, finite-horizon Bayesian mean-regret decomposition, exact clipped-UCB score regularity, stationary reward-kernel arm-stream representation, all-time latent-stream trajectory support, and fixed-environment actual augmented-trajectory tails compiled; the pinned final LML declaration remains a theorem card | mix the pointwise tails through the augmented prior, build measurable clipped-confidence events and the two concentration expectation bounds, then close the final regret inequality |
| EXP3/adversarial | finite-action exponential-weights potential, importance-weighted conditional moments, generated exploration-mixed trajectory, predictable `[0,1]` feedback, finite-horizon Hedge/moment integration, the unoptimized expected predictable-regret theorem, deterministic parameter simplification, the large-horizon `4 sqrt(|A| T log|A|)` corollary, realized selected-loss expectation transport, and the all-horizon clipped-rate min bound compiled | high-probability regret, stochastic rewards, broader adversary models, and other EXP3 variants remain separate |
| Tsallis-INF/FTRL | generic finite-simplex FTRL one-step wrapper and finite-simplex Tsallis regularizer well-definedness compiled; paper/weapon cards for the rest | convexity/existence side conditions, rpow stability/penalty algebra, self-bounding conversion, learning-rate optimization |
| Linear/OFUL/LinUCB | local Gram PSD wrapper, Mathlib Schur-complement rank-one determinant-update wrapper, scalar regularized-Gram base wrapper, regularized-Gram quadratic-form/PSD wrapper, strict-positive qform wrapper, Mathlib PosDef determinant/IsUnit bridge, arbitrary regularized-Gram rank-one determinant recursion, one-step log-det increment wrapper, abstract finite-horizon log-det telescope, concrete Nat-prefix log-det telescope, scalar-base endpoint, first min/log determinant-growth consumer, clipped finite-sum log-upper handoff, finite-sum small-update log bridge, finite-sum small-update log-upper handoff, explicit-regularity small-update log-det raw-sum handoff, PosDef-inverse quadratic nonnegativity consumer, small-update log-det endpoint raw-sum handoff, terminal log-det upper-bound consumer, small-update terminal log-det raw-sum handoff, multiplicative determinant-upper consumer, small-update multiplicative determinant raw-sum handoff, prefix trace/radius bound, trace-average determinant consumer, AM-GM determinant trace bound, trace-average exp handoff consumer, scalar trace-average exp bound, dimension-cancelled trace-average exp consumers, standard logarithmic trace-average endpoint, generic small-update raw-sum handoff, dimension-scaled small-update raw-sum endpoint, dimension-cancelled small-update raw-sum endpoint, and small-update raw-sum logarithmic consumer compiled; paper/weapon cards for the rest | confidence ellipsoid, self-normalized tail |
| RL/MDP | scenario/paper cards only | finite kernels, Bellman recursion, occupancy measures, episode regret |
| Proof export | skeleton exists | exports must be generated from compiled theorem declarations |

## Textbook-Scope Completion Estimate

For the three current textbook/survey roots, ABRL has a broad map but not a
full proof library.

| Source root | Current coverage | Remaining proof strata |
| --- | --- | --- |
| Bubeck-Cesa-Bianchi 2012 | stochastic/adversarial routes and paper cards | UCB/EXP3 tails, lower bounds, minimax routes, final theorem exports |
| Lattimore-Szepesvari 2020 | main scenario tree and Mathlib routes | probability foundation, concentration chapters, ETC/UCB/MOSS/KL-UCB/linear proofs |
| Slivkins 2019/2024 | scenario atlas, Bayesian, Lipschitz, BwK, agents | Bayesian/posterior formalization, Lipschitz/metric trees, BwK and incentive proofs |

Pragmatic estimate: for the desired textbook-scale proof weapon library, the
current compiled Lean is under one tenth of the needed proof surface.  It is
useful because it sets stable harness rules and proves the first finite
bookkeeping leaves, but the major Mathlib-backed layers still need to be
imported, adapted, or proved.

## Required Next Milestones

1. Treat `ETC-EXPLOREARM-EQ-IFF-MOD` as the compiled modular selector helper
   for future ETC count theorems.
2. Treat `ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` as the compiled first-cycle ETC
   round-robin count scaffold.
3. Treat `ETC-ROUND-ROBIN-ADD-K-COUNT` as the compiled full-cycle extension
   recurrence for ETC pull counts.
4. Treat `ETC-ROUND-ROBIN-MUL-K-COUNT` as the compiled multiple-full-cycle ETC
   count theorem.
5. Treat `ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` as the compiled configured
   exploration-horizon count adapter.
6. Treat `ETC-EXPLORATION-REGRET-BOUND` as the compiled deterministic
   exploration-only ETC pseudo-regret scaffold.
7. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` as the compiled fixed-commit
   ETC trace boundary on the exploration prefix.
8. Treat `ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` as the compiled fixed-commit
   ETC trace boundary after the exploration horizon.
9. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` as the compiled
   exploration-prefix pull-count transfer for the fixed-commit ETC trace.
10. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` as the compiled
   configured exploration-horizon pull count for the fixed-commit ETC trace.
11. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND` as the
   compiled deterministic pseudo-regret scaffold for the fixed-commit ETC trace
   at the exploration horizon.
12. Treat `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` as the compiled
   one-step post-commit pull-count recurrence for the fixed-commit ETC trace.
13. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` as the compiled closed-form
   post-exploration suffix pull count for the fixed-commit ETC trace.
14. Treat `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` as the compiled
   non-commit-arm post-exploration pull-count stability corollary.
15. Treat `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` as the compiled
    commit-arm post-exploration pull-count corollary.
16. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` as the compiled
    reviewer-approved deterministic count-budget pseudo-regret scaffold for
    the fixed-commit ETC trace after the exploration horizon.
    The reviewer prompt was
    `reports/extended_pro_after_commitarm_suffix_count_candidate_prompt_2026-06-29.md`;
    the recorded answer is
    `reports/extended_pro_after_commitarm_suffix_count_response_2026-06-30.md`.
17. Treat `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` as the compiled
    reviewer-approved coarse uniform post-exploration suffix regret bound.  The
    reviewer prompt was
    `reports/extended_pro_after_suffix_budget_regret_candidate_prompt_2026-06-30.md`;
    the recorded answer is
    `reports/extended_pro_after_suffix_budget_regret_response_2026-06-30.md`.
18. Treat `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` as the compiled
    reviewer-approved fixed-commit post-horizon phase-split pseudo-regret
    equality. The reviewer prompt was
    `reports/extended_pro_after_coarse_suffix_regret_candidate_prompt_2026-06-30.md`;
    the recorded answer is
    `reports/extended_pro_after_coarse_suffix_regret_response_2026-06-30.md`.
19. Treat `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` as the compiled
    reviewer-approved phase-split exploration-plus-suffix-gap regret bound. The
    reviewer prompt was
    `reports/extended_pro_after_phase_split_regret_candidate_prompt_2026-06-30.md`;
    the recorded answer is
    `reports/extended_pro_after_phase_split_regret_response_2026-06-30.md`.
20. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` as the compiled
    reviewer-approved optimal-commit no-extra-suffix-regret equality. The
    reviewer prompt was
    `reports/extended_pro_after_gap_bestarm_candidate_prompt_2026-06-30.md`;
    the recorded answer is
    `reports/extended_pro_after_gap_bestarm_response_2026-06-30.md`.
21. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` and
    `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` as the current deterministic
    ETC boundary: if the commit arm is the selected best arm, the post-horizon
    trace and regret contribution are controlled.
22. Treat `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as the theorem-card-only
    bridge, not as a completed probability proof.
23. Treat `ETC-MEAS-COMMITARM-NE-BESTARM` as the first compiled wrong-commit
    event measurability canary.
24. Treat `ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT` as the compiled pure
    wrong-commit set-inclusion leaf.
25. Treat `ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET` as the
    compiled arbitrary-measure monotonicity wrapper.
26. Treat `ETC-MEAS-EMPMEAN-GE-EMPMEAN` as the compiled pairwise
    empirical-mean comparison-event measurability canary.
27. Treat `ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM` as the compiled
    finite existential wrong-mean event measurability wrapper.
28. Treat `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM` as the
    compiled finite-union probability upper-bound wrapper.
29. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS` as the compiled
    final elementary event-probability assembly wrapper.
30. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL` as the compiled
    abstract non-best pairwise-tail consumer wrapper.
31. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL` as the compiled
    if-zeroed nonbest pairwise-tail consumer wrapper.
32. Treat `ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL` as the
    compiled filtered-sum pairwise-tail consumer wrapper.
33. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` as the compiled
    deterministic Nat denominator-positivity leaf for fixed-commit ETC
    exploration counts.
34. Treat `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` as the
    compiled Rat denominator-positivity adapter for fixed-commit ETC
    exploration counts.
35. Treat `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO` as the
    compiled Rat nonzero-denominator adapter for fixed-commit ETC exploration
    counts.
36. Treat `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` as the compiled
    deterministic fixed-commit exploration-horizon empirical-mean definition
    and denominator rewrite.
37. Treat `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION` as the
    compiled numerator-measurability bridge for fixed-commit ETC empirical
    means under stochastic reward traces.
38. Treat `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST`
    as the compiled full empirical-mean measurability wrapper under an
    explicit Rat division-by-constant measurability contract.
39. Treat `RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON` as the compiled
    Rat division-by-constant measurability wrapper under
    `[MeasurableSingletonClass Rat]`.
40. Treat `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION` as the
    compiled no-`hdiv_const` empirical-mean measurability theorem consuming
    the Rat wrapper.
41. Treat `ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES` as the compiled
    coordinate-shaped empirical-mean measurability wrapper selected by
    Extended Pro after the no-`hdiv_const` theorem.
42. Treat `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER` as the compiled deterministic
    abstract commit-oracle argmax consumer for the wrong-commit event
    reduction.
43. Treat `ETC-COMMIT-ORACLE-PROB-WRAPPER` as the compiled oracle-specialized
    abstract pairwise-tail probability consumer selected by Extended Pro.
44. Treat `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL` as the compiled
    oracle-specialized filtered-sum pairwise-tail probability consumer selected
    by Extended Pro.
45. Treat `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL` as the compiled
    oracle-specialized if-zeroed nonbest pairwise-tail probability consumer
    selected by Extended Pro.
46. Treat `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY` as the compiled
    oracle-selected wrong-commit event measurability wrapper under direct
    composed choice measurability, selected by Extended Pro.
47. Treat `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE` as the compiled
    Mathlib-backed countable score-vector oracle-choice measurability wrapper
    selected by Extended Pro as an immediately compilable candidate.
48. Treat `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` as the compiled Mathlib
    Pi-space coordinate-to-vector empirical-mean measurability wrapper selected
    by Extended Pro.
49. Treat `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES` as the
    compiled coordinatewise empirical-mean-to-oracle-choice measurability
    composition wrapper selected by Extended Pro.
50. Treat `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` as the
    compiled coordinatewise empirical-mean-to-oracle-wrong-event measurability
    composition wrapper selected by Extended Pro.
51. Treat `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL` as the
    compiled concrete argmax-oracle filtered-sum pairwise-tail consumer wrapper.
    `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` is now compiled locally, packaging the
    fixed-commit ETC empirical-mean pairwise-tail assumption and its concrete
    argmax consumer.  `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` is also compiled
    locally as the positive-denominator bridge from empirical-mean comparison
    to fixed-horizon reward-sum comparison.  The tail contract itself is still
    not proved.  `TAIL-HOEFFDING-BOUNDED` is now compiled locally as the
    bounded-centered Hoeffding MGF source; `TAIL-SUBGAUSS-SUM`,
    `TAIL-SUBGAUSS-DIFF-SUM-IMPORT`, and `TAIL-COND-SUBGAUSS` are now compiled
    locally as Mathlib-backed sub-Gaussian finite-prefix tail wrappers, including the `ENNReal`
    event-probability shape for both independent and strongly adapted
    conditional routes.
    `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` is also compiled locally, producing
    `ETC.PairwiseEmpMeanTailContract` from explicit non-best-arm sub-Gaussian
    witnesses and event-subset hypotheses.  The generic event-shape adapter
    from ETC empirical-mean comparison to abstract fixed-horizon `sumRewards`
    tail events is also compiled locally.  `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET`
    now instantiates that implication with a concrete centered
    reward-difference finite-sum event, and
    `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` specializes the abstract
    producer to those summands.  `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT`
    packages the exact reward-law witness fields consumed by that producer.
    `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` fixes the exact
    exponential tail budget, and
    `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` connects that budget to the
    concrete argmax-oracle wrong-commit probability consumer.  The
    reward-law route then compiles the trace-coordinate independence transfer,
    the centered reward sub-Gaussian transfer, the bounded-reward Hoeffding
    source, the bounded-to-integrable source, the centered reward
    zero-integral source, the strong all-arm bounded-reward wrong-commit
    bound, the action-matched bounded-reward
    wrong-commit bound, the
    `ETC.BoundedRewardTraceSource` contract wrapper, and the fixed
    product-coordinate source theorem.  Downstream work now needs the
    fixed-commit wrong-commit probability bound connected to expected-regret
    assembly before starting final adaptive ETC theorem work.
    On the canonical reward-only conditional route,
    `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-AVERAGE-TAIL` now
    compiles the strictly-positive-denominator specialization from a centered
    successor sum tail to an aggregate average tail.  It does not provide an
    arm-wise empirical mean, a UCB/ETC confidence event, or a regret theorem;
    the `COND-EXPECT-REWARD` conversion-window and proof-obligation entries
    named by the retrieval index are absent from this worktree and must not be
    treated as current route evidence.
    The ETC fixed-product Bochner route now also has
    `ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET`: the public coordinate
    source contract is stated directly over `ETC.exploreArm`, with the former
    base commit arm eliminated from the theorem interface.  It is a compiled
    Real expected-regret theorem for the fixed product source, not a proof of
    the adaptive LML `Bandits.ETC.regret_le` target; action-dependent adaptive
    reward-law transport remains the precise missing technology.
    `ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE` now provides the narrow
    deterministic history-reconstruction prerequisite: two reward traces that
    agree below the exploration horizon have equal fixed-commit empirical means
    at every arm. It has no probability or regularity contract and does not
    establish a generated action trace or adaptive reward law.
    `ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION` now turns that fact into the
    shifted generated-action state contract: completing
    `finiteRewardHistoryOfTrace reward t` by zero after `t` reproduces the
    ambient empirical score when `spec.explorationPulls * K <= t + 1`. It still
    does not construct or prove equality of the finite-history policy action.
    `ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT` now completes that action
    layer: the measurable policy over completed reward histories generates
    exactly `ETC.explorationArgmaxAction` when exploration pulls are positive.
    The remaining blocker is strictly the action-dependent reward-law and
    conditional-law transport, not policy definition, score recovery, or action
    measurability.
    `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW` now proves the
    action-dependent full `partialTraj` law under the canonical Markov-kernel
    trajectory measure. The remaining transport is therefore specifically from
    that canonical kernel measure to the fixed-product or arbitrary adaptive
    environment surface, plus the model regularity identification required by
    the final theorem.
    `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN` now supplies
    the conditional sub-Gaussian MGF for successor rewards centered at the
    selected arm's finite-bandit model mean, under an explicit centered kernel
    law and selected-history variance ceiling. The remaining deficit is the
    construction/transport of the centered regularity contracts and the
    tail/regret assembly, not conditional-MGF plumbing.
    `ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL` now constructs the raw
    context-independent Markov reward kernel from per-arm probability laws and
    proves exact selected-measure equality.
    `ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF` now constructs its
    centered model-mean law from common bounded arm laws and directly proves
    the canonical successor conditional MGF at the Hoeffding proxy. Time-zero
    initial-law alignment and the full selected centered-reward finite-sum tail
    are now compiled by `ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL`.
    `ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-PAIRWISE-TAIL-CONTRACT` now removes the
    bounded-support premise from the canonical pairwise concentration layer:
    direct per-arm centered MGFs at one common proxy and exact model means
    construct the kernel law, initial/successor fixed-filtration witnesses, and
    the empirical-mean pairwise tail contract. This remains a `Rat` theorem and
    does not yet provide commit-fiber probability, per-arm regret consumption,
    external law transport, or exact LML tie semantics.
    `ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT` now additionally compiles the
    actual empirical-mean pairwise tail contract and finite-union wrong-commit
    probability under canonical `trajMeasure`, using exploration-prefix action
    and filtration equality rather than coordinate independence.
    `ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET` now closes the remaining
    canonical adapter: finite ENNReal-to-Real probability conversion,
    empirical-mean argmax/wrong-event measurability, finite-valued integrability,
    and the generated-action Real expected-regret theorem all compile. The
    external exploration-prefix law consumer now also compiles: the regret
    integrand factors through `m*K` rewards and `Measure.integral_map`
    transports the bound from equality of finite-prefix pushforwards. The new
    external conditional-law consumer derives that equality from the zeroth
    marginal and successor `condDistrib` laws through exploration, on an
    arbitrary sample space. The scheduled exploration-arm adapter now removes
    the local step kernel from that contract: callers provide only the initial
    arm law and conditional laws of the scheduled exploration arms. The
    remaining environment work is a concrete source or `IsAlgEnvSeq` bridge.
    The full action/reward-history consumer now closes the local conditioning
    coarsening that mirrors `IsAlgEnvSeq.hasCondDistrib_feedback`; the remaining
    seed-specific law step of reducing the action-dependent stationary kernel
    with exploration action a.e. equality is now compiled in dependency-light
    form. A direct newer-toolchain wrapper is optional integration work.
    The direct-MGF contract now compiles through canonical per-arm regret,
    exploration-prefix equality, generic initial/successor conditional laws,
    the scheduled exploration-arm external endpoint, and the LML-shaped full
    action/reward-history constant-law consumer and its action-dependent
    selected-kernel adapter. Dependency-light direct-MGF `Rat` law transport is
    therefore closed. Exact LML alignment next requires porting the remaining
    reward/model surface to Real and aligning argmax ties and exact pull-count/
    RHS semantics; a direct toolchain wrapper remains separate integration.
52. Extend the Mathlib-backed probability layer only with explicit
    measurable/integrable contracts.
53. Convert retrieval cards for sub-Gaussian tails into exact imported theorem
    packets and local wrappers.
54. Close one narrow textbook theorem end-to-end, likely a small UCB/ETC
   bookkeeping or concentration-dependent theorem.
55. Export that theorem to Markdown and LaTeX from compiled declarations.
56. Only then expand to TS, EXP3, Tsallis-INF/FTRL, OFUL, BwK, and RL/MDP final
   theorem branches.

## Non-Negotiable Leaf Discipline

Every new leaf must satisfy the local contract:

- decompose aggressively;
- target a lemma that fits within one lower-agent context window;
- specify more than the theorem: local APIs, imports, assumptions, intended
  proof route;
- treat persistent failure as mathematical signal;
- promote hidden regularity into reusable theorem contracts;
- do not frequently change the proof route without a reviewer-visible reason.

The point of the audit is not to lower ambition.  It is to prevent agents from
mistaking a broad tree for completed Lean mathematics.

## ETC Per-Arm RHS Update

The generic per-arm Bochner assembly compiles as
`ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob`.
It preserves `sum_a (r * gap a) * P(commit=a)` instead of charging the entire
wrong event by `maxGap`. The arm-specific canonical ENNReal commit-event bound
and its finite Real conversion now feed
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal`.
The proof substitutes the non-best bounds termwise and removes the best-arm
summand with `gap_bestArm`, without a union. External exploration-prefix
transport now also compiles: equality of finite prefix pushforwards gives equal
regret integrals and transfers the same per-arm RHS without full trajectory or
suffix laws. The initial marginal plus successor `condDistrib` consumer now
constructs that identity and pulls the integral back to the original sample
space. The scheduled exploration-arm per-arm adapter now compiles as well: it
uses the deterministic exploration step-kernel equality with `Context := Unit`
and preserves the same gap-weighted RHS. The full action/reward-history
constant-law adapter now compiles too, using generic conditional-law coarsening
and marginal extraction. Its action-dependent selected-kernel per-arm adapter
now closes the dependency-light bounded-Rat law chain. The canonical pairwise
concentration layer also accepts direct common-proxy arm MGFs without bounded
support. Its concrete commit-fiber probability, finite Real tail, and canonical
gap-weighted per-arm Bochner theorem now compile as well, without a max-gap
collapse or arm union. Its direct-MGF endpoint now also propagates through the
external conditional-law chain. The separate Real scalar regret/pull-count
leaf below closes the target-side bookkeeping mismatch. Downstream leaves now
also close kernel means, native Real concentration/constants, per-arm counts,
finite-prefix law transport, and scheduled conditional-law transport. The
remaining exact-route work is upstream field/tie alignment; a direct
newer-toolchain LML wrapper remains optional integration work.

## Real Mean-Regret Pull-Count Foundation

`REAL-MEAN-REGRET-PULLCOUNT` now compiles in
`BanditRLProof.RealMeanRegretPullCount`. It defines the exact-route Real gap as
`iSup mean - mean a`, defines finite-horizon Real regret, proves its
gap-times-pull-count identity, and proves the Bochner expected pull-count
identity under explicit per-arm pull-count integrability. It reuses the local
Mathlib-backed finite-sum and pull-count wrappers and assumes no probability,
kernel, reward law, concentration, or argmax semantics.

The downstream `REAL-KERNEL-REGRET-PULLCOUNT` leaf now also closes stationary-
kernel identity-integral specialization, including kernel-gap nonnegativity and
the kernel-facing Bochner pull-count equality. Downstream leaves now also close
the exact canonical per-arm producer and the cast-pushforward Real-kernel
finite-sum assembly. Later native Real product, prefix-law, and action-dependent
source leaves close the external selected feedback-law transport. Remaining
exact ETC work is horizon action equality and selector tie equivalence. If that
route fails, isolate its first action or tie-equivalence fact; do not mark
`LML-ETC-REGRET` as ported.

## Real ETC Expected Pull-Count Endpoint

`REAL-ETC-EXPECTED-PULLCOUNT` now compiles in
`BanditRLProof.Algorithms.ETCExpectedPullCount`. It proves finite-measure
integrability for the Real cast of each measurable `actionWithCommit` pull
count, integrates the deterministic suffix formula exactly, and exposes the
LML-shaped probability consumer `m + (n - K*m) * p`. This closes the counting
and Bochner integration half of the per-arm expected-count route.

## Exact Common-Sub-Gaussian ETC Per-Arm Endpoint

`ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT` now compiles in
`BanditRLProof.Algorithms.ETCExactSubGaussianTail`. On the existing canonical
generated-history model with `Rat` arm laws and Real centered MGFs, it proves
the exact proxy sum `2*m*sigma2`, the non-best threshold `m*gap`, the LML
exponent `exp (-m*gap^2/(4*sigma2))`, the corresponding commit-fiber bound,
and the full per-arm Real expected pull-count inequality. The zero-proxy case
is handled explicitly because Lean's division is total.

This closes the exact common-proxy constant arithmetic and its canonical
per-arm count producer. This leaf itself is not a native Real reward-kernel
theorem, but downstream leaves now provide the native Real product theorem,
kernel gaps, and external scheduled conditional-law transport. The remaining
route is the actual `IsAlgEnvSeq` field wrapper and upstream
`measurableArgmax` tie semantics, not a weaker exponent or another Rat leaf.

## Rat Arm-Law Pushforward Real-Kernel Exact Regret

`ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRatArmLawRealKernel`. It maps each Rat arm law to
Real, proves the resulting countable arm kernel is Markov, identifies its
identity-integral means and `iSup` gaps exactly with the cast model values, and
assembles the exact per-arm count inequalities into the full LML-shaped finite
sum for `realKernelRegret`. The best-arm summand is eliminated explicitly.

This closes kernel-gap alignment and finite-arm summation for the canonical
Rat-law route. The Real kernel here remains a cast pushforward with Rat sample
coordinates, but downstream native Real product and finite-prefix leaves now
close that separate law-transport gap. The precise remaining blocker is
mapping the actual upstream `IsAlgEnvSeq` fields and proving ETC
action/`measurableArgmax` tie equivalence.

## Native Real Empirical Mean, Argmax, And Count Surface

`ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT` now compiles in
`BanditRLProof.Algorithms.ETCRealEmpiricalMean`. It defines exploration
empirical means directly on `RewardTrace Real`, proves a deterministic finite
argmax maximality certificate, and proves that selector measurable from
timewise measurable rewards. The proof does not countabilize `Fin K -> Real`:
it rewrites a dynamically selected score as a finite indicator sum and then
proves the comparison fold measurable step by step. The resulting native Real
action instantiates both the exact expected pull-count identity and its
abstract commit-fiber probability-bound consumer.

This closes the local native Real algorithm/count surface, including explicit
keep-the-old-arm tie behavior. The subsequent canonical product-law, prefix,
and action-dependent source leaves supply native Real concentration and map the
upstream-shaped selected feedback laws. Upstream horizon action equality and
selector tie equivalence remain separate obligations.

## Native Real Infinite-Product Exact ETC Regret

`ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealInfinitePiTail`. For a Markov Real reward
kernel with a common centered sub-Gaussian proxy, it chooses a finite
identity-integral best arm and works under the action-matched law
`Measure.infinitePi (fun t => nu (ETC.exploreArm spec t))`. It proves the
native Real empirical-comparison event inclusion, coordinate independence and
MGF transport, exact `2*m*sigma2` proxy sum, single-arm
`exp (-m*gap^2/(4*sigma2))` commit bound, matching expected pull count, and
the complete LML-shaped finite sum for `realKernelRegret`. The `sigma2 = 0`
case is handled explicitly.

This closes canonical independent native Real concentration, count, kernel
gap, and regret assembly. The external finite-prefix transport below now
removes the canonical ambient-space restriction; upstream structure and
selector alignment remain explicit.

## Native Real External Prefix-Law Exact ETC Regret

`ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealPrefixLawTransport`. It proves that native Real
empirical means, commit, action, and horizon regret factor through the finite
`Fin (m*K)` reward prefix, transports the canonical exact theorem across an
equality of prefix pushforward laws, and permits an arbitrary external action
that agrees a.e. with the local action only through horizon `n`.

The strongest endpoint removes the abstract prefix-law premise as well. It
uses the generic finite reward-prefix uniqueness theorem with the scheduled
exploration-arm zeroth marginal and successor `condDistrib` laws, identifies
the resulting constant-kernel Ionescu-Tulcea trajectory with
`Measure.infinitePi` via projective-limit uniqueness, and concludes the full
external exact finite-sum regret bound. It requires no
`StandardBorelSpace Omega`, external-action measurability, full reward-trace
law equality, or infinite-horizon action equality.

The downstream source adapter below now constructs `hzero` and scheduled
successor `hcond` from action-selected full-history feedback laws. The only
remaining exact LML blocker is horizon action generation and tie alignment.

## Native Real Action-Dependent Source Exact ETC Regret

`ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealSourceAdapter`. Its endpoint accepts the
upstream `IsAlgEnvSeq` feedback-law shape directly: reward zero conditioned on
action zero through `Kernel.ofFunOfCountable`, and reward `i+1` conditioned on
the complete finite action/reward history plus action `i+1` through the
stationary action-selected kernel.

The proof freezes those kernels with the a.e. round-robin exploration action,
extracts the zeroth marginal, projects full pair histories to reward prefixes,
and invokes the compiled native Real exact theorem. It adds no
`StandardBorelSpace Omega`, full trajectory law, independence, or
infinite-horizon action equality.

The pinned LML source audit at commit
`19dc3ab132c2a7539f5944503d1114eac4c5bb74` confirms the exact field shapes.
The downstream least-encoded action leaf now closes the selector and
`hactionETC` assembly obligations; this source leaf should not be reopened.

## Native Real Least-Encoded Action Exact ETC Regret

`ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealArgmaxTie`. The local strict-improvement fold
is identified with Mathlib's first-occurrence `List.argmax`; combining
`index_of_argmax` with `idxOf_finRange` proves least-`Encodable.encode`
selection. A specialized `Nat.find` selector matching the pinned LML
definition is then proved equal to the fold.

The same module combines a.e. round-robin exploration, least-encoded commit at
`K*m`, and post-commit persistence into equality with the native Real ETC
action at every time. Its strongest endpoint consumes those action fields and
the upstream-shaped selected feedback laws and returns the exact finite regret
sum without a caller-supplied horizon action equality. No
`StandardBorelSpace Omega`, full law, independence, or stronger action premise
is introduced.

The downstream history-score source leaf now closes that finite-history score
mapping. The remaining direct LML blocker is symbol-level compatibility:
instantiate the actual `measurableArgmax` and `IsAlgEnvSeq` source fields. LML
remains card-only until that source/toolchain wrapper compiles.

## Native Real History-Score Source Exact ETC Regret

`ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealHistoryScore`. It mirrors inclusive finite-
history pull counts, reward sums, and empirical means, proves they equal the
trace quantities at `n+1`, and identifies the `K*m-1` history score with
`realEmpMeanAtExploration` under the round-robin exploration action law.

Its strongest endpoint accepts a source-shaped finite-history least-encoded
commit law and returns the same exact native Real finite regret sum. The proof
intersects all finite exploration action equalities a.e., rewrites the score
vector, and reuses the prior action/source endpoint. It adds no standard-Borel,
full trajectory-law, independence, local-score commit, or preassembled action-
equality assumption. Focused and external canary builds pass.

The remaining direct-port boundary is no longer mathematical score mapping.
The downstream local field compatibility layer now compiles; only a true
cross-toolchain import of the concrete LML symbols remains.

## Native Real LML Field Compatibility Exact ETC Regret

`ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealLMLCompat`. The proposition
`ETC.RealStationaryETCSequence` records exactly the measurable action/reward,
round-robin exploration, finite-history least-encoded commit, persistence, and
stationary selected-feedback laws consumed from the pinned source.

`ETC.regret_le_of_realStationaryETCSequence` projects those fields into the
history-score theorem and returns the exact finite-arm LML-shaped sum. It adds
no standard-Borel sample-space, full-law, independence, local-score, or
preassembled action-equality premise. Focused and external canary builds pass.

This is a local compatibility theorem, not an imported LML declaration. The
toolchain audit found ABRL on Lean/mathlib `v4.29.1`, while pinned LML commit
`19dc3ab132c2a7539f5944503d1114eac4c5bb74` uses Lean `v4.32.0-rc1` and
mathlib commit `9ca31d8b72cf8c317e49c301bfdbfbe91fc49136`. The only remaining direct
boundary is a repository-level toolchain/dependency decision and proof over the
actual upstream symbols.

## Native Real UCB History Index

`UCB-NATIVE-REAL-HISTORY-INDEX` now compiles in
`BanditRLProof.Algorithms.UCBRealHistoryIndex`. It replaces the placeholder or
deterministic-proxy score boundary with the pinned-source quantities:
`sumRewards/pullCount` and
`sqrt(2*c*log(n+1)/pullCount)` on each realized trace.

Inclusive finite-pair-history mean, width, score, and least-encoded selector
are proved equal to their trace versions at time `n+1`. The Real index action
is score-maximal and measurable from timewise measurable action/reward
coordinates. No probability law, MGF, filtration, independence, or positive
pull-count premise is hidden in this leaf; division is the totalized Real
operation used by the source before initialization behavior supplies positive
counts.

The pinned LML audit shows the next missing theorem is not another generic
confidence-radius wrapper. Its one-sided UCB tail proof first invokes
`prob_pullCount_prod_sumRewards_mem_le`; generic fixed-count peeling,
complete-stream law transport, and next-unused-coordinate reward consumption
now compile in the following leaves. The remaining source boundary is the
recursive UCB action on that stream space and its stationary/product measure
law before specializing one-sided tails and expected pulls.

## UCB Fixed-Count Peeling And Law Transport

`UCB-FIXED-COUNT-PEELING-LAW` now compiles in
`BanditRLProof.Algorithms.UCBFixedCountPeeling`. The module defines a latent
`Nat -> Fin K -> Real` arm stream, measurable fixed-prefix sums, and a
`FixedArmPrefixSource` whose key field is the pathwise equality
`sumRewards = armPrefixSum pullCount`. From that equality and
`pullCount_le_time`, the adaptive pair event is contained in the finite union
of fixed-count prefix events. The local Mathlib-backed outer-measure union
bound then gives the finite sum.

A second theorem assumes one `IdentDistrib` law for the complete latent stream
and obtains every fixed-count law by measurable composition with
`armPrefixSum`. This exactly isolates the mathematical role of pinned LML
`identDistrib_sum_range_snd` plus
`prob_pullCount_prod_sumRewards_mem_le`, without importing the incompatible LML
toolchain or hiding the law inside a concentration hypothesis.

The regularity contract is measurable source/canonical spaces and stream
coordinates, measurable pair event, and a decidable projected-count filter.
No probability measure, independence, MGF, filtration, or positive count is
needed for the compiled theorem. Its pathwise source premise is now discharged
by `UCB-ARM-STREAM-REWARD-SOURCE`; the process/product and index-tail
instantiations are recorded separately below.

## UCB Arm-Stream Reward Source

`UCB-ARM-STREAM-REWARD-SOURCE` now compiles in
`BanditRLProof.Algorithms.UCBArmStreamSource`. `rewardFromArmStream` reads the
selected arm's next unused latent coordinate. Induction on the horizon proves
that selected `sumRewards` is exactly `armPrefixSum` at the realized
`pullCount`, and the module packages this theorem into general measurable and
canonical `FixedArmPrefixSource` adapters plus direct peeling consumers.

The only regularity in the general adapter is measurable stream coordinates;
the canonical Pi stream space discharges that automatically. No action
measurability, probability measure, stationarity, independence, MGF,
filtration, or positive count is assumed. Retrieval evidence is pinned LML
`ArrayProbSpace.reward_eq` and `SumRewards.sumRewards_eq`, together with local
count/sum recurrences and the compiled peeling interface.

`UCB-ARM-STREAM-PROCESS-LAW` now compiles the recursive inclusive history,
round-robin/native-index action, next-unused reward trace, exact actual-history
invariant, measurable history/action/reward coordinates, canonical
double-product arm-stream measure, and actual-process peeling endpoint.
`UCB-ARM-STREAM-INDEX-TAIL` compiles the product coordinate laws, independent
centered MGF transport, positive adaptive-count peeling, actual random-width
event algebra, logarithmic finite-sum collapse, and both LML-shaped bounds
`1 / (n+1)^(c-1)`.

`UCB-ARM-STREAM-EXPECTED-PULLCOUNT` now compiles the deterministic threshold,
selected-large failure union, `2*constSum` summation, ENNReal lower-integral
bound, pull-count integrability, and the Real Bochner expected-count endpoint
`8*c*sigma2*log(n+1)/gap^2 + 2 + 2*(constSum c n).toReal`.

`UCB-ARM-STREAM-LML-REGRET` then rewrites expected `realKernelRegret` as the
finite gap-weighted sum of expected pulls, removes zero-gap arms, and compiles
the exact pinned LML RHS
`sum a, 8*c*sigma2*log(n+1)/gap a + gap a*(2+2*constSum.toReal)`.
Its regularity contract is `0<K`, `0<c`, nonzero common NNReal proxy, a Markov
Real arm kernel, and centered sub-Gaussian MGF witnesses for every arm. The
canonical mathematical route is closed. Literal upstream `IsAlgEnvSeq` symbol
import remains separate cross-toolchain work and is not claimed by this
canonical theorem.

`UCB-EXTERNAL-ACTION-LAW-LML-REGRET` now closes the generic external-process
adapter when the complete external action trace is `IdentDistrib` to the
canonical arm-stream UCB action. The compiled proof makes the canonical trace
and finite-horizon regret functional measurable, composes the law witness via
`IdentDistrib.comp`, transports the Bochner integral with
`IdentDistrib.integral_eq`, and reuses the exact theorem above. Its only new
contract is the complete action-trace law identity; it adds no external
probability-measure, separate integrability, reward-process, filtration, or
standard-Borel premise. At this layer, the remaining compatibility input is a
construction of that action-law witness or literal import on a compatible
toolchain.

`UCB-EXTERNAL-ARM-STREAM-SOURCE-LAW-LML-REGRET` is a compiled optional stronger
adapter.
Given a latent `ArmRewardStream` with complete law `IdentDistrib` to the
identity stream under `armStreamMeasure`, and a.e. equality of the external
action with recursive `armStreamAction` on that latent stream, the compiled
constructor derives the required complete action law and its consumer returns
the exact regret RHS. It uses `IdentDistrib.comp/of_ae_eq/trans` and derives
action a.e. measurability rather than assuming it separately. Pinned LML does
not require this external latent array law.

The source audit at commit `19dc3ab...` shows the faithful route is
`IsAlgEnvSeq.identDistrib_trajectory` against
`ArrayModel.isAlgEnvSeq_arrayMeasure`: transport the complete observable
action/reward pair trajectory, then project to actions. The compiled
`UCB-EXTERNAL-ACTION-REWARD-TRAJECTORY-LAW-LML-REGRET` leaf now performs this
measurable Pi/`Prod.fst` projection and returns the exact regret RHS.
`UCB-COMMON-ACTION-REWARD-CONDDISTRIB-LML-REGRET` now also compiles the missing
trajectory-uniqueness layer: common initial pair marginal and successor pair
`condDistrib` kernels determine both complete laws via finite-prefix transport
and Mathlib projective-limit uniqueness, then yield the exact regret RHS. The
canonical specialization now chooses the canonical initial pushforward and
regular conditional kernels internally, so callers only prove external-vs-
canonical initial and successor pair-law equalities. The remaining source gap
is deriving those equalities from actual upstream environment/action fields or
literal import, not trajectory uniqueness, canonical law-bundle construction,
or reconstruction of independent unused-arm arrays.
## UCB IsAlgEnvSeq Split-Law Leaf

The local UCB route now compiles from the four pinned `IsAlgEnvSeq`-shaped law
surfaces rather than a preassembled observable pair law. Initial and successor
action/feedback laws are composed with Mathlib `compProd`; complete trajectory
uniqueness and the exact regret sum then follow. This closes local split-to-
joint law assembly. Literal LML symbols remain unimported, and the next honest
gap is proving those four fields from a concrete upstream sequence under a
compatible toolchain.

## Thompson Recursive Finite-History Density Leaf

`Thompson.finitePairHistory_map_eq_withDensity` now compiles in
`ThompsonAlgorithmDensityProcess`. From LML-shaped initial and successor
action/feedback conditional laws plus pointwise action-law absolute
continuity, it proves the actual inclusive finite pair-history law is the
reference law weighted by the recursive initial/policy RN density. The proof
uses Mathlib `condDistrib`, `compProd`, kernel RN derivatives, and
`withDensity`; it no longer assumes RN densities are pointwise finite.

This closes the local counterpart of pinned LML
`IsAlgEnvSeq.hasLaw_history_withDensity`. The downstream conditional-process
source now applies it under `condDistrib id env mu`, derives the Bayes
conditional-history density law, and closes finite-prefix Thompson probability
matching. `ConditionalHistoryAlgorithmDensitySplitSource` now constructs that
source from the four initial/successor action/feedback law families by gathering
the time-indexed fields with `ae_all_iff` and applying the local split-law
assembler. The next honest gap is one concrete recursive TS/reference
trajectory producer for those four fields. Global sampler coupling, regret
decomposition, concentration, and final Thompson regret remain open.

## UCB Local Field Compatibility Theorem

`UCB.RealStationaryUCBSequence` and
`UCB.regret_le_of_realStationaryUCBSequence` now compile. This is the faithful
local theorem-level endpoint: the pinned measurability and split law fields are
bundled, the canonical process supplies a witness, and arbitrary bundle
instances inherit the exact finite-arm UCB bound. The route is not an imported
LML proof. The remaining gap is exclusively a concrete producer using actual
upstream symbols or a common-toolchain import.

## Thompson Stationary Empirical-Mean Tail Transport

`TS-STATIONARY-EMPIRICAL-MEAN-TAIL-TRANSPORT` is now compiled in
`ThompsonStationaryReward`. The route removes the zero-pull fiber, integrates
the fixed-environment adaptive-count tails through the augmented prior with
Mathlib `Measure.compProd_apply`, specializes to the clipped-UCB square-root
radius, evaluates the finite exponential count sum, and transports the result
through `MeasurableEquiv.prodAssoc.symm` onto the left-associated canonical
trajectory measure used by `TS-DECOMP`.

For every fixed arm and horizon, both lower- and upper-confidence failure
events are bounded by `(n : ENNReal) * ENNReal.ofReal delta`. The contract is a
probability prior, Standard Borel environment, finite nonempty arms, a Markov
stationary reward kernel, measurable mean, pointwise centered
`HasSubgaussianMGF`, nonzero variance proxy, and `0 < delta <= 1`. This closes
prior mixing and decomposition-shape transport. It does not close finite
arm/time unions, either clipped-score expectation, or final Bayesian regret;
those failures belong to `TS-CLIPPED-UCB-CONCENTRATION-EXPECTATIONS`.

## Thompson Selected-Arm Horizon Lower Tail

`TS-STATIONARY-SELECTED-ARM-HORIZON-LOWER-TAIL` is now compiled. Its canonical
endpoint accepts a measurable `selectedArm : Env -> Fin K` and bounds the event
that some `t < n` has positive selected-arm count and lower-confidence failure
by `((n - 1 : Nat) : ENNReal) * ENNReal.ofReal delta`.

The proof rewrites actual trajectory rewards to the latent arm stream a.e.,
maps each bad time to its realized pull count, and unions only the prefix events
for `k in Finset.Icc 1 (n - 1)`. This preserves the pinned LML constant; unioning
the existing fixed-time `t * delta` bounds would not. Selected-arm measurability,
prior mixing, and product-associativity transport are discharged locally. Its
best-action expectation consumer now compiles; the next leaf is the
selected-action clipped-UCB-minus-mean expectation bound.

## Thompson Best-Action Clipped-UCB Expectation

`TS-CLIPPED-UCB-BEST-ACTION-EXPECTATION` is now compiled. On the stationary
canonical augmented trajectory measure, the integral of
`sum_{t<n} (mean(env,bestAction env) - clippedUCB(bestAction env,t))` is at most
`(u - l) * (n - 1) * n * delta`, matching the first concentration expectation
in pinned LML `BayesRegretTS`.

The proof splits over the compiled selected-arm horizon event. Its complement
makes every summand nonpositive; on the event, the mean and clipped score range
contracts bound every summand by `u-l`. The ENNReal event bound is converted to
`Measure.real` without weakening constants. The remaining concentration gap is
the selected-action clipped-UCB-minus-mean expectation, which needs a finite-arm
horizon upper event and the deterministic clipped-score sum inequality.

## Thompson Selected-Action Expectation And Final Bound

`TS-CLIPPED-UCB-CONCENTRATION-EXPECTATIONS` and the stationary `TS-FINAL` route
are now compiled. `finset_sum_comp_pullCount` reindexes selected-time sums by
arm and realized pull number; `sum_clippedUCB_action_sub_mean_le` gives the
pathwise square-root bound. The all-arm horizon upper event is count-collapsed
before the arm union, so its cost is exactly `K * (n-1) * delta`. Splitting the
canonical integral yields the pinned second expectation bound.

The general-`delta` theorem then joins both expectations through the compiled
recursive Thompson decomposition. Specializing `delta = 1/n^2` proves
`(2*K+1)*(u-l) + 8*sqrt(sigma2*K*n*log n)` in
`stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le`.
Contracts are a probability prior, Standard Borel nonempty environment, finite
nonempty arms, a stationary Markov reward kernel, measurable bounded means and
best action, pointwise centered `HasSubgaussianMGF`, and nonzero `sigma2`.
This is a compiled local stationary theorem, not a literal LML import or a
nonstationary/contextual/RL result; broader routes require explicit adapters.

## EXP3 Conditional Moment Transport

`EXP3-CONDITIONAL-MOMENT-TRANSPORT` now compiles in
`BanditRLProof.Exp3ConditionalMoments`. It packages a normalized nonnegative
finite action vector as a finite Dirac probability measure and proves that an
actual history-adaptive `condDistrib` law transports measurable integrable
history/action scores to finite conditional weighted sums. The specialized
consumers give armwise importance-weighted unbiasedness and exact mixed-loss
and mixed-square Bochner-integral identities.

The proof is Mathlib-backed through
`condDistrib_ae_eq_iff_measure_eq_compProd`, `integral_map`,
`Measure.integral_compProd`, and finite Dirac integral rules, then reuses the
compiled deterministic EXP3 moment identities. Its explicit contracts include
finite ambient measure, Standard Borel action regularity, a Markov policy equal
a.e. to the finite action law, the actual conditional distribution equality,
strictly positive supported probabilities, and score measurability/integrability.
Because the ambient measure is only finite, the equalities are unnormalized
integral identities unless a probability-measure instance is supplied.
The downstream generated-process leaf now supplies the policy and conditional
law premises; score regularity and finite-horizon moment assembly now compile
downstream. The integrated expected-regret and large-horizon tuned square-root
consumers, realized selected-loss expectation adapter, and uniform-horizon
clipped-rate theorem also compile on this EXP3 route.

## EXP3 Generated Action Process

`EXP3-GENERATED-ACTION-PROCESS` now compiles in
`BanditRLProof.Exp3ActionProcess`. A measurable family of normalized finite
probability vectors is converted into a finite-Dirac Markov kernel. Composing a
finite history measure with that kernel produces a canonical joint
history/action measure whose first marginal is the supplied history law and
whose sampled action `condDistrib` is a.e. the generated policy. The joint
measure is finite for a finite history measure and is a probability measure
when the history measure is a probability measure.

The proof establishes kernel measurability from finite sums of measurable
coordinate probabilities, obtains Markovness from the pointwise distribution
contract, and uses Mathlib `condDistrib_ae_eq_iff_measure_eq_compProd` for the
law identification. Canonical armwise, mixed-loss, and mixed-square wrappers
then consume `EXP3-CONDITIONAL-MOMENT-TRANSPORT` without external policy or law
assumptions. The downstream score-regularity leaf now also removes the explicit
score measurability and integrability premises. Recursive finite-horizon
trajectory generation, expectation assembly, the unoptimized expected-regret
endpoint, its large-horizon tuned square-root consumer, realized selected-loss
transport, and uniform-horizon clipped-rate theorem now compile downstream.

## EXP3 Score Regularity

`EXP3-SCORE-REGULARITY` now compiles in
`BanditRLProof.Exp3ScoreRegularity`. Its
`BoundedMeasurableLossWithProbabilityFloor` contract records `epsilon > 0`,
`epsilon <= prob(history, action)` on the finite support, measurable supported
loss coordinates, and supported losses in `[0,1]`. The module proves
measurability of the armwise importance-weighted score and both mixed scores,
with pointwise norm bounds `1/epsilon`, `1/epsilon`, and `(1/epsilon)^2`.

`Integrable.of_bound` turns those bounds into generated `compProd`-law
integrability. Three final wrappers feed the resulting positivity,
measurability, and integrability witnesses into `Exp3ActionProcess`, so callers
no longer supply `hprob`, `hscore`, or `hIntegrable`. Root import and external
integrability/premise-free mixed-square canaries compile. This remains a
one-round regularity result, but its downstream score-driven recursive
trajectory and its concrete sampled importance-weighted score instantiation now
compile. The generated scalar-feedback law transport, finite-horizon moments,
integrated expected-regret endpoint, large-horizon tuned square-root consumer,
realized selected-loss transport, and uniform-horizon clipped-rate theorem now
compile downstream.

## EXP3 Exploration-Mixed Recursive Trajectory

`EXP3-EXPLORATION-MIXED-RECURSIVE-TRAJECTORY` now compiles in
`BanditRLProof.Exp3RecursiveTrajectory`. For any measurable cumulative score on
inclusive finite action/loss histories, it defines positive exponential
weights, normalizes them over a nonempty finite arm set, and mixes the result
with the uniform distribution. The resulting probability coordinates are
nonnegative, sum to one, are measurable in finite history, and have the
pointwise floor `gamma / arms.card` when `0 <= gamma <= 1`; `gamma > 0` makes
that floor strictly positive.

The module packages these laws as `MeasurableFiniteActionDistribution`, builds
an exploration-mixed `Thompson.HistoryAlgorithm`, and uses the existing
Mathlib-backed Ionescu-Tulcea trajectory layer to construct the complete
environment-indexed action/loss process. Its endpoint theorem identifies every
successor action's `condDistrib` given the finite trajectory prefix with the
explicit finite action kernel. Root import and external score, floor, kernel,
and full conditional-law canaries compile.

Regularity is explicit: nonempty finite support; measurable action, loss, and
environment spaces with measurable action singletons; measurable supported
score coordinates; `0 <= gamma <= 1`; nonempty action/loss targets for
trajectory construction; Standard Borel environment/action/loss spaces and a
finite prior for the conditional-law endpoint. Its downstream sampled-score
module now closes the arbitrary-score boundary, and its predictable-moment
consumer now compiles finite-horizon integral sums. The integrated expected
EXP3 regret endpoint and large-horizon eta/gamma square-root optimization also
compile downstream; the realized selected-loss transport and uniform-horizon
clipped-rate theorem compile as well.

## EXP3 Sampled History Score Recursive Trajectory

`EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY` now compiles in
`BanditRLProof.Exp3SampledHistoryScore`. The Real-valued inclusive pair history
is restricted measurably to its previous prefix. At time zero the score uses
the initial action law; at each successor it adds the newly observed scalar
loss divided by the exploration-mixed probability generated from the prior
score and prefix. `sampledHistoryScore_zero` and
`sampledHistoryScore_succ` expose these exact equations.

Structural induction proves every supported score coordinate measurable, so
the generic trajectory layer can be instantiated without an external
`score/hscore`. The module exposes the concrete probability floor, stochastic
history algorithm, complete environment-indexed trajectory kernel, Markov
instance, and `sampledImportanceWeightedTrajectoryMeasure_condDistrib_action`,
which identifies every successor action law with the finite action kernel
computed from the recursively accumulated sampled score. Root import and
external recursive-equation and full conditional-law canaries compile.

Regularity contracts are Real-valued observed feedback; measurable action
singletons and decidable action equality; nonempty finite arms; `0 <= gamma <=
1`, with `gamma > 0` for strict downstream positivity; a measurable history
environment; Standard Borel environment/action; and a finite prior. Eta
positivity and `[0,1]` loss bounds are deliberately absent from process
construction and remain downstream regret contracts. Failure policy: this
sampled-score module alone returns only a sampled scalar; the downstream
predictable-adversary module now closes that law boundary.

## EXP3 Predictable Adversary

`EXP3-PREDICTABLE-ADVERSARY` now compiles in
`BanditRLProof.Exp3PredictableAdversary`. `Exp3.PredictableLossVector` records
jointly measurable initial and finite-history successor loss vectors selected
before the current action, together with pointwise `[0,1]` bounds. Its
`environment` uses `Kernel.deterministic`; the initial and successor feedback
apply theorems reduce exactly to Dirac measures at the chosen coordinates.

`trajectoryMixture_condDistrib_action_given_environment_history` lifts a
common fixed-environment history/action law through a finite prior while
retaining the environment in the conditioning variable. The concrete theorem
`sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment`
therefore identifies the sampled EXP3 action law given `(Env,prefix)` with the
same exploration-mixed policy, comapped along the prefix projection. The route
uses measurable event sections, `Measure.ext_prod`, Tonelli through
`Measure.lintegral_compProd`, and the canonical fixed-environment trajectory
law. Root import, module/root builds, external declaration and Dirac canaries,
and `Tests.Basic` compile. Regularity is pre-action joint measurability,
pointwise `[0,1]`, measurable action singletons and decidable equality,
nonempty finite arms, `0 <= gamma <= 1`, Standard Borel environment/action,
and a finite prior. Failure policy: the next leaf must combine these two law
surfaces with the existing one-round estimator identities and prove the needed
roundwise measurability/integrability; no expected-regret claim is available.

### EXP3 predictable observed moments

`EXP3-PREDICTABLE-OBSERVED-MOMENTS` now compiles in
`BanditRLProof.Exp3PredictableMoments`. The module transports the canonical
prefix/next-pair law through an environment prior, identifies initial and
successor reward coordinates with selected predictable losses almost surely,
packages the `(Env,prefix)` sampled policy and its positive `gamma / |arms|`
floor, and proves observed-scalar armwise first-moment unbiasedness together
with the exact probability-mixed estimator-square moment. It reuses
`Exp3ConditionalMoments`; no integrability premise remains at the public
endpoint. Contracts are predictable jointly measurable `[0,1]` losses,
nonempty finite arms, `0 < gamma <= 1`, measurable action singletons,
decidable equality, Standard Borel environment/action, a finite prior, and a
supported comparator. Its downstream finite-horizon consumer now compiles;
these remain moment identities rather than a potential inequality, optimized
bound, or regret theorem.

### EXP3 predictable finite-horizon moments

`EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS` now compiles in
`BanditRLProof.Exp3PredictableMoments`. It exposes uniform actual-time
probability and predictable-loss surfaces, including `t = 0`, proves observed
and latent score integrability under the finite prior mixture, transports the
initial and successor moment identities to the common full trajectory law, and
uses `ExpectationBochnerSums.integral_finset_sum` to sum both identities over
`t < horizon`; this includes `t = 0` when `0 < horizon`. Contracts remain jointly measurable predictable
`[0,1]` losses, nonempty finite arms, `0 < gamma <= 1`, measurable singleton
actions with decidable equality, Standard Borel environment/action, finite
prior, and supported comparator; no positivity assumption on `eta` is used.
Failure policy: this is not the pathwise sampled-score/Hedge inequality,
exploration-bias estimate, optimized parameter choice, or final EXP3 regret.

## EXP3 Sampled-Score/Hedge Join

`EXP3-SAMPLED-HEDGE` now compiles in `BanditRLProof.Exp3SampledHedge`.
The concrete actual-time observed estimator is packaged as
`sampledTrajectoryObservedLoss`. Structural induction proves that the
inclusive `sampledHistoryScore` through `n` is exactly Hedge
`cumulativeLoss` at `n + 1`. The successor Hedge distribution is then
identified with `normalizedHistoryDistribution` of that score, and the
actual trajectory probability is rewritten as its explicit
`(1 - gamma) q + gamma / |arms|` exploration mixture.

The endpoint `sampledHistoryScore_hedge_regret_le` is a concrete pathwise
finite-horizon second-order Hedge inequality with the comparator cumulative
term exposed as the sampled score. Contracts are nonempty finite arms,
decidable equality, `eta > 0`, `0 <= gamma <= 1`, comparator membership, and
nonnegative observed scalar losses on the finite prefix. No measurable-space,
prior, integrability, or probability-law premise is needed. Retrieval is
`LOCAL-LEAF-EXP3-HEDGE-DETERMINISTIC-REGRET`,
`LOCAL-LEAF-EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY`,
`LOCAL-LEAF-EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS`, Mathlib finite sums and
order/exponential algebra, the EXP3 paper/textbook cards, and the
inspiration-only weapon card. Root import and a full external theorem canary
compile. Its finite-horizon a.e. predictable reward support,
pure-vs-explored distribution bias, integration, expected-regret, tuned
square-root, realized selected-loss, and uniform-horizon consumers now compile
downstream. Failure policy: this leaf alone remains pathwise and must not be
reported as an expected-regret theorem.

## EXP3 Predictable Hedge Almost-Sure Endpoint

`EXP3-PREDICTABLE-HEDGE-AE` now compiles in
`BanditRLProof.Exp3PredictableHedge`. The module rewrites the observed reward at
time zero and every successor to the selected coordinate of the predictable
`[0,1]` loss vector, derives reward nonnegativity almost surely, and uses
`ae_all_iff` to place all `t < horizon` facts on one common full-trajectory
event. On that event the compiled pathwise sampled-Hedge theorem applies
without an external `hreward_nonneg` premise.

Public endpoints are
`sampledPredictableTrajectoryMeasure_hedge_regret_le_ae` for any horizon and
`sampledPredictableScoreHedge_ae` with the comparator cumulative estimator
exposed as `sampledHistoryScore`. Contracts are predictable jointly measurable
`[0,1]` losses, nonempty finite arms, measurable-singleton decidable actions,
Standard Borel environment/action, a finite prior, `eta > 0`,
`0 <= gamma <= 1`, and comparator membership. Gamma positivity, probability
normalization of the prior, and integrability are not needed for this a.e.
endpoint. Retrieval uses the sampled-Hedge, predictable-observed-moment, and
finite-horizon-moment local cards, Mathlib measure/kernel/finite-sum APIs, and
the EXP3 paper/textbook route; the weapon card remains inspiration only.
Failure policy: this is not an integrated regret theorem. Next prove the
pure-Hedge `q` versus explored `p` bias and second-moment inequalities plus
integrability, then integrate before optimizing eta/gamma.

## EXP3 Exploration Bias

`EXP3-EXPLORATION-BIAS` now compiles in
`BanditRLProof.Exp3ExplorationBias`. The module unfolds the concrete sampling
mixture `p_t = (1-gamma)q_t + gamma/|arms|`, proves
`q_t(a) <= p_t(a)/(1-gamma)`, and uses it to compare the pure-Hedge estimator
square with the actual probability-mixed estimator square. A separate
`[0,1]` argument bounds actual predictable loss by pure loss plus `gamma`.
`sampledTrajectory_finiteHorizon_explorationBias_secondMoment` sums both
inequalities over an arbitrary `Finset.range horizon`.

Contracts are a nonempty finite arm set, decidable equality, measurable spaces
needed by `PredictableLossVector`, and `0 <= gamma < 1`; eta positivity, a
prior, Standard Borel structure, probability normalization, integrability,
and a comparator are not used. Retrieval uses the predictable-Hedge,
sampled-Hedge, finite-horizon-moment, and importance-weighted local cards plus
Mathlib finite-sum/order algebra and the EXP3 paper/textbook route; the weapon
card is inspiration only. Status is compiled with root import and a full
external finite-horizon canary. Failure policy: this remains pathwise algebra,
not expected regret by itself. Its adaptive pure-q transport, integrability,
and expected-regret consumer now compile; its tuned square-root consumer also compiles.

## EXP3 Predictable Expected Regret

`EXP3-PREDICTABLE-EXPECTED-REGRET` now compiles in
`BanditRLProof.Exp3PredictableIntegration`. Its public endpoint
`sampledPredictable_expectedRegret_le` bounds the expected finite-horizon
exploration-mixed predictable loss minus any supported comparator by
`log |arms| / eta + eta/(1-gamma) * |arms| * horizon + gamma * horizon` on the
actual generated trajectory law.

The Lean-facing route adds a cross-weight estimator with sampling weights `p`
and predictable Hedge weights `q`, proves the finite-sum identity
`E_p[q dot hat-loss] = q dot loss`, transports it through the identified
conditional action law, constructs measurable pure-Hedge sources at every
time, aggregates their first moments, integrates the a.e. Hedge inequality,
and applies the exploration-bias and exact second-moment bounds. Imports and
local APIs are `Exp3ExplorationBias`, `normalizedHistoryDistributionSource`,
the conditional-moment transport, generated reward a.e. identification,
`IntegrabilitySums.integrable_finset_sum`, and
`ExpectationBochnerSums.integral_finset_sum`.

Contracts are a probability prior, Standard Borel environment and action,
measurable action singletons, decidable equality, nonempty finite arms,
jointly measurable predictable `[0,1]` losses, a supported comparator,
`eta > 0`, and `0 < gamma < 1`. There is no independence, stationarity,
oblivious-adversary, concentration, or supplied-integrability assumption.
Retrieval evidence is the compiled exploration-bias, predictable-Hedge,
finite-horizon-moment, conditional-moment, and score-regularity local cards;
Mathlib measure/kernel/finite-sum/order APIs; the EXP3 paper and textbook
cards; and the inspiration-only weapon card. Status is `leanCompiled`, root
imported, with a full external theorem canary. Failure policy: this is a real
expected predictable-regret theorem, but not the optimized classical EXP3
corollary by itself; its tuned square-root consumer now compiles downstream.
Its left side is the `p_t`-mixed predictable loss; the separate realized
selected-loss expectation consumer and all-horizon clipped-rate consumer now
compile. Preserve this reusable p-mixed endpoint when extending to broader
adversary or high-probability routes.

## EXP3 Tuned Expected Regret

`EXP3-TUNED-EXPECTED-REGRET` now compiles in
`BanditRLProof.Exp3ExpectedRegret`. The deterministic theorem
`expectedRegretBudget_le_four_mul_gamma_mul_horizon` reduces the unoptimized
budget to `4*gamma*T` under `eta=gamma/K`, `gamma<=1/2`, and
`K*log K<=gamma^2*T`. The final generated-trajectory theorem
`sampledPredictable_expectedRegret_le_four_mul_sqrt` instantiates
`gamma=sqrt(K*log K/T)` and `eta=gamma/K`, yielding
`4*sqrt(K*T*log K)`.

Local APIs/imports are `Exp3PredictableIntegration`, the compiled unoptimized
endpoint, `Real.sqrt_pos`, `Real.sqrt_le_iff`, `Real.sq_sqrt`,
`Real.sqrt_div'`, field simplification, ring normalization, and Nat/Real cast
transport. The proof is deterministic after the expectation theorem: bound
the log term by `gamma*T`, use `gamma<=1/2` for the second-order denominator,
then normalize the square-root expression.

Contracts retain the prior probability, Standard Borel, predictable `[0,1]`,
finite-arm, and supported-comparator assumptions, and add `2<=K`, `0<T`, and
the large-horizon regime `4*K*log K<=T`. There are no new law, independence,
stationarity, concentration, or integrability assumptions. Retrieval evidence
is `LOCAL-LEAF-EXP3-PREDICTABLE-EXPECTED-REGRET`, `MLIB-REAL-LOG-SQRT`,
Mathlib order/measure APIs, EXP3 paper/textbook cards, and the inspiration-only
weapon card. Status is `leanCompiled`, root imported, with a full external
canary. Its realized selected-loss and uniform-horizon consumers now compile.
Failure policy: this theorem remains the square-root branch under the stated
large-horizon regime; arbitrary horizons use the separate clipped-rate theorem.

## EXP3 Realized Expected Regret

`EXP3-REALIZED-EXPECTED-REGRET` now compiles in
`BanditRLProof.Exp3RealizedRegret`. The generated scalar reward is identified
almost surely with the predictable coordinate at the sampled action. The
existing initial and successor action `condDistrib` laws are then consumed by
`integral_historyAction_eq_integral_sum_of_condDistrib_ae_eq_finiteActionMeasure`
to prove, at every actual time,
`E[realizedLoss_t] = E[sum_a p_t(a) * loss_t(a)]`. Mathlib-backed finite-sum
Bochner integration lifts this equality to arbitrary finite horizons.

The unoptimized theorem
`sampledPredictable_realizedExpectedRegret_le` therefore has the same
`log(K)/eta + eta*K*T/(1-gamma) + gamma*T` bound as the compiled mixed-loss
endpoint. The tuned theorem
`sampledPredictable_realizedExpectedRegret_le_four_mul_sqrt` gives
`4*sqrt(K*T*log K)` for the actual generated scalar losses under `2<=K`,
`0<T`, and `4*K*log K<=T`.

Local APIs/imports are `Exp3ExpectedRegret`, the generated reward a.e. laws,
initial/successor action conditional laws, finite-action conditional integral
transport, `Measure.integral_map`, `ExpectationBochnerSums.integral_finset_sum`,
`IntegrabilitySums.integrable_finset_sum`, and `integral_sub`. Contracts are the
existing finite/probability prior, Standard Borel, measurable-singleton,
finite-arm, predictable `[0,1]`, rate, and comparator assumptions. No
independence, stationarity, obliviousness, concentration, or new integrability
premise is introduced. Retrieval is recorded by
`LOCAL-LEAF-EXP3-REALIZED-EXPECTED-REGRET` plus the predictable/tuned,
conditional-moment, adversary, Mathlib measure/kernel/finite-sum, and EXP3
paper/textbook cards; the weapon card remains inspiration-only. Status is
`leanCompiled`, root imported, with declaration canaries and a full external
tuned theorem canary. Failure policy: this transport remains reusable for legal
rates; the all-horizon clipped-rate consumer now compiles, while high-probability
and broader adversary models remain separate.

## EXP3 Uniform-Horizon Realized Regret

`EXP3-UNIFORM-HORIZON-REALIZED-REGRET` now compiles in
`BanditRLProof.Exp3UniformRegret`. The support theorem
`sampledPredictable_realizedExpectedRegret_le_horizon` bounds expected realized
regret by `T` for arbitrary legal `eta` and `0 <= gamma <= 1`. The public endpoint
`sampledPredictable_clippedRealizedExpectedRegret_le_min` defines
`gamma = min(1/2, sqrt(K*log K/T))`, `eta = gamma/K`, and proves
`E[R_T] <= min(T, 4*sqrt(K*T*log K))` for every natural horizon, including zero.

Local APIs/imports are `Exp3RealizedRegret`, the realized-to-explored
finite-horizon expectation equality, explored-loss unit-interval control,
finite-sum integrability, `integral_mono_ae`, `integral_sub`, `Real.log_pos`,
and `Real.sq_sqrt`. The proof route first derives the trivial horizon bound,
then splits on `4*K*log K <= T`: in the large branch the clipped rate equals
the tuned rate and the compiled square-root theorem applies; in the small branch
ordered-ring algebra proves `T <= 4*sqrt(K*T*log K)`, so the minimum is `T`.

Regularity contracts are a probability prior, Standard Borel Env/Action,
measurable action singletons, decidable nonempty finite arms with `2 <= K`, a
jointly measurable predictable `[0,1]` loss vector, and a supported comparator.
There is no positive-horizon, independence, stationarity, obliviousness,
concentration, or supplied-integrability premise. Retrieval uses the realized
and tuned local cards, Mathlib Real log/sqrt, measure/integral, finite-sum, and
order-algebra cards, EXP3 paper/textbook cards, and the weapon card only as
inspiration. Status is `leanCompiled`, root imported, with declaration canaries
and a full external theorem canary. Failure policy: this closes expected realized
regret for the generated predictable-adversary model at all horizons; it does
not claim high-probability regret, stochastic reward regret, arbitrary
non-predictable adversaries, or other EXP3 variants.

### Conditional-kernel measurable-state freeze leaf

`COND-EXPECT-REWARD-CONDEXPKERNEL-MEASURABLE-FREEZE` now compiles in
`BanditRLProof.ConditionalExpectationReward`. The kernel theorem states that
if `X` is measurable in `mcond`, then `(condExpKernel mu mcond).map X` is
`mu.trim hm`-a.e. the deterministic kernel at `X`; the companion theorem
rewrites each pushed-forward measure as `Measure.dirac (X omega)`.

The proof maps Mathlib's diagonal `compProd_trim_condExpKernel` identity through
`X`, identifies the deterministic composition-product, and applies
`Kernel.ae_eq_of_compProd_eq`. Its contracts are finite `mu`, Standard Borel
ambient `Omega`, `mcond <= mOmega`, a countably generated target, and
`Measurable[mcond] X`. In particular, it does not require a countable target,
so Real-valued finite prefixes are supported. Status is `leanCompiled` with two
external canaries. Failure policy: this freezes conditioning-measurable state
only; the generated successor action law and realized-deviation conditional MGF
now compile downstream, while initial-time alignment, Azuma aggregation, and a
high-probability EXP3 theorem remain open.

## EXP3 Successor Realized-Deviation Conditional MGF

`EXP3-REALIZED-DEVIATION-SUCC-COND-MGF` now compiles in
`BanditRLProof.Exp3RealizedConcentration`. The final Lean endpoint
`sampledPredictableRealizedDeviation_succ_hasCondSubgaussianMGF` conditions the
joint `(Env, trajectory)` law on `(Env, finite pair prefix)` and proves a
Mathlib `HasCondSubgaussianMGF` witness with
`Concentration.intervalVarianceProxy 0 1` for realized loss minus the
exploration-mixed predictable loss at time `n + 1`.

The proof recovers the complete finite-support action measure from singleton
`condExpKernel` masses, freezes the predictable environment/history state,
and applies the bounded centered Hoeffding MGF theorem on `[0,1]`. The generated
feedback a.e. law then transports the selected predictable deviation to the
realized scalar deviation. Contracts are finite prior, Standard Borel and
nonempty Env/Action, measurable action singletons, decidable nonempty finite
arms, `0 <= gamma <= 1`, and predictable measurable `[0,1]` losses. No
`Countable Action`, independence, stationarity, probability prior, or supplied
exponential integrability is required. Status is `leanCompiled`, root imported,
with declaration checks and an external theorem canary. Failure policy: this
leaf closes successor one-step MGF only; initial-time alignment, strongly
adapted process assembly, finite-horizon Azuma, confidence events, and
high-probability EXP3 regret remain open. The initial-time and finite-sum items
are now discharged by the downstream leaf below.

## EXP3 Finite-Horizon Realized-Deviation Tail

`EXP3-REALIZED-DEVIATION-SUM-TAIL` now compiles in
`BanditRLProof.Exp3RealizedDeviationTail`. Its Lean endpoint
`sampledPredictableRealizedDeviation_sum_tail_ennreal` bounds the probability
of
`eps <= sum_{t<horizon} (realizedLoss_t - explorationMixedLoss_t)` by the
ENNReal lift of
`exp (-eps^2 / (2 * horizon * intervalVarianceProxy 0 1))`.

The route proves the missing time-zero conditional MGF from the initial-action
law, transports selected to realized loss, and defines the shifted filtration
`F 0 = sigma(Env)`, `F (i+1) = sigma(Env,prefix i)`. The shifted process has
`Y 0 = 0` and `Y (i+1)` equal to the actual time-`i` deviation; explicit
finite-prefix factorizations prove `StronglyAdapted`. The zero and successor
MGF branches then feed the Mathlib-backed ENNReal Azuma wrapper, and two local
sum lemmas remove the index shift. Contracts are a probability prior, Standard
Borel nonempty Env/Action, measurable action singletons, decidable nonempty
finite arms, predictable measurable `[0,1]` losses, legal gamma, and
`eps >= 0`. Failure policy: the realized concentration term is closed, but its
delta confidence-radius simplification now compiles downstream. A statement
audit shows that direct combination with the deterministic Hedge theorem is
not sufficient for true comparator regret because that theorem is expressed
through random importance-weighted estimators.

## EXP3 Realized-Deviation Delta Confidence

`EXP3-REALIZED-DEVIATION-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3RealizedConfidence`. The endpoint
`sampledPredictableRealizedDeviation_sum_tail_delta` states that, for positive
`horizon` and `delta`, the probability that cumulative realized loss minus
exploration-mixed predictable loss exceeds
`sqrt (2 * horizon * intervalVarianceProxy 0 1 * log (1 / delta))` is at most
`ENNReal.ofReal delta`.

The proof records strict positivity of the `[0,1]` Hoeffding proxy, derives the
square-root radius from an arbitrary exponential budget, applies the compiled
finite-horizon ENNReal tail, and simplifies `exp (-log (1/delta))` exactly.
Contracts are a probability prior, Standard Borel nonempty Env/Action,
measurable action singletons, decidable nonempty finite arms, predictable
measurable `[0,1]` losses, legal gamma, positive horizon, and positive delta.
No `delta <= 1` premise is needed for validity, although that is the informative
confidence regime. Failure policy: full high-probability EXP3 regret still
needs conditional concentration for comparator-estimator minus true comparator
loss and pure-`q` cross-weight estimator minus predictable pure-`q` loss, plus
random second-moment control or an EXP3.P-style estimator modification.

## EXP3 Comparator-Estimator Delta Confidence

`EXP3-COMPARATOR-ESTIMATOR-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3ComparatorConfidence`. The endpoint
`sampledObservedComparatorEstimatorDeviation_sum_tail_delta` bounds the event
that the fixed comparator's cumulative observed importance-weighted estimator
minus cumulative true predictable comparator loss exceeds
`sqrt(2 * horizon * intervalVarianceProxy 0 (1/(gamma/|arms|)) * log(1/delta))`.

The module proves a reusable finite-action conditional-MGF bridge, generated
time-zero/successor instances, observed-feedback a.e. transport, finite-prefix
strong adaptedness, an arbitrary-epsilon ENNReal tail, and the delta wrapper.
Contracts are a probability prior, Standard Borel nonempty Env/Action,
measurable singletons, decidable nonempty arms, `0 < gamma <= 1`, predictable
measurable `[0,1]` losses, a supported comparator, and positive horizon/delta.
The comparator concentration obligation is closed. The pure-`q` cross-weight
obligation now compiles downstream; random estimator-square control or an
EXP3.P-style modification remains.

## EXP3 Pure Cross-Weight Delta Confidence

`EXP3-PURE-CROSS-WEIGHT-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3PureConfidence`. The endpoint
`sampledPurePredictableMinusObserved_sum_tail_delta` bounds cumulative
pure-Hedge predictable loss minus pure-Hedge observed cross-weight loss by the
delta radius with proxy `intervalVarianceProxy 0 (1/(gamma/|arms|))`. The
opposite observed-minus-predictable tail remains available as a helper.

The module proves the generic `p`-sampled/`q`-weighted conditional-MGF bridge,
generated zero/successor instances, observed-feedback transport, MGF negation
for the regret-required sign, finite-prefix strong adaptedness, the
arbitrary-epsilon ENNReal tail, and the sqrt/log delta wrapper. Contracts are a
probability prior, Standard Borel nonempty Env/Action,
measurable singletons, decidable nonempty arms, `0 < gamma <= 1`, predictable
measurable `[0,1]` losses, and positive horizon/delta; no comparator or eta
positivity is needed. Pure-`q` cross-weight concentration is closed and its
generated predictable high-probability consumer now compiles downstream.

## EXP3 Predictable High-Probability Regret

`EXP3-PREDICTABLE-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3HighProbabilityRegret`. The support theorem first proves
generated rewards lie in `[0,1]` almost surely and uses
`mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div` plus the exploration
floor to bound the random estimator-square sum by
`horizon / (gamma / |arms|)` almost surely.

The primary endpoint
`sampledPredictable_highProbabilityRegret_tail_total_delta` bounds the
probability that generated exploration-mixed predictable pseudo-regret exceeds
the Hedge term, deterministic reciprocal-floor second-moment term, exploration
bias, and the two confidence radii evaluated at `delta / 2`. Its total failure
probability is `ENNReal.ofReal delta`; the raw two-event endpoint
`sampledPredictable_highProbabilityRegret_tail_delta` remains available.
Contracts are a
probability prior, Standard Borel nonempty Env/Action, measurable singletons,
decidable nonempty arms, `eta>0`, `0<gamma<1`, predictable measurable `[0,1]`
losses, a supported comparator, and positive horizon/delta. This closes the
generated predictable high-probability route and is consumed by the realized
selected-loss theorem below. It is not an ideal-rate result; that still needs a
variance-sensitive/Freedman or EXP3.P route.

## EXP3 Realized High-Probability Regret

`EXP3-REALIZED-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3RealizedHighProbabilityRegret`. Its primary endpoint
`sampledPredictable_realizedHighProbabilityRegret_tail_total_delta` controls
cumulative scalar loss stored in the generated trajectory minus a supported
comparator's true predictable cumulative loss. The budget is the predictable
high-probability budget plus the realized-minus-exploration confidence radius,
all evaluated at `delta / 3`, and the total failure probability is
`ENNReal.ofReal delta`.

The proof uses the pathwise decomposition `realized regret = predictable
regret + realized deviation`, contains the target event in the union of the
compiled predictable-regret and realized-deviation bad events, and applies
`measure_union_le`. Contracts are unchanged from the predictable theorem; no
independence, countability, extra integrability, or new law transport is added.
This closes generated realized selected-loss high-probability regret for the
current range-Hoeffding budget, not a tuned or ideal-rate EXP3 theorem.

## Fixed-Tilt Conditional MGF Sum Tail

`CONCENTRATION-FIXED-TILT-CONDITIONAL-MGF-SUM-TAIL` now compiles in
`BanditRLProof.ConcentrationFixedMGF`. The endpoint
`measure_sum_ge_le_of_hasCondMGFUpperBoundAt` gives
`mu.real {sum Y >= eps} <= exp (-tilt * eps + sum psi)` for a strongly adapted
finite process, from one time-zero MGF budget, successor conditional MGF
budgets, and `0 <= tilt`.

The source witnesses retain exponential integrability at every real multiple,
which is the contract needed by kernel `compProd` composition, but impose the
MGF upper bound only at the selected tilt. The route reuses Mathlib's kernel,
conditional-expectation, `MemLp`, filtration, and exponential Markov APIs.
Local Mathlib retrieval found no Freedman, Bernstein, sub-gamma, or predictable
quadratic variation tail theorem. This generic leaf is not a variance tail by
itself; its one-step fixed-comparator EXP3 consumer is now compiled in
`Exp3ComparatorBernstein`, as recorded below.

## EXP3 Fixed-Comparator Variance-Sensitive Tail

`EXP3-COMPARATOR-BERNSTEIN-FIXED-TILT` now compiles in
`BanditRLProof.Exp3ComparatorBernstein`. Its generated-trajectory endpoint
`sampledObservedComparatorEstimatorDeviation_sum_tail_fixedTilt` proves
`mu.real {sum deviation >= threshold} <= exp (-tilt * threshold +
horizon * tilt^2 / (gamma / |arms|))` whenever
`0 <= tilt <= gamma / |arms|`.

The route uses Mathlib's `Real.abs_exp_sub_one_sub_id_le`, the exact finite-law
centered second moment `loss^2 / prob - loss^2`, its `1 / epsilon` bound, the
compiled `condDistrib`/`condExpKernel.map` bridge, generated zero/successor
action laws, observed/predictable a.e. transport, and the fixed-tilt adapted
sum theorem. Contracts are a probability prior, Standard Borel nonempty
environment/action spaces, measurable singletons, finite nonempty arms,
`0 < gamma <= 1`, predictable measurable `[0,1]` losses, and a supported
comparator. This closes one fixed-comparator arbitrary-tilt tail with linear
reciprocal-floor dependence. Its optimized delta consumer is compiled below;
the pure-cross analogue is also compiled below, while the finite-comparator
union and improved full EXP3 regret theorem remain open.

## EXP3 Fixed-Comparator Variance-Sensitive Delta Confidence

`EXP3-COMPARATOR-BERNSTEIN-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3ComparatorBernstein`. The endpoint
`sampledObservedComparatorEstimatorDeviation_sum_tail_bernstein_delta` uses
`epsilon = gamma / |arms|` and `budget = max (log (1 / delta)) 0`, and bounds
the ENNReal probability of exceeding
`2 * sqrt (horizon * budget / epsilon) + budget / epsilon` by
`ENNReal.ofReal delta`.

The scalar optimizer chooses `sqrt (epsilon * budget / horizon)` when
`budget <= epsilon * horizon`, and the boundary tilt `epsilon` otherwise.
The proof supports zero horizon and every `delta > 0`; it needs neither
`delta <= 1` nor an extra horizon-positivity contract. This closes the
one-comparator delta confidence route, not simultaneous comparator confidence,
the pure-cross route compiled below, a general Freedman theorem, or complete
improved EXP3 high-probability regret.

## EXP3 Pure-Cross Variance-Sensitive Delta Confidence

`EXP3-PURE-CROSS-BERNSTEIN-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3PureBernstein`. The endpoint
`sampledPurePredictableMinusObserved_sum_tail_bernstein_delta` bounds the
generated event where cumulative pure-Hedge predictable loss minus observed
cross-weighted loss exceeds
`2 * sqrt (horizon * budget / epsilon) + budget / epsilon` by
`ENNReal.ofReal delta`, for `epsilon = gamma / |arms|` and
`budget = max (log (1 / delta)) 0`.

The finite-law source reduces the p-sampled/q-weighted estimator to
`q(chosen) * loss(chosen) / p(chosen)` and proves its centered second moment is
at most `1 / epsilon`. A direct positive-tilt proof handles the required
`mean - estimator` sign, then existing conditional-law transport,
observed-feedback equality, adaptedness, fixed-tilt summation, and scalar
optimization complete the route. Contracts permit zero horizon and every
`delta > 0`, with no comparator, eta positivity, independence, stationarity,
countability, or supplied integrability. The predictable two-event consumer
now compiles below; it deliberately retains the existing pathwise
`horizon / epsilon` Hedge-square bound.

## EXP3 Predictable Bernstein High-Probability Regret

`EXP3-PREDICTABLE-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinHighProbabilityRegret`. The endpoint
`sampledPredictable_bernsteinHighProbabilityRegret_tail_total_delta` bounds
the generated exploration-mixed predictable regret bad event by
`ENNReal.ofReal delta`, with the pure-cross and fixed-comparator Bernstein
confidence radii evaluated at `delta / 2`. The raw endpoint retains the two
separate `ENNReal.ofReal delta` failure terms.

The proof reuses the sampled Hedge inequality, exploration bias, and the
pathwise estimator-square bound from the range-Hoeffding assembly. Outside the
two Bernstein bad events, these deterministic inequalities and both strict
confidence complements contradict the target regret event; `measure_mono_ae`
and `measure_union_le` close the union. Contracts allow zero horizon and every
positive delta, with no independence, stationarity, countability, supplied
integrability, or separate square concentration. The deterministic
`horizon / (gamma / |arms|)` square contribution remains, so this is not a
general Freedman theorem or an ideal tuned EXP3/EXP3.P rate. Its generated
realized selected-loss consumer now compiles below.

## EXP3 Random-Square Bernstein High-Probability Regret

`EXP3-RANDOM-SQUARE-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3RandomSquareHighProbabilityRegret`. The supporting endpoint
`sampledPredictableObservedMixedSquared_sum_tail_markov` uses the
finite-horizon expectation upper bound `E[sum mixedSquare] <= |arms|*T` and Mathlib
`Integrable.measure_le_integral` to prove failure probability at most
`deltaSquare` above `|arms|*T/deltaSquare`. Pointwise nonnegativity,
measurability, and integrability of that sum are compiled in the same module.

The primary endpoint
`sampledPredictable_randomSquareBernsteinHighProbabilityRegret_tail_total_delta`
adds the square event to the pure-cross and fixed-comparator Bernstein events,
allocates `delta/3` to all three, and removes reciprocal `gamma` from the Hedge
square budget. Contracts are the generated predictable EXP3 contracts plus
`T>0` and `delta>0`; no independence, stationarity, countability, supplied
integrability, or new law transport is assumed. This is a real improvement over
the deterministic square assembly, but Markov costs `1/delta` rather than
`log(1/delta)`, and both confidence radii still depend on the exploration floor.
The generated realized consumer now compiles below. The ideal
logarithmic-confidence `sqrt(K*T)` route remains open.

## EXP3 Random-Square Bernstein Realized High-Probability Regret

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedHighProbabilityRegret`. The
primary endpoint
`sampledPredictable_randomSquareBernsteinRealizedHighProbabilityRegret_tail_total_delta`
controls cumulative generated scalar loss minus one supported comparator's true
predictable cumulative loss. Its budget adds the random-square predictable
budget to the bounded realized-deviation confidence radius.

The proof uses the exact pathwise decomposition into exploration-mixed
predictable regret and realized-minus-predictable deviation. The raw theorem
exposes the three predictable failures plus the realized failure; the public
wrapper allocates `delta/4` to all four and proves total failure
`ENNReal.ofReal delta`. Contracts require positive horizon and failure
allocations but add no independence, stationarity, countability, supplied
integrability, or law transport. The generated realized consumer is closed
without restoring reciprocal `gamma` in the Hedge-square term. Markov still
costs `1/delta`, both Bernstein radii retain exploration-floor dependence, and
the realized radius remains Hoeffding/Azuma, so ideal Freedman/EXP3.P rates are
still open. The learning-rate-only tuning now compiles below.

## EXP3 Random-Square Bernstein Realized Tuning

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-TUNING` now compiles in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedTuning`. It chooses
`eta = sqrt(log K * (delta/4) / (T*K))` and proves that entropy plus the
stability-amplified Markov-square term is at most
`3*sqrt(4*K*T*log K/delta)` when `gamma <= 1/2`.

The deterministic endpoint bounds the complete four-event budget by this
balanced term plus `gamma*T`, both Bernstein radii at `delta/4`, and the
realized-deviation radius at `delta/4`. The final generated-trajectory theorem
uses `measure_mono` to transfer the existing tail to that explicit threshold.
Contracts require `K>=2`, `T>0`, `0<gamma<=1/2`, and `delta>0`; no
`delta<=1`, cubic/quadratic dominance, independence, stationarity,
countability, supplied integrability, or law transport is added. This closes
eta tuning only. The explicit large-horizon gamma schedule now compiles in the
adjacent route; the caller-selected surface remains useful without dominance
or `delta<=1` assumptions.

## EXP3 Random-Square Bernstein Realized Explicit Tuning

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-EXPLICIT-TUNING` now compiles in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedExplicitTuning`. It first proves
that the two `delta/4` exploration-floor Bernstein radii are each at most
`3*gamma*T` under `K*log(4/delta)<=gamma^3*T`, while the realized radius is at
most `gamma*T` under `2*v*log(4/delta)<=gamma^2*T`. Together with exploration,
the tuned threshold is at most
`3*sqrt(4*K*T*log K/delta)+8*gamma*T`.

The final theorem chooses
`gamma=min(1/2,max((K*log(4/delta)/T)^(1/3),
sqrt(2*v*log(4/delta)/T)))` and discharges both dominance conditions from the
transparent assumptions `8*K*log(4/delta)<=T` and
`8*v*log(4/delta)<=T`. Contracts otherwise match the generated predictable
loss route and require `0<delta<=1`, `K>=2`, and `T>0`; no caller-supplied
gamma, independence, stationarity, countability, supplied integrability, or
new law transport is added. This is an explicit large-horizon result, not a
sharp large-horizon theorem: the leading Markov term still contains
`1/sqrt(delta)` and the realized radius remains Hoeffding/Azuma. The adjacent
all-horizon route handles active clipping with an honest coarse fallback.

## EXP3 Random-Square Bernstein Realized All Horizon

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-ALL-HORIZON` now compiles in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedAllHorizon`. Its threshold
branches internally on the two factor-eight contracts. In the valid explicit
regime it uses `3*sqrt(4*K*T*log K/delta)+8*gamma*T`; otherwise it invokes the
compiled a.e. bound that generated selected-loss regret is at most `T`, making
the strict `T+1` event have measure zero.

The public theorem covers every `T>0` and `0<delta<=1` without a caller-supplied
regime proof. Its probability/Standard-Borel/measurability and
supported-comparator contracts match the explicit route, with no independence,
stationarity, countability, supplied integrability, or new law transport. This
closes all-horizon coverage, not sharp active-clipping analysis: the fallback
is deliberately coarse, while the refined branch still has Markov
`1/sqrt(delta)` dependence and Hoeffding/Azuma realized deviation. General
Freedman and ideal EXP3.P remain open.

## EXP3 Realized Regret With Bernstein Predictable Confidence

`EXP3-REALIZED-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinRealizedHighProbabilityRegret`. The endpoint
`sampledPredictable_bernsteinRealizedHighProbabilityRegret_tail_total_delta`
bounds cumulative scalar loss stored in the generated trajectory minus one
supported comparator's true predictable cumulative loss by
`ENNReal.ofReal delta`. Its budget is the predictable Bernstein regret budget
plus the realized-deviation confidence radius, both evaluated at `delta / 3`;
the raw endpoint displays all three equal-delta failures.

The pathwise identity splits realized regret into exploration-mixed
predictable regret and realized-minus-predictable deviation. The first term
uses the compiled pure-cross and fixed-comparator Bernstein tails; the second
uses the existing `[0,1]` Hoeffding/Azuma confidence radius. Contracts require
positive horizon and delta, but no `delta <= 1`, independence, stationarity,
countability, supplied integrability, extra law transport, or separate square
concentration. The deterministic `horizon / epsilon` Hedge-square term and the
bounded-loss realized radius remain, so this is not a general Freedman theorem,
a fully Bernstein variance-process result, or an ideal tuned EXP3/EXP3.P rate.

## EXP3 Bernstein Tuning Corollary

`EXP3-BERNSTEIN-TUNED-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinTuning`. The endpoint
`sampledPredictable_tunedBernsteinRealizedHighProbabilityRegret_tail` chooses
`eta = sqrt (log K * gamma / (T * K))` and bounds the generated selected-loss
regret event at threshold `11 * gamma * T` by `ENNReal.ofReal delta`.

The proof records the exact rate contracts rather than hiding them: at least
two arms, positive horizon, `0 < gamma <= 1/2`, `0 < delta <= 1`, cubic
dominance of both `K * log K` and `K * log (3/delta)` by `gamma^3 * T`, and
quadratic dominance of the realized interval-variance budget by
`gamma^2 * T`. Entropy and the stability-amplified Hedge square term cost
`3 gamma T`; exploration costs `gamma T`; the two Bernstein radii cost
`3 gamma T` each; realized deviation costs `gamma T`. This closes the
characterized `T^(2/3)`-type implication for the retained deterministic square
term. Its concrete cube-root/max consumer now compiles below; an ideal
`sqrt(K*T)` EXP3.P/Freedman theorem remains separate.

## EXP3 Explicit Bernstein Schedule

`EXP3-EXPLICIT-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinExplicitTuning`. It defines `gamma` as one half
clipped against the maximum of the arm-entropy cube root, confidence cube root,
and realized square root, then proves the generated selected-loss regret tail
at `11*gamma*T` with failure at most `ENNReal.ofReal delta`.

The caller supplies no cubic or quadratic dominance proofs. Instead, the
module derives all three from `8*K*log K<=T`,
`8*K*log(3/delta)<=T`, and
`8*intervalVarianceProxy(0,1)*log(3/delta)<=T`; these also show the clip is
inactive. Contracts retain `K>=2`, `T>0`, `0<delta<=1`, the existing
probability/measurability assumptions, and a supported comparator. This closes
the explicit large-horizon `T^(2/3)`-type schedule. Its active-clip branch is
consumed by the all-horizon wrapper below. An ideal `sqrt(K*T)`
variance-sensitive route remains open.

## EXP3 All-Horizon Bernstein Realized Regret

`EXP3-ALL-HORIZON-BERNSTEIN-REALIZED-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinAllHorizon`. Generated realized scalar loss equals
the selected predictable loss almost surely and is therefore at most one;
the comparator predictable sum is pointwise nonnegative. Finite-sum order then
gives generated realized regret at most `T` almost surely, so the bad event at
the strict threshold `T+1` has measure zero.

`sampledPredictable_allHorizonBernsteinRealizedRegret_tail` branches on the
three factor-eight horizon inequalities. It uses the explicit
`11*gamma*T` Bernstein tail when they hold and the zero-probability `T+1`
fallback otherwise, under the same positive-horizon and `0<delta<=1`
contracts but without caller-supplied regime proofs. This closes the
active-clipping gap. The fallback is deliberately coarse; the ideal
`sqrt(K*T)` EXP3.P/Freedman route remains open.

## EXP3 Mixed-Square Exponential Confidence

`EXP3-MIXED-SQUARE-EXPONENTIAL-CONFIDENCE` now compiles in
`BanditRLProof.Exp3MixedSquareConfidence`. The endpoint
`sampledPredictableObservedMixedSquared_sum_tail_delta` bounds the observed
mixed estimator-square sum at
`K*T + sqrt(2*T*intervalVarianceProxy(0,K/gamma)*log(1/delta))` with failure
at most `ENNReal.ofReal delta`.

The proof identifies the exact finite-action conditional mean
`sum_a loss_t(a)^2`, bounds the raw score in `[0,K/gamma]`, transports the
action law through `condExpKernel`, builds a strongly-adapted centered
process, and transports the latent square sum to scalar feedback almost
everywhere. Contracts are `0<gamma<=1`, positive horizon and delta, a
probability prior, the existing Standard-Borel/measurability assumptions, and
predictable `[0,1]` losses. No comparator, positive eta, `delta<=1`,
independence, stationarity, or supplied integrability is needed.

This removes the Markov `1/delta` threshold, but the interval proxy remains
of order `(K/gamma)^2` per round. The adjacent predictable- and realized-regret
theorems and their learning-rate-tuned consumer now compile. A concrete gamma
schedule remains open, and this is not a Freedman or ideal EXP3.P result.

## EXP3 Mixed-Square Exponential Predictable Regret

`EXP3-MIXED-SQUARE-EXPONENTIAL-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3MixedSquareExponentialHighProbabilityRegret`. Its
total-delta endpoint allocates `delta/3` to the mixed-square, pure-cross, and
fixed-comparator events and bounds generated exploration-mixed predictable
regret against one supported comparator by `ENNReal.ofReal delta`.

The new budget replaces `K*T/deltaSquare` by
`K*T + sampledMixedSquaredConfidenceRadius(...,deltaSquare)` inside the
Hedge stability coefficient. It reuses the compiled pathwise Hedge inequality,
exploration bias, and both Bernstein confidence routes; only the square event
and corresponding deterministic budget changed. Contracts require
`eta>0`, `0<gamma<1`, positive horizon and delta, the existing probability
and measurability assumptions, predictable `[0,1]` losses, and a supported
comparator. No `delta<=1`, independence, stationarity, or supplied
integrability is added.

This is the first downstream regret theorem to remove the Markov
`1/delta` square term. Its interval radius still contributes
`K/gamma * sqrt(T*log(1/delta))` before multiplication by eta. The adjacent
realized-loss and learning-rate-tuned consumers now compile; a concrete gamma
schedule, Freedman, and ideal EXP3.P remain open.

## EXP3 Mixed-Square Bernstein Confidence

`EXP3-MIXED-SQUARE-BERNSTEIN-CONFIDENCE` now compiles in
`BanditRLProof.Exp3MixedSquareBernstein`. For `epsilon=gamma/K`, its generated
observed-square endpoint uses the radius
`2*sqrt(T*(K/epsilon)*log_+(1/delta)) + log_+(1/delta)/epsilon` and has failure
at most `ENNReal.ofReal delta`, including at horizon zero.

The finite sampling law gives the exact uncentered second moment and the
centered bound `K/epsilon`. The proof keeps the sharper centered range cap
`1/epsilon`, transports a fixed-tilt MGF through the existing
`condExpKernel` action law, sums the strongly-adapted generated process,
applies the `K*T` mean budget, transfers to observed feedback a.e., and
optimizes the separate variance coefficient and tilt cap. Contracts are a
probability prior, Standard Borel nonempty Env/Action, measurable singletons,
decidable nonempty arms, arbitrary eta, `0<gamma<=1`, predictable `[0,1]`
losses, any natural horizon, and `delta>0`; no comparator, eta positivity,
positive horizon, `delta<=1`, independence, stationarity, countability,
supplied integrability, or new law transport is added.

This improves the old `1/epsilon^2` interval proxy, but it is a fixed-tilt
deterministic `K/epsilon` variance bound, not a random predictable
quadratic-variation, anytime, self-normalized, or general Freedman theorem.

## EXP3 Mixed-Square Predictable Variance

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE` now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVariance`. It defines the exact
finite-action centered second moment, proves its finite-law integral identity,
nonnegativity, measurability, and `K/epsilon` bound, then instantiates it at
each generated EXP3 round. After shifting by one, the resulting process is
`IsPredictable` for `sampledPredictableDeviationFiltration`; its first `T`
actual-time values sum to at most `T*(K/(gamma/K))`.

The proof factors time zero through `Env` and successor rounds through
`(Env, finite prefix)`, using the existing generated probability source and
predictable-loss regularity. Contracts are measurable Env/Action, measurable
action singletons, decidable nonempty arms, arbitrary eta, `0<gamma<=1`,
predictable `[0,1]` losses, and any natural horizon. It needs no prior,
Standard Borel instance, comparator, confidence parameter, or integrability
premise. The compiled finite-action integral equality is not yet an ambient
`condExpKernel` square identity in this row; the adjacent law-transport row now
closes that gap and the new predictable-variance tail row consumes it. The
remaining blockers are maximal/anytime control and preserving the random
variance event through the EXP3 regret assembly.

## EXP3 Mixed-Square Predictable Variance Conditional Square Law

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-COND-EXP` now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVariance`. Its primary endpoint states
that, at every shifted process index `n+1`, the ambient `condExpKernel` square
integral of the centered mixed-square increment given the generated filtration
`F_n` equals the matching shifted predictable variance almost everywhere.

The generic layer freezes history inside `condExpKernel`, composes the
identified finite action pushforward with the centered score, and applies
`integral_map` twice before using the finite-action square identity. Generated
wrappers instantiate time zero given `Env`, successors given `(Env,prefix n)`,
and then normalize both cases to the shifted process. Contracts are a finite
prior, Standard Borel nonempty Env/Action, measurable action singletons,
decidable nonempty arms, arbitrary eta, `0<gamma<=1`, predictable `[0,1]`
losses, and any process index; no probability prior, comparator, horizon,
delta, independence, stationarity, or supplied integrability is required.
This is an exact conditional-square law, not yet a random-variance
exponential-supermartingale or Freedman tail.

## EXP3 Mixed-Square Bernstein Predictable Regret

`EXP3-MIXED-SQUARE-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinHighProbabilityRegret`. Its total-delta
endpoint places the new mixed-square Bernstein radius inside the Hedge
stability term and combines it with the existing pure-cross and comparator
Bernstein radii using three `delta/3` events.

The theorem covers every natural horizon and otherwise retains the generated
predictable-adversary contracts: probability prior, Standard Borel nonempty
Env/Action, measurable singletons, decidable nonempty arms, `eta>0`,
`0<gamma<1`, predictable `[0,1]` losses, a supported comparator, and positive
delta. It is root imported and has a full external total-delta canary. The
realized-regret assembly below now consumes this radius; parameter tuning,
general Freedman, and ideal EXP3.P remain separate.

## EXP3 Mixed-Square Bernstein Realized Regret

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinRealizedHighProbabilityRegret`. Its
total-delta endpoint controls generated scalar cumulative loss minus one
supported comparator's true predictable cumulative loss using four
`delta/4` events.

The Lean route proves the pathwise identity between realized regret,
exploration-mixed predictable regret, and cumulative realized deviation. It
then combines `sampledPredictable_bernsteinSquareHighProbabilityRegret_tail`
with `sampledPredictableRealizedDeviation_sum_tail_delta`, contains the target
event in their union, and normalizes the four underlying allocations. No new
filtration, conditional-law, or integrability transport is introduced.

Contracts require a probability prior, Standard Borel nonempty Env/Action,
measurable action singletons, decidable nonempty arms, `eta>0`,
`0<gamma<1`, predictable measurable `[0,1]` losses, a supported comparator,
positive horizon, and positive delta. The theorem is root imported and has a
full external total-delta canary. The mixed-square term now uses the
deterministic `K/epsilon` second-moment radius in generated realized regret,
but it is not random quadratic-variation or general Freedman control; the
realized radius remains Hoeffding/Azuma. Eta tuning now compiles below; explicit
gamma scheduling and ideal EXP3.P remain open.

## EXP3 Mixed-Square Bernstein Realized Tuning

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-TUNING` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinRealizedTuning`. It defines

`S = K*T + sampledMixedSquaredBernsteinConfidenceRadius(arms,gamma,T,delta/4)`

and `eta=sqrt(log(K)/S)`. The generated endpoint controls realized selected-loss
regret at `3*sqrt(log(K)*S)+gamma*T` plus the pure-cross Bernstein, comparator
Bernstein, and realized-deviation radii, with failure at most
`ENNReal.ofReal delta`.

The proof explicitly establishes `S>0`: unlike the old interval-square scale,
the new radius has a linear `log_+/epsilon` term, so positivity uses `K>=2`,
`T>0`, and `gamma>0` to show both epsilon and the variance coefficient are
positive. It then proves `eta>0`, `eta^2*S=log K`, identifies entropy with
`eta*S` and `sqrt(log K*S)`, uses `gamma<=1/2` for the factor-two stability
bound, compares the complete realized budget, and applies measure monotonicity.

Contracts are a probability prior, Standard Borel nonempty Env/Action,
measurable singletons, decidable arms with `K>=2`, predictable `[0,1]` losses,
a supported comparator, positive horizon and delta, and `0<gamma<=1/2`. No
`delta<=1`, dominance premise, independence, stationarity, countability,
supplied integrability, or new law transport is added. The theorem is root
imported and externally canaried. Eta is now closed against the exact
deterministic Bernstein-square scale; explicit gamma scheduling, the linear
`log_+/epsilon` correction, Hoeffding/Azuma replacement, random quadratic
variation, general Freedman, and ideal EXP3.P remain open.

## EXP3 Mixed-Square Exponential Realized Regret

`EXP3-MIXED-SQUARE-EXPONENTIAL-REALIZED-HIGH-PROBABILITY-REGRET` now compiles
in `BanditRLProof.Exp3MixedSquareExponentialRealizedHighProbabilityRegret`.
Its primary endpoint controls generated scalar cumulative loss minus one
supported comparator's predictable cumulative loss with total failure
probability `ENNReal.ofReal delta`.

The proof uses the exact pathwise identity between realized regret,
exploration-mixed predictable regret, and cumulative realized deviation. The
predictable theorem contributes the exponential square, pure-cross Bernstein,
and comparator Bernstein events; the existing realized-deviation tail is the
fourth event. The public wrapper allocates `delta/4` to all four events.

Contracts require a probability prior, Standard Borel nonempty Env/Action,
measurable action singletons, decidable nonempty arms, `eta>0`,
`0<gamma<1`, predictable measurable `[0,1]` losses, a supported comparator,
positive horizon, and positive delta. No `delta<=1`, independence,
stationarity, countability, supplied integrability, or new law transport is
introduced. Markov square dependence is now absent from generated realized
regret, but the `K/gamma` interval radius and bounded-loss Hoeffding/Azuma
realized radius remain. Learning-rate tuning compiles below; a concrete gamma
schedule, variance-sensitive Freedman control, and ideal EXP3.P remain open.

## EXP3 Mixed-Square Exponential Realized Tuning

`EXP3-MIXED-SQUARE-EXPONENTIAL-REALIZED-TUNING` now compiles in
`BanditRLProof.Exp3MixedSquareExponentialRealizedTuning`. It defines

`S = K*T + sampledMixedSquaredConfidenceRadius(arms,gamma,T,delta/4)`

and chooses `eta=sqrt(log K/S)`. For `K>=2`, `T>0`, and
`0<gamma<=1/2`, the module proves `S>0`, `eta>0`,
`eta^2*S=log K`, and bounds entropy plus the stability-amplified square scale
by `3*sqrt(log K*S)`.

The public tail controls generated realized selected-loss regret at this
balanced term plus `gamma*T`, the two Bernstein radii, and the realized
deviation radius, all at `delta/4`, with failure at most
`ENNReal.ofReal delta`. It needs no `delta<=1` or caller-supplied dominance
contract. The explicit large-horizon gamma consumer and its coarse all-horizon
wrapper now compile below; this caller-selected theorem remains useful under
weaker assumptions. Variance-sensitive Freedman control and ideal EXP3.P
remain separate.

## EXP3 Mixed-Square Exponential Realized Explicit Tuning

`EXP3-MIXED-SQUARE-EXPONENTIAL-REALIZED-EXPLICIT-TUNING` now compiles in
`BanditRLProof.Exp3MixedSquareExponentialRealizedExplicitTuning`. It chooses
`gamma` as the minimum of `1/2` and the maximum of four scales:

- `sqrt(K*log K/T)` for the `K*T` part of the balanced square scale;
- `(K^2*(log K)^2*log(4/delta)/(2*T^3))^(1/6)` for the current
  `(K/(2*gamma))^2` mixed-square interval proxy;
- `(K*log(4/delta)/T)^(1/3)` for both Bernstein confidence radii;
- `sqrt(2*v*log(4/delta)/T)` for realized deviation, where
  `v=intervalVarianceProxy(0,1)`.

The module proves the exact proxy identity, reduces the balanced square-root
term to `2*gamma*T`, and obtains a generated realized-regret tail at
`14*gamma*T`. Four transparent horizon contracts make clipping inactive and
discharge the quadratic, sixth-power, cubic, and realized quadratic dominance
conditions. Contracts are a probability prior, Standard Borel nonempty
Env/Action, measurable singletons, decidable arms with `K>=2`, predictable
measurable `[0,1]` losses, a supported comparator, `T>0`, `0<delta<=1`, and
the four displayed large-horizon inequalities; no independence, stationarity,
countability, supplied integrability, caller gamma, or new law transport is
added. Large-horizon gamma scheduling is now closed for this route. The
sixth-root term honestly records the current Hoeffding-proxy limitation. Its
active-clipping complement is consumed by the all-horizon wrapper below;
variance-sensitive Freedman control and ideal EXP3.P remain open.

## EXP3 Mixed-Square Exponential Realized All Horizon

`EXP3-MIXED-SQUARE-EXPONENTIAL-REALIZED-ALL-HORIZON` now compiles in
`BanditRLProof.Exp3MixedSquareExponentialRealizedAllHorizon`. It defines the
exact four-contract large-horizon proposition and branches the generated
realized-regret threshold between the explicit exponential-square threshold,
which is bounded upstream by `14*gamma*T`, and the strict `T+1` fallback.

The positive branch invokes the compiled explicit-schedule tail. The
complementary branch reuses `sampledPredictable_trivialRealizedRegret_tail`,
whose pathwise finite-horizon bound makes the strict fallback event have
probability zero. Contracts are a probability prior, Standard Borel nonempty
Env/Action, measurable action singletons, decidable arms with `K>=2`,
predictable measurable `[0,1]` losses, a supported comparator, `T>0`, and
`0<delta<=1`; no caller regime proof, independence, stationarity,
countability, supplied integrability, or new law transport is added. The leaf
is root imported, has a focused build, and has a full external theorem canary
in `Tests.Basic`.

Failure policy: every positive horizon is covered, but outside the four-contract
regime the threshold is deliberately the coarse `T+1` zero-probability
fallback. The refined branch still has the Bernstein confidence cube-root
`T^(2/3)` limitation and Hoeffding/Azuma realized deviation. This is not a
sharp active-clipping theorem, variance-sensitive mixed-square Freedman
control, or ideal EXP3.P.

## EXP3 Mixed-Square Bernstein Realized Explicit Tuning

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-EXPLICIT-TUNING` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinRealizedExplicitTuning`; the preceding
eta-tuning row is consumed by this endpoint. The public theorem
`sampledPredictable_explicitBernsteinSquareRealizedRegret_tail` balances eta
against the exact fixed-tilt Bernstein mixed-square scale and uses the same
conservative four-scale clipped gamma already compiled for the exponential
square route. Under the arm factor-four, mixed factor-64, confidence
factor-eight, and realized factor-eight contracts, its generated realized
regret threshold is `14*gamma*T` with failure at most `ENNReal.ofReal delta`.

The proof identifies the variance coefficient as `K^2/gamma`, uses
`gamma<=1/2` to turn the sixth-power mixed contract into the power needed by
the square-root term, uses the arm and confidence contracts for the linear
`log_+/epsilon` term, and derives the balanced-root bound `2*gamma*T`. It then
transports positivity, stability, and all four dominance contracts through a
thin alias of the existing clipped schedule and invokes the characterized
tail. Contracts are a probability prior, Standard Borel nonempty Env/Action,
measurable action singletons, decidable arms with `K>=2`, predictable `[0,1]`
losses, a supported comparator, `T>0`, and `0<delta<=1`; no independence,
stationarity, countability, supplied integrability, caller gamma, or new law
transport is added. The module is root imported and externally instantiated
in `Tests.Basic`.

Failure policy: this is an honest reuse of the conservative sixth-root
schedule, not a newly optimized fifth-root or coupled gamma formula. The
current linear `log_+/epsilon` correction is already controlled inside the
compiled constant; eliminating or improving it, Hoeffding/Azuma realized
deviation, random predictable quadratic variation, general Freedman, and ideal
EXP3.P remain open. The active-clipping complement now compiles below through
an honest coarse `T+1` fallback.

## EXP3 Mixed-Square Bernstein Realized All Horizon

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-ALL-HORIZON` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinRealizedAllHorizon` and consumes the
preceding explicit-tuning row. It defines the exact conjunction of the arm
factor-four, mixed factor-64, confidence factor-eight, and realized
factor-eight contracts. Its threshold is the explicit variance-sensitive
threshold, upstream-bounded by `14*gamma*T`, in that regime and strict `T+1`
otherwise.

The positive branch invokes
`sampledPredictable_explicitBernsteinSquareRealizedRegret_tail`. The negative
branch instantiates `sampledPredictable_trivialRealizedRegret_tail` with the
same exact Bernstein-square eta and clipped gamma, so the fallback event has
probability zero. Regularity contracts are a probability prior, Standard
Borel nonempty Env/Action, measurable action singletons, decidable arms with
`K>=2`, predictable `[0,1]` losses, a supported comparator, `T>0`, and
`0<delta<=1`; no caller regime proof, independence, stationarity,
countability, supplied integrability, or new law transport is added. The
module is root imported and externally instantiated in `Tests.Basic`.

Failure policy: every positive horizon is covered, but outside the exact
four-contract regime the `T+1` threshold is deliberately coarse. The refined
branch retains the controlled linear `log_+/epsilon` term and
Hoeffding/Azuma realized deviation. This is not sharp active clipping, a
sharper fifth-root/coupled schedule, random predictable quadratic variation,
general Freedman, or ideal EXP3.P.

## EXP3 Mixed-Square Predictable-Variance Tail

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-TAIL` now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceTail`. The fixed-tilt theorem
`sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_fixedTilt`
proves
`P(sum X >= x and sum V <= v) <= exp(-t*x+t^2*v)` for
`0<=t<=gamma/K`. The optimized theorem
`sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta`
uses radius `2*sqrt(v*log_+(1/delta))+log_+(1/delta)/(gamma/K)` and failure
probability at most `ENNReal.ofReal delta`.

The proof establishes the support bound `|X|<=1/epsilon`, retains the exact
finite-law centered second moment in the one-step MGF, subtracts that random
predictable budget, transports the compensated law through the generated
zero/successor conditional kernels, and iterates the shifted strongly adapted
process with the existing fixed-MGF sum theorem. Contracts are a probability
prior, Standard Borel nonempty Env/Action, measurable action singletons,
decidable nonempty arms, arbitrary eta, `0<gamma<=1`, predictable measurable
`[0,1]` losses, any natural horizon, and positive `v,delta` for the optimized
wrapper. The module is root imported and its delta endpoint has an external
canary in `Tests.Basic`.

Failure policy: this is a fixed-horizon joint-event predictable-variance
Bernstein/Freedman theorem. It is not maximal/Ville, peeling/stitching,
anytime/self-normalized, an unconditional tail without controlling `sum V`,
or a complete ideal EXP3.P regret theorem. Its random-variance event is now
consumed by the generated predictable-regret route below.

## EXP3 Mixed-Square Predictable-Variance High-Probability Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-HIGH-PROBABILITY-REGRET` now
compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceHighProbabilityRegret`.
The observed-square bridge transports the centered joint tail to the Hedge
square sum using `sampledObservedMixedSquaredSum_eq_predictable_ae`, the exact
deviation identity, and the `K*T` predictable-mean bound. The joint regret
endpoint combines that event with the existing pure-cross and comparator
Bernstein events. The primary total-delta theorem proves
`P(regret >= budget(v,delta)) <= ofReal(delta) + P(sum V > v)`, with square
radius `2*sqrt(v*log_+(3/delta))+log_+(3/delta)/(gamma/K)`.

The proof uses the sampled Hedge inequality, exploration bias, strict
complements of the three confidence events, `measure_mono_ae`, and union
bounds. It then splits the unconditional regret event into the compiled joint
event on `sum V<=v` and the single variance-overflow event. Contracts are a
probability prior; Standard Borel nonempty Env/Action; measurable action
singletons; decidable nonempty arms; `eta>0`; `0<gamma<1`; predictable
measurable `[0,1]` losses; a supported comparator; any natural horizon; and
positive `v,delta`. No `delta<=1`, independence, stationarity, countability,
supplied integrability, deterministic variance-envelope premise, or new
conditional-law transport is required. The module is root imported and the
primary residual theorem has an external canary in `Tests.Basic`.

Failure policy: random predictable variance now reaches generated predictable
regret without replacement by the deterministic envelope and is consumed by
the realized selected-loss route below. A closed sharper regret rate still
requires control of `P(sum V>v)`, for example through
algorithm-specific structure, peeling/stitching, or a maximal/self-normalized
argument. This is not anytime control, general Freedman, or ideal EXP3.P.

## EXP3 Mixed-Square Predictable-Variance Realized High-Probability Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-REALIZED-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceRealizedHighProbabilityRegret`.
Its joint total-delta endpoint proves
`P(realized regret >= budget(v,delta) and sum V <= v) <= ofReal(delta)`, and
the primary residual endpoint proves
`P(realized regret >= budget(v,delta)) <= ofReal(delta) + P(sum V > v)`.
The budget adds `sampledPredictableRealizedDeviationConfidenceRadius` to the
predictable random-variance budget and allocates `delta/4` to random-square,
pure-cross, comparator, and realized-deviation failures.

The proof rewrites realized selected-loss regret pathwise as predictable
exploration-mixed regret plus cumulative realized deviation, unions the
predictable joint event with the compiled realized-deviation event, then
splits the unconditional event into the variance-good branch and the strict
overflow `varianceBudget < sum V`. Contracts are a probability prior;
Standard Borel nonempty Env/Action; measurable action singletons; decidable
nonempty arms; `eta>0`; `0<gamma<1`; predictable measurable `[0,1]` losses;
a supported comparator; positive horizon; and positive variance budget and
confidence allocations. No `delta<=1`, independence, stationarity,
countability, supplied integrability, deterministic variance-envelope
premise, or new conditional-law transport is required. Retrieval uses the
predictable-variance regret row, realized-deviation confidence, the comparable
Bernstein realized assembly, Mathlib measure/finite-sum/order/sub-Gaussian/MGF
cards, the Auer EXP3 card, and inspiration-only potential/tail weapons. The
module is root imported, focused-built, and externally canaried at the primary
total-delta residual theorem in `Tests.Basic`.

Failure policy: realized selected-loss transport is closed while preserving
the overflow probability and this row is consumed by the Markov route below.
No maximal/anytime or self-normalized theorem, general Freedman theorem, or
ideal EXP3.P theorem is claimed.

## EXP3 Predictable-Variance Realized Markov High-Probability Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-REALIZED-MARKOV-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceRealizedMarkovHighProbabilityRegret`.
Its Mathlib-backed overflow endpoint states
`mu {sum V > v} <= lintegral (ofReal (sum V)) mu / ofReal v` for any measure
and `v>0`. The raw realized consumer substitutes an explicit contract
`lintegral (ofReal (sum V)) mu <= ofReal varianceMeanBudget` into the prior
residual theorem. The primary endpoint chooses
`v=varianceMeanBudget/(delta/5)`, allocates `delta/5` to random-square,
pure-cross, comparator, realized-deviation, and overflow failures, and proves
`P(realized regret >= budget(varianceMeanBudget,delta)) <= ofReal delta`.

Local APIs/imports are the prior realized residual route,
`Mathlib.MeasureTheory.Integral.Lebesgue.Markov`,
`meas_ge_le_lintegral_div`, cumulative-variance measurability/nonnegativity,
`ENNReal.measurable_ofReal`, `measure_mono`, `ENNReal.div_le_div`,
`ENNReal.ofReal_div_of_pos`, `ENNReal.div_div_cancel`, and
`ENNReal.ofReal_add`. The proof contains the strict real overflow event in
Mathlib's weak ENNReal threshold event, applies Markov, inserts the supplied
lintegral budget, then normalizes five equal allocations.

The generic Markov leaf needs only an arbitrary measure, measurable
Env/Action with measurable action singletons, decidable nonempty arms,
`0<gamma<=1`, predictable measurable `[0,1]` losses, and `v>0`; it does not
need a finite measure. The primary regret endpoint additionally requires a
probability prior, Standard Borel nonempty Env/Action, `eta>0`, `0<gamma<1`,
a supported comparator, positive horizon, positive variance mean budget and
delta, and the displayed generated-trajectory lintegral contract. No
`delta<=1`, independence, stationarity, countability, separate integrability
witness, deterministic envelope, or new law transport is required. Retrieval
uses `MLIB-MEASURE-INTEGRAL` with Markov, finite-sum/order cards, the Auer EXP3
card, and inspiration-only tail/potential weapons. The module is root imported,
focused/root built, and externally canaried at the primary endpoint.

Failure policy: the probability residual is closed under a precise expectation
contract, and the loss-energy route below now discharges it when a pathwise
armwise loss-square budget is supplied. Markov still forces `v` to scale as
`varianceMeanBudget/delta`; sharper scenario-specific energy estimates or a
stronger exponential/self-normalized overflow theorem are still required for
general Freedman, anytime control, or ideal EXP3.P.

## EXP3 Predictable-Variance Loss-Energy Realized Markov Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-LOSS-ENERGY-REALIZED-MARKOV-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceLossEnergyRealizedMarkovHighProbabilityRegret`.
Its finite-law endpoint proves that the centered mixed-square estimator
variance is at most `(1/epsilon) * sum_a loss(a)^2`. Generated transport and
finite summation yield
`sum V <= (1/(gamma/K)) * sampledPredictableLossSquaredSum`. Consequently, a
pathwise armwise loss-square budget `L2` gives the exact lintegral contract
`lintegral(ofReal(sum V)) <= ofReal((1/(gamma/K))*L2)` and the prior Markov
consumer yields a realized selected-loss tail with total failure `delta`.

Local APIs/imports are the prior realized Markov module,
`sampledPredictableLossSquaredSum`, the exact mixed-square first/second-moment
identities, `FiniteActionDistribution.sum_eq_one`, generated probability and
loss-regularity sources, finite-sum/order/ring arithmetic, `lintegral_mono`,
`ENNReal.ofReal_le_ofReal`, and probability-measure integration of constants.
The proof expands the centered variance, applies `loss^4<=loss^2` and the
probability floor termwise, subtracts the nonnegative squared mean, transports
the result to every generated time, factors the horizon sum, integrates the
pathwise energy bound, and invokes the five-event Markov theorem.

The generic finite-law theorem needs a positive probability floor and losses
in `[0,1]`. The generated primary endpoint requires a probability prior,
Standard Borel nonempty Env/Action, measurable action singletons, decidable
nonempty arms, `eta>0`, `0<gamma<1`, predictable measurable `[0,1]` losses, a
supported comparator, positive horizon, positive `L2` and `delta`, and the
pathwise cumulative loss-square contract. No `delta<=1`, independence,
stationarity, countability, separate integrability witness, new law transport,
or deterministic `K*T` envelope premise is required. Retrieval uses the prior
Markov and predictable-variance rows, mixed-square Bernstein confidence,
finite-sum/order/measure cards, the Auer EXP3 card, and inspiration-only
tail/potential weapons. The module is root imported, focused/root built, and
externally canaried at the primary theorem.

Failure policy: the downstream small-loss route now derives `L2<=L1` and
replaces the Hedge `K*T` mean upper bound by `L1`. Markov still costs
`(L2/epsilon)/delta`; sharper exponential/self-normalized overflow,
maximal/anytime control, general Freedman, and ideal EXP3.P remain open.

## EXP3 Predictable-Variance Small-Loss Realized Markov Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SMALL-LOSS-REALIZED-MARKOV-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSmallLossRealizedMarkovHighProbabilityRegret`.
It defines the pathwise armwise loss mass
`L1=sum_t sum_a predictableLoss_t(a)` and proves `sum_t sum_a loss_t(a)^2<=L1`
from the existing `[0,1]` regularity. Hence `sum V<=(1/(gamma/K))*L1`, and the
same inequality supplies the generated variance `lintegral` budget.

The new observed-square bridge uses `L1` as an upper bound on the exact
predictable mixed-square mean `L2`, replacing the previous `K*T` upper bound.
Its predictable regret budget is
`log(K)/eta + eta/(1-gamma)*(L1+radius(v,deltaSquare)) + gamma*T` plus the
pure-cross and comparator Bernstein radii. The realized wrapper adds the
realized-deviation radius. The primary theorem sets
`v=((1/(gamma/K))*L1)/(delta/5)`, allocates `delta/5` to mixed-square,
pure-cross, comparator, realized-deviation, and Markov overflow, and proves the
generated realized selected-loss tail is at most `ofReal(delta)`.

Local APIs/imports are the loss-energy module, generated predictable loss
coordinates and unit-interval contracts, finite sums, observed/predictable
mixed-square a.e. equality, centered predictable-variance tail, sampled Hedge,
exploration bias, pure-cross/comparator Bernstein tails, realized-deviation
confidence, variance lintegral and Mathlib Markov, measure unions, and ENNReal
division/ofReal algebra. The proof first derives `l^2<=l`, sums over arms/time,
rebuilds the three-event predictable assembly with `L1`, adds realized
deviation as a fourth event, then splits the unconditional event into the
variance-good branch and fifth Markov overflow event.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; supported comparator;
positive horizon, `L1`, and `delta`; and a universal pathwise armwise loss-mass
bound. No `delta<=1`, independence, stationarity, countability, separate
integrability, new law transport, deterministic `K*T`, supplied `L2`, or
supplied variance-lintegral premise is required. Retrieval uses the loss-energy
and predictable/realized variance rows, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, `MLIB-MEASURE-INTEGRAL`, `SCN-ADVERSARIAL-FINITE`, the
Auer EXP3 card, and inspiration-only tail/potential weapons. The module is root
imported, focused/root built, and externally canaried at the primary theorem.

Failure policy: this is an armwise aggregate small-loss theorem, not a standard
first-order best-arm-loss guarantee. The generic pathwise `L1` premise is now
consumed by the sparse-loss route below. `eta` and `gamma` remain
caller-selected, and Markov gives `v=(L1/(gamma/K))/(delta/5)`. L1-aware
tuning, best-arm first-order conversion, exponential/self-normalized overflow,
anytime control, general Freedman, and ideal EXP3.P remain open.

## EXP3 Predictable-Variance Sparse-Loss Realized Markov Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovHighProbabilityRegret`.
The Lean-facing support definition filters `arms` to coordinates with nonzero
`predictableLossAt`. `sampledPredictableLossMassAt_le_supportCard` removes the
zero coordinates and uses the existing `[0,1]` contract to bound one-round
armwise loss mass by the support cardinality.
`sampledPredictableLossMassSum_le_sparsity_mul_horizon` then turns a universal
per-round natural support cap `s` into `L1 <= s*T`. The sparse budget aliases
the small-loss budget at `lossMassBudget=(s:Real)*T`, and the primary theorem
proves the generated realized selected-loss bad event has probability at most
`ENNReal.ofReal delta`.

Local APIs/imports are the compiled small-loss module,
`sampledPredictableLossMassSum`, `predictableLossAt_mem_unitInterval`,
`Finset.filter`, `Finset.filter_subset`, `Finset.sum_subset`,
`Finset.sum_le_sum`, `Finset.mem_range`, `Nat.cast_le`, and finite-sum/order
algebra. The proof filters to nonzero support, bounds each retained coordinate
by one, sums the support cap over `Finset.range horizon`, proves positivity of
`s*T`, and invokes the small-loss total-delta theorem.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon, positive natural sparsity, positive delta; and the pathwise
support-cardinality cap for every generated sample and `t<horizon`. No
`s<=K`, `delta<=1`, independence, stationarity, countability, supplied
integrability, new law transport, supplied `L1`/`L2`/lintegral premise, or
deterministic `K*T` premise is required.

Retrieval uses the compiled small-loss row, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, `SCN-ADVERSARIAL-FINITE`, the Auer EXP3 card, and
inspiration-only tail/potential weapons. Status is `leanCompiled`, root
imported, focused/root built, and externally canaried at the primary theorem.

Failure policy: this closes the former abstract `L1` input for uniformly
pathwise sparse nonzero supports, but the result still controls armwise
aggregate loss and assumes sparsity for every generated sample. Eta is selected
by the tuning route below; gamma remains caller-selected and Markov retains
`1/delta`. Best-arm first-order conversion, probabilistic sparsity,
exponential/self-normalized overflow, anytime control, general Freedman, and
ideal EXP3.P remain open.

## EXP3 Sparse-Loss Predictable-Variance Realized Markov Eta Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovTuning`.
For `L=(s:Real)*T`, it defines the exact Markov threshold
`v=((1/(gamma/K))*L)/(delta/5)` and complete Hedge scale
`S=L+sampledMixedSquaredPredictableVarianceRadius arms gamma v (delta/5)`.
The internal learning rate is `eta=sqrt(log K/S)`.

The module proves `v>0`, `S>0`, `eta>0`, and `eta^2*S=log K`. Under
`K>=2` and `0<gamma<=1/2`, it identifies the entropy term with
`sqrt(log K*S)` and bounds the stability-amplified term by twice entropy.
Thus the complete eta-dependent budget is at most `3*sqrt(log K*S)`. The
tuned threshold adds `gamma*T` and the pure-cross, comparator, and
realized-deviation radii at `delta/5`; the final theorem tightens the compiled
sparse-loss event and retains failure probability `ENNReal.ofReal delta`.

Local APIs/imports are the sparse-loss total-delta module, its exact budget,
`sampledMixedSquaredPredictableVarianceRadius`, `Real.log`, `Real.sqrt`,
`Real.log_pos`, `Real.sqrt_pos`, `Real.sq_sqrt`, finite-cardinality casts,
`field_simp`, `ring`, `linarith`, `nlinarith`, and `measure_mono`.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
`0<gamma<=1/2`; predictable measurable `[0,1]` losses; supported comparator;
positive horizon, natural sparsity, and delta; and the universal pathwise
support-cardinality cap. Eta is internal. No eta premise, `s<=K`, `delta<=1`,
independence, stationarity, countability, supplied integrability, new law
transport, supplied `L1`/`L2`/lintegral premise, or deterministic `K*T`
premise is required.

Retrieval uses the sparse-loss route, existing exponential/Bernstein square
tuning templates, `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`,
`MLIB-FINSET-SUMS`, `SCN-ADVERSARIAL-FINITE`, the Auer EXP3 card, and
inspiration-only tail/potential weapons. Status is `leanCompiled`, root
imported, focused/root built, and externally canaried at the final theorem.

Failure policy: eta tuning is closed against the exact Markov sparse-loss
scale and is consumed by the explicit-gamma route below. Sparsity remains
universal pathwise, the loss notion remains armwise aggregate, and Markov
retains `1/delta`. Probabilistic sparsity, best-arm conversion,
exponential/self-normalized overflow, general Freedman, anytime control, and
ideal EXP3.P remain open.

## EXP3 Sparse-Loss Predictable-Variance Realized Markov Explicit Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-EXPLICIT-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovExplicitTuning`.
Writing `B=log(5/delta)`, it proves the exact Markov budget
`v=5*K*s*T/(gamma*delta)` and uses the full scale
`S=s*T+sampledMixedSquaredPredictableVarianceRadius(K,gamma,v,delta/5)`.
The contracts
`s*log K<=gamma^2*T`,
`5*K*s*(log K)^2*B<=gamma^5*delta*T^3`, and
`K*B<=gamma^3*T` control the complete balanced scale by
`sqrt(log K*S)<=2*gamma*T`; the usual realized quadratic contract then bounds
the eta-tuned threshold by `14*gamma*T`.

The explicit gamma is the minimum of `1/2` and the maximum of the sparse arm
square root, Markov fifth root, confidence cube root, and realized square
root. New fifth-root lemmas based on `Real.rpow_inv_natCast_pow` recover the
fifth-power contract. Four horizon inequalities with constants `4`, `32`,
`8`, and `8` make clipping inactive and discharge every characterized
premise. The final theorem
`sampledPredictable_explicitSparseLossPredictableVarianceRealizedMarkovRegret_tail`
selects both eta and gamma internally and bounds the generated realized-regret
bad event by `ENNReal.ofReal delta`.

Local APIs/imports are the preceding sparse eta-tuned theorem, the existing
explicit exponential-square algebra template, `Real.rpow_inv_natCast_pow`,
`Real.sqrt_le_iff`, power monotonicity, max/min order lemmas, the generic
Bernstein-radius and realized-radius dominance lemmas, finite-cardinality
casts, field/ring normalization, arithmetic tactics, and `measure_mono`.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and natural sparsity; `0<delta<=1`; the four explicit large-horizon
inequalities; and universal pathwise support sparsity. No caller eta/gamma,
`s<=K`, independence, stationarity, countability, supplied integrability, new
law transport, or supplied `L1`/`L2`/lintegral premise is required.

Retrieval uses the sparse eta-tuned route, exponential explicit-tuning and
Bernstein explicit-tuning templates, `MLIB-REAL-LOG-SQRT`,
`MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the final explicit theorem.

Failure policy: explicit large-horizon eta/gamma tuning is closed and consumed
by the all-horizon route below. The fifth-root term preserves polynomial
`1/delta` dependence inherited from Markov, while the theorem remains armwise
aggregate with universal pathwise sparsity. Best-arm first-order conversion,
probabilistic sparsity, exponential/self-normalized overflow, general
Freedman, anytime control, sharper constants, and ideal EXP3.P remain open.

## EXP3 Sparse-Loss Predictable-Variance Realized Markov All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAllHorizon`.
It packages the four explicit contracts into
`sparseLossPredictableVarianceLargeHorizonCondition` and defines a branch
threshold: the compiled explicit `14*gamma*T` threshold in that regime, and
the strict `(T:Real)+1` threshold otherwise.

The final theorem
`sampledPredictable_allHorizonSparseLossPredictableVarianceRealizedMarkovRegret_tail`
branches on that condition. The positive branch invokes the explicit
sparse-loss theorem after projecting the four conjunction fields. The
negative branch applies `sampledPredictable_trivialRealizedRegret_tail` with
the same internally selected eta and clipped gamma. It therefore covers every
positive horizon for `0<delta<=1` without a caller-supplied regime proof.

Local APIs/imports are the explicit sparse-loss tuning module,
`Exp3BernsteinAllHorizon`, the explicit and strict-fallback tail theorems,
the generated realized-to-selected almost-sure law behind the fallback,
classical `if`/`by_cases`, schedule positivity/stability, and existing
finite-sum/order/measure-zero APIs.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and natural sparsity; `0<delta<=1`; and universal pathwise support
sparsity. Eta and gamma are internal. No large-horizon premise, caller
eta/gamma, `s<=K`, independence, stationarity, countability, supplied
integrability, new law transport, or supplied `L1`/`L2`/lintegral premise is
required.

Retrieval uses the explicit sparse-loss route, generic Bernstein and
exponential-square all-horizon templates, `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the final all-horizon theorem.

Failure policy: all positive horizons are covered, but the complementary
branch deliberately uses the coarse zero-probability `T+1` threshold. The
refined branch retains Markov's polynomial `1/delta`, universal pathwise
sparsity, armwise aggregate loss, componentwise constant `14`, and bounded
realized deviation. A sharp active-clipping rate, best-arm first-order
conversion, probabilistic sparsity, stronger overflow, general Freedman,
anytime control, and ideal EXP3.P remain open.

## EXP3 Sparse-Loss Realized Markov A.E. Sparsity All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-AE-SPARSITY-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAESparsityAllHorizon`.
Its Lean endpoint
`sampledPredictable_allHorizonSparseLossPredictableVarianceRealizedMarkovRegret_tail_of_ae_sparsity`
uses the same internal eta, clipped gamma, branch threshold, and exact
generated trajectory measure as the preceding all-horizon theorem, but only
assumes the support cap on one common almost-everywhere event under that
measure.

The supporting small-loss APIs now accept an a.e. `L1` budget. The
sample-local support lemma transports a.e. sparsity to `L1<=S*T`;
`lintegral_mono_ae` supplies the Markov variance mean bound, and the
observed-square event inclusion uses the same a.e. event. Thus no extra
failure allocation is introduced. In the four-contract branch the proof
combines the raw a.e.-sparse tail with the compiled raw-to-tuned and
tuned-to-explicit budget comparisons; otherwise it reuses the strict `T+1`
zero-probability fallback.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and sparsity; `0<delta<=1`; and a.e. support sparsity under the exact
internally tuned generated measure. No universal pathwise cap, extra
sparsity-failure probability, caller regime proof, eta/gamma, `S<=K`,
independence, stationarity, countability, or supplied integrability is needed.

Retrieval uses the pathwise all-horizon, sparse base, and small-loss rows;
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused-built, and
externally canaried in `Tests.Basic`.

Failure policy: measure-zero exceptional sparsity paths cost no probability,
but positive-probability sparsity violations remain open. The fallback is
still coarse, and the refined branch retains Markov polynomial `1/delta`,
armwise aggregate loss, constant `14`, and bounded realized deviation.

## EXP3 Sparse-Loss Realized Markov Probabilistic Sparsity

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-PROBABILISTIC-SPARSITY`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsity`.
The Lean-facing `sampledPredictableSparsityFailure` event contains exactly the
generated trajectories with some `t<T` whose nonzero predictable-loss support
has cardinality greater than `S`.
`sampledPredictableLossMassSum_le_or_mem_sparsityFailure` proves pointwise that
`L1<=S*T` or the sample lies in that event. The small-loss observed-square,
predictable-joint, and realized-joint layers now expose matching explicit-bad-
set residual APIs.

The Markov mean cannot use `S*T` on exceptional paths. The new global lemma
uses `support.card<=arms.card` to prove `L1<=K*T` for every trajectory and then
derives
`sampledPredictableGlobalVarianceMeanBudget=(1/(gamma/K))*(K*T)`.
The regret budget therefore keeps `S*T` in the observed-square and Hedge terms
but uses the global variance mean divided by `delta/5` for overflow.
`sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegret_tail`
bounds the bad-regret event by `ofReal(delta)+mu(sparsityFailure)`, and the
`_tail_of_sparsityFailure_le` consumer turns a supplied
`mu(sparsityFailure)<=ofReal(epsilon)` into `ofReal(delta)+ofReal(epsilon)`.

Local APIs/imports are the sparse base and small-loss modules; the three
explicit-bad-set residual consumers; `Filter.Eventually.of_forall`;
`Finset.filter_subset`, `Finset.card_le_card`; `lintegral_mono_ae`;
`measure_mono`, `measure_union_le`; ENNReal division/addition; and finite-sum
and order algebra. The proof route splits each sample into sparse-or-bad,
uses `S*T` only on the variance-good realized residual event, independently
closes Markov overflow with the global `K*T` lintegral, unions the fifth
ordinary event, and normalizes the five `delta/5` terms before adding the
sparsity-failure measure.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon and delta; a natural sparsity level; and, for the practical
consumer, the exact generated-measure sparsity-failure bound. No universal or
a.e. sparsity cap, `S>0`, `S<=K`, `epsilon>=0`, `delta<=1`, independence,
stationarity, countability, supplied integrability, or event-measurability
premise is required.

Retrieval uses the a.e.-sparsity, sparse-base, and small-loss rows;
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the `delta+epsilon` consumer in `Tests.Basic`.

Failure policy: positive-probability sparsity violations are now represented
honestly, but the threshold pays the global `K*T` Markov envelope instead of
the sparse `S*T` envelope. Eta/gamma remain caller-selected; Markov remains
polynomial in `1/delta`; and the result is armwise aggregate. Do not claim the
tuned all-horizon `14*gamma*T` threshold, best-arm first-order conversion,
exponential/self-normalized overflow, general Freedman, anytime control, or
ideal EXP3.P.

## EXP3 Probabilistic-Sparsity Pathwise Variance

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsity`.
The Lean-facing
`sampledPredictableMixedSquaredVarianceSum_le_sparsePathwiseVarianceBudget_or_mem_sparsityFailure`
proves pointwise that
`sum V <= (1/(gamma/K))*(S*T)` or the generated sample belongs to the exact
sparsity-failure event. The budget
`sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget`
therefore uses `S*T` both for the observed-square mean and for the deterministic
variance threshold, with four `delta/4` confidence allocations and no Markov
overflow event.

The small-loss module now exposes observed-square, predictable-joint, and
realized-joint off-bad APIs. Their source events are explicit set differences
by `bad`, and their conclusions contain only the ordinary confidence
allocations. The final pathwise-variance theorem contains the full regret event
in the off-bad variance-good event union `sparsityFailure`, giving
`ofReal(delta)+mu(sparsityFailure)`. Its practical consumer gives
`ofReal(delta)+ofReal(epsilon)` under the exact same generated-measure failure
bound.

Local APIs/imports are the probabilistic-sparsity and small-loss modules;
`sampledPredictableLossMassSum_le_or_mem_sparsityFailure`;
`sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossMassSum`; the
three off-bad joint tails; `Set.diff`, intersection, and union;
`Filter.Eventually.of_forall`; `measure_mono`, `measure_union_le`;
`ENNReal.ofReal_add`; and finite-sum, cast, ring, and order algebra. The proof
route is pointwise sparse variance or bad, four-event off-bad confidence, one
final union with the failure event, and normalization of four quarters.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon, sparsity, and delta; and the exact generated-measure
failure bound for the epsilon consumer. No event-measurability premise,
restricted measure, universal/a.e. sparsity cap, `S<=K`, epsilon positivity,
`delta<=1`, independence, stationarity, countability, supplied integrability,
Markov inequality, or new law transport is required.

Retrieval uses the probabilistic Markov row, small-loss off-bad declarations,
sparse-base row, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, `SCN-ADVERSARIAL-FINITE`, Auer EXP3, and
inspiration-only tail/potential weapons. Status is `leanCompiled`, root
imported, focused/root built, and externally canaried at the practical
`delta+epsilon` theorem in `Tests.Basic`.

Failure policy: the caller-selected eta/gamma surface no longer pays global
`K*T`, `K^2`, or polynomial Markov `1/delta` variance costs. Eta tuning now
compiles downstream, and the large-horizon explicit gamma route now consumes
that tuning. The small-horizon/all-horizon fallback still uses the older
five-event route. The theorem remains armwise aggregate and uses bounded
realized deviation; do not claim best-arm first-order conversion, general
Freedman, anytime control, sharp active clipping, or ideal EXP3.P.

## EXP3 Probabilistic-Sparsity Pathwise-Variance Eta Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityTuning`.
The complete scale is
`S*T + predictableVarianceRadius((1/(gamma/K))*S*T, delta/4)`, and
`pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate` sets
`eta=sqrt(log K/scale)`.

The module proves positivity of the scale and eta, the exact balance
`eta^2*scale=log K`, and under `gamma<=1/2` the Hedge entropy-plus-stability
bound `3*sqrt(log K*scale)`. The raw four-event budget is contained in
`pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold`, whose three
remaining confidence radii all use `delta/4`. The generated residual theorem
preserves `delta+mu(sparsityFailure)`, and the practical endpoint consumes the
failure bound under the exact internally eta-tuned measure to obtain
`delta+epsilon`.

Local APIs/imports are the pathwise-variance probabilistic-sparsity module;
the sparse pathwise variance budget and predictable-variance radius;
`Real.log`, `Real.sqrt`, square and positivity APIs; finite casts;
field/ring/nonlinear arithmetic; `measure_mono`; and ENNReal addition. The
proof route is positive four-event scale, sqrt balancing, gamma-half stability
control, raw-to-tuned budget inclusion, and exact-measure residual
consumption.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
`0<gamma<=1/2`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon, sparsity, and delta; and the exact internally eta-tuned
generated-measure failure bound for epsilon. Eta is internal. No global
`K*T` envelope, Markov, caller eta, event measurability, restricted measure,
universal/a.e. cap, `S<=K`, epsilon positivity, `delta<=1`, independence,
stationarity, countability, supplied integrability, or new law transport is
required.

Retrieval uses the pathwise-variance base row, the previous eta-tuning algebra
template, `MLIB-REAL-LOG-SQRT`, `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, adversarial finite/Auer EXP3, and
inspiration-only tail/potential weapons. Status is `leanCompiled`, root
imported, focused/root built, and externally canaried at the eta-tuned
`delta+epsilon` theorem.

Failure policy: eta has been migrated to the four-event sparse variance scale,
so this layer no longer pays global `K*T`, `K^2`, or Markov `1/delta`. Gamma
is now selected by the compiled explicit route below. The all-horizon fallback
is the next route leaf; armwise aggregate loss, bounded realized deviation,
best-arm conversion, general Freedman, anytime control, sharp clipping, and
ideal EXP3.P remain open.

## EXP3 Probabilistic-Sparsity Pathwise-Variance Explicit Gamma

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY-EXPLICIT-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityExplicitTuning`.
The sparse good-path variance budget rewrites to `K*S*T/gamma`. The resulting
mixed exploration component is
`(K*S*(log K)^2*log(4/delta)/T^3)^(1/5)`, with neither the extra `K` nor the
polynomial `1/delta` from the global-envelope Markov route.

The module proves the log-weighted predictable-variance radius is at most
`3*gamma^2*T^2`, the balanced root is at most `2*gamma*T`, and the eta-tuned
threshold is at most `14*gamma*T`. It then defines gamma as the clipped
maximum of the sparse arm square root, the new pathwise mixed fifth root, the
Bernstein cube root, and the realized-deviation square root. Four transparent
large-horizon contracts prove clipping inactive and supply every characterized
contract. The final generated endpoints give `delta+mu(sparsityFailure)` and
`delta+epsilon` under the exact internally eta/gamma-tuned measure.

Local APIs/imports are the pathwise eta-tuned theorem and sparse variance
budget; `sampledMixedSquaredPredictableVarianceRadius`;
`log_one_div_fourth_eq_log_four_div`; the Bernstein and realized radius
dominance lemmas; sparse arm and random-square confidence/realized exploration
scales; the existing general fifth/cube/square root algebra helpers;
`Real.log`/`sqrt`/`rpow`; finite casts; field/ring/nonlinear arithmetic;
`measure_mono`; and ENNReal addition. The old Markov explicit module is used
only for reusable root/power utilities, not as probability evidence.

The proof route is budget normalization, fifth-power and cubic radius control,
balanced-root and `14*gamma*T` comparison, clipped four-component schedule,
large-horizon contract extraction, event containment under one generated
measure, and exact failure-event consumption.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and natural sparsity; `0<delta<=1`; the four inequalities
`4*S*log K<=T`,
`32*K*S*(log K)^2*log(4/delta)<=T^3`,
`8*K*log(4/delta)<=T`, and
`8*intervalVarianceProxy(0,1)*log(4/delta)<=T`; and the exact internally
tuned failure bound for epsilon. Eta and gamma are internal. No global `K*T`
envelope, Markov overflow, `K^2` mixed numerator, polynomial `1/delta`,
event measurability, restricted measure, universal/a.e. cap, `S<=K`, epsilon
positivity, independence, stationarity, countability, supplied integrability,
or new law transport is required.

Retrieval uses the pathwise eta-tuning row; reusable algebra from the old
explicit row; `MLIB-REAL-LOG-SQRT`, `MLIB-EXP-LOG-INEQUALITIES`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
adversarial finite/Auer EXP3, and inspiration-only tail/potential weapons.
Status is `leanCompiled`, root imported, focused/root and `Tests.Basic` built,
and externally canaried at the fully explicit `delta+epsilon` theorem.

Failure policy: the large-horizon explicit-gamma branch is closed on the
four-event pathwise scale and is consumed by the all-horizon theorem below.
The result remains armwise aggregate and uses bounded realized deviation; do
not claim sharp active clipping, best-arm first-order conversion, general
Freedman, anytime control, or ideal EXP3.P.

## EXP3 Probabilistic-Sparsity Pathwise-Variance All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityAllHorizon`.
It names the exact four-contract regime used by the pathwise explicit
schedule and defines an all-horizon threshold: the refined explicit threshold
(already bounded by `14*gamma*T`) in that regime, and strict `T+1`
otherwise.

The generated off-bad theorem gives `delta` after removing the exact
`sampledPredictableSparsityFailure` set. The residual theorem then gives
`delta+mu(sampledPredictableSparsityFailure)` for every positive horizon.
The practical theorem consumes the exact same-measure failure bound and gives
`delta+epsilon`. Both branches use the same internally selected clipped gamma,
pathwise balanced eta, and generated trajectory measure.

Local APIs/imports are the raw, eta-tuned, gamma-characterized, and explicit
off-bad pathwise theorems; the pathwise explicit-tuning theorem;
`Exp3BernsteinAllHorizon`; clipped-rate positivity and stability;
`sampledPredictable_trivialRealizedRegret_tail`; classical `if`/`by_cases`;
ENNReal addition order; and the generated regret and sparsity-failure events.
The proof route invokes the refined off-bad theorem in the true branch and
rewrites the threshold to `T+1` in the false branch, where
`regretBad \ sparsityBad ⊆ regretBad` feeds the strict tail under the identical
measure. The residual endpoint then adds the common bad set once.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and natural sparsity; `0<delta<=1`; and the exact internally tuned
failure-event bound for epsilon. Eta, gamma, and regime selection are
internal. No caller horizon inequality, global `K*T` Markov envelope, `K^2`
mixed numerator, polynomial `1/delta`, event measurability, restricted
measure, universal/a.e. sparsity cap, `S<=K`, epsilon positivity,
independence, stationarity, countability, supplied integrability, or new law
transport is required.

Retrieval uses the pathwise explicit-gamma row, the generic Bernstein
all-horizon fallback, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, adversarial finite/Auer EXP3, and inspiration-only
tail/potential weapons. Status is `leanCompiled`, root imported,
focused/root and `Tests.Basic` built, and externally canaried at the practical
all-horizon theorem. This fixed-comparator surface is consumed by the finite
best-supported-arm single-charge theorem below.

Failure policy: all positive horizons are covered without reintroducing the
old Markov scale, but the complementary threshold is deliberately coarse
`T+1`. The refined branch remains armwise aggregate and uses bounded realized
deviation. Sharp active clipping, general Freedman, anytime control, and ideal
EXP3.P remain separate theorem routes.

## EXP3 Probabilistic-Sparsity Pathwise-Variance Best Arm All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY-BEST-ARM-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityBestArmAllHorizon`.
It defines the hindsight best supported-arm cumulative predictable loss as
the `Finset.inf'` over the nonempty supported-arm set and proves that the
corresponding regret event is exactly the existential finite union of the
fixed-comparator events.

The confidence schedule remains armwise `delta/K`, but the common
sparsity-failure event is no longer union-bounded once per arm. New off-bad
theorems are compiled at the raw pathwise-variance, eta-tuned,
gamma-characterized, fully explicit, and all-horizon fixed-comparator layers.
The best-arm off-bad theorem unions only
`comparatorRegretBad \ sampledPredictableSparsityFailure`, yielding
`ofReal(delta)`. The strengthened residual then adds the common bad set once:
`ofReal(delta) + mu(sampledPredictableSparsityFailure)`. Its practical
consumer assumes the exact same generated measure satisfies
`mu(sampledPredictableSparsityFailure) <= ofReal(epsilon)` and concludes
`ofReal(delta) + ofReal(epsilon)` for every positive horizon. The previous
`K*mu(bad)` and `epsilon/K` theorems remain as compatibility APIs.

Local APIs/imports are the full fixed-comparator off-bad transport chain;
`Finset.inf'_le_iff` and `Finset.inf'_le`; `Set.diff` and finite-iUnion
membership; `measure_biUnion_finset_le`, `measure_mono`, and
`measure_union_le`; finite-sum comparison and constant-sum APIs; ENNReal
`ofReal` division and multiplication cancellation; finite casts; and order
algebra. The proof route rewrites the best-loss event as existence of a
supported comparator, proves `0<delta/K<=1`, distributes removal of the common
bad set through the finite comparator union, invokes the same internal
eta/gamma/generated measure for every arm, normalizes
`K*ofReal(delta/K)=ofReal(delta)`, and finally covers the full event by its
off-bad part union the common bad set.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; positive horizon and sparsity;
`0<delta<=1`; and the unscaled same-measure failure bound for the practical
endpoint. Eta, gamma, the best-arm infimum, and regime selection are internal.
No caller comparator, caller horizon inequalities, epsilon/K calibration,
global `K*T` Markov envelope, `K^2` mixed numerator, polynomial `1/delta`,
event measurability, restricted measure, universal/a.e. sparsity cap, `S<=K`,
epsilon positivity, independence, stationarity, countability, supplied
integrability, or new law transport is required.

Retrieval uses the fixed-comparator pathwise all-horizon row,
`MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`,
adversarial finite/Auer EXP3, and inspiration-only tail/potential weapons.
Status is `leanCompiled`, root imported, focused/root and `Tests.Basic` built,
and externally canaried at the single-charge practical best-arm theorem.

Failure policy: this closes the finite hindsight best-supported-arm gap, not a
stochastic-mean or first-order best-arm theorem. Single charging of the common
sparsity-failure event is now closed, but `delta/K` still introduces the
expected logarithmic arm-count cost and the complementary threshold remains
coarse `T+1`. Sharp active clipping, general Freedman, anytime control, and
ideal EXP3.P remain separate theorem routes.

## EXP3 Probabilistic-Sparsity Realized Markov Eta Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-PROBABILISTIC-SPARSITY-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityTuning`.
It defines the honest global Markov threshold
`v=((1/(gamma/K))*(K*T))/(delta/5)`, the complete Hedge scale
`S*T+sampledMixedSquaredPredictableVarianceRadius arms gamma v (delta/5)`,
and the internal learning rate `eta=sqrt(log K/scale)`.

The module proves positivity of `v`, the scale, and eta; the exact identity
`eta^2*scale=log K`; and, under `gamma<=1/2`, the bound
`entropy+stability<=3*sqrt(log K*scale)`. Unfolding the raw and tuned budgets
then gives
`sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget_le_tunedThreshold`.
The residual theorem has failure
`ofReal(delta)+mu(sparsityFailure)` under the exact internally eta-tuned
generated measure. Its practical consumer assumes the same measure gives
`mu(sparsityFailure)<=ofReal(epsilon)` and concludes
`ofReal(delta)+ofReal(epsilon)`.

Local APIs/imports are the probabilistic-sparsity residual module;
`sampledPredictableGlobalVarianceMeanBudget`;
`sampledMixedSquaredPredictableVarianceRadius`; the raw generated tail;
`Real.log`/`Real.sqrt` positivity and square identities; finite-cardinality
casts; field/ring normalization; nonlinear and linear arithmetic;
`measure_mono`; and ENNReal addition order. The proof route balances eta
against the complete global-variance scale, proves raw-budget containment
under the identical generated measure, and consumes the exact failure-event
bound without changing its measure.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
`0<gamma<=1/2`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon, sparsity, and delta; and, for the epsilon theorem, the exact
internally tuned generated-measure sparsity-failure bound. Eta is internal.
No caller eta, universal/a.e. sparsity cap, `S<=K`, `epsilon>=0`, `delta<=1`,
independence, stationarity, countability, supplied integrability,
event-measurability premise, or new law transport is required.

Retrieval uses the probabilistic-sparsity residual and pathwise eta-tuning
rows; `MLIB-REAL-LOG-SQRT`, `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `SCN-ADVERSARIAL-FINITE`,
Auer EXP3, and inspiration-only tail/potential weapons. Status is
`leanCompiled`, root imported, focused/root built, and externally canaried at
the eta-tuned `delta+epsilon` theorem in `Tests.Basic`.

Failure policy: eta tuning is closed against the global `K*T` Markov envelope
and is consumed by the explicit-gamma route below. Markov remains polynomial
in `1/delta`; all-horizon fallback, sharper decomposed or exponential
overflow, best-arm first-order conversion, general Freedman, anytime control,
and ideal EXP3.P remain open.

## EXP3 Probabilistic-Sparsity Realized Markov Explicit Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-PROBABILISTIC-SPARSITY-EXPLICIT-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityExplicitTuning`.
The global Markov budget is proved equal to
`5*K^2*T/(gamma*delta)`. Consequently the schedule uses the new fifth-root
component
`(5*K^2*log(K)^2*log(5/delta)/(delta*T^3))^(1/5)` together with the sparse
arm square root, Bernstein cube root, and realized-deviation square root.
Gamma is their clipped maximum and eta remains the exact
probabilistic-sparsity balanced learning rate.

Four explicit horizon inequalities make clipping inactive and provide
`0<gamma<=1/2` plus the quadratic, fifth-power, cubic, and realized quadratic
dominance contracts. The module proves the mixed-square radius bound, reduces
the complete tuned threshold to `14*gamma*T`, and obtains both
`delta+mu(sparsityFailure)` and `delta+epsilon` generated tails. The epsilon
premise is stated under the exact internally eta/gamma-tuned measure used by
the conclusion.

Local APIs/imports are the probabilistic-sparsity eta-tuning module; the
pathwise explicit-tuning power/root utilities; global variance mean and
mixed-square radius; Bernstein and realized radius dominance lemmas;
`Real.log`, `Real.sqrt`, and `Real.rpow`; finite casts; field/ring/nonlinear
arithmetic; `measure_mono`; and ENNReal addition order. The proof route is:
normalize the global budget, control the log-weighted radius, derive the
`14*gamma*T` gamma-characterized theorem, prove the clipped schedule
contracts, and instantiate the same-measure residual theorem.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and sparsity; `0<delta<=1`; four transparent large-horizon
inequalities; and the exact generated-measure failure bound for the epsilon
endpoint. Eta and gamma are internal. No universal/a.e. support cap, `S<=K`,
epsilon positivity, independence, stationarity, countability, supplied
integrability, event-measurability premise, or new law transport is required.

Retrieval uses the probabilistic eta-tuning and pathwise explicit-gamma rows;
`MLIB-REAL-LOG-SQRT`, `MLIB-EXP-LOG-INEQUALITIES`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the fully explicit `delta+epsilon` theorem.

Failure policy: explicit eta/gamma tuning is closed in the stated
large-horizon regime and is consumed by the all-horizon wrapper below. The
global envelope costs `K^2` in the fifth-root numerator and polynomial
`1/delta`; the theorem remains armwise aggregate. Do not claim pathwise
sparse variance, sharp active clipping, best-arm first-order conversion,
exponential/self-normalized overflow, general Freedman, anytime control, or
ideal EXP3.P.

## EXP3 Probabilistic-Sparsity Realized Markov All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-PROBABILISTIC-SPARSITY-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityAllHorizon`.
The named regime packages the same four explicit horizon inequalities. The
new threshold selects the refined `14*gamma*T` branch when they hold and the
strict `T+1` zero-probability branch otherwise, using exactly the same
internally clipped gamma, balanced eta, and generated trajectory measure.

The residual theorem proves
`mu(regret >= threshold) <= ofReal(delta) + mu(sparsityFailure)` for every
positive horizon. The practical endpoint consumes
`mu(sparsityFailure)<=ofReal(epsilon)` under that identical measure and
returns `ofReal(delta)+ofReal(epsilon)`. No caller-supplied regime proof is
required.

Local APIs/imports are the probabilistic explicit-tuning module;
`Exp3BernsteinAllHorizon`; clipped-rate positivity and stability;
`sampledPredictable_trivialRealizedRegret_tail`; classical `if`/`by_cases`;
ENNReal addition order; and generated regret/failure events. The proof route
splits on the named condition, invokes the explicit residual theorem in the
positive branch, and rewrites to `T+1` before applying the strict trivial tail
in the negative branch.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and sparsity; `0<delta<=1`; and the exact internally tuned
generated-measure failure bound for the epsilon theorem. Eta, gamma, and
regime selection are internal. No universal/a.e. support cap, caller horizon
inequalities, `S<=K`, epsilon positivity, independence, stationarity,
countability, supplied integrability, event-measurability premise, or new law
transport is required.

Retrieval uses the probabilistic explicit-gamma and pathwise all-horizon rows,
the generic Bernstein all-horizon fallback, `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the all-horizon `delta+epsilon` theorem.

Failure policy: every positive horizon is covered, but the complementary
branch is deliberately coarse `T+1`. The refined branch still pays `K^2`,
polynomial `1/delta`, armwise aggregate loss, and bounded realized deviation.
Do not claim sharp active clipping, pathwise sparse variance, best-arm
first-order conversion, stronger overflow, general Freedman, anytime control,
or ideal EXP3.P.

## EXP3 Bernstein-Square Finite Best Arm

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-BEST-ARM-ALL-HORIZON` now compiles.
The shared `Exp3BestArm` module isolates the `Finset.inf'` cumulative-loss
definition and proves that the best-arm regret event is the finite union of
fixed-comparator events. The new theorem applies the compiled all-horizon
Bernstein-square tail at `delta/K` for each supported arm under one common
eta/gamma/generated measure. `measure_biUnion_finset_le` and the ENNReal
identity `K*ofReal(delta/K)=ofReal(delta)` yield a total failure bound
`ofReal(delta)`.

The endpoint needs a probability prior, Standard Borel nonempty spaces,
measurable action singletons, decidable arms with `K>=2`, predictable
`[0,1]` losses, positive horizon, and `0<delta<=1`. It needs no comparator,
caller regime proof, sparsity assumption, event-measurability premise,
integrability premise, or new conditional-law transport. The module is root
imported and externally instantiated in `Tests.Basic`.

This closes finite hindsight best-supported-arm conversion for the fixed-tilt
Bernstein route. It does not remove the `delta/K` logarithmic arm-count cost,
the coarse `T+1` fallback, or bounded-loss Hoeffding/Azuma realized deviation.
Random predictable quadratic variation, general Freedman, anytime control,
stochastic-mean/first-order regret, sharp clipping, and ideal EXP3.P remain
open.

## EXP3 Sparse Double Pathwise Variance

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsity`
now compiles. The Lean-facing endpoint replaces the fixed realized-deviation
proxy by the exact selected-loss predictable variance. On the
sparsity-good event, the mixed-square variance budget is
`(1/(gamma/K))*(S*T)` and the realized selected-loss variance budget is
`S*T`. The corrected small-loss assembler also uses `S*T`, rather than
`K*T`, as the predictable mixed-square mean budget. Its raw Hedge scale is
therefore `S*T + sampledMixedSquaredPredictableVarianceRadius
((K/gamma)*S*T) (delta/4)`, plus the exact realized radius.

The supporting route is also compiled. `selectedLossCenteredSecondMoment`
has a finite-action MGF compensation and an armwise loss-mass upper bound.
The generic conditional wrapper explicitly requires joint
`(history,action)` loss measurability and a global `[0,1]` bound, because
`BoundedMeasurableLossWithProbabilityFloor` only provides fixed supported-arm
measurability. Generated zero/successor action laws instantiate the wrapper;
the deterministic-feedback AE identity transports selected loss to realized
loss. The shifted variance process is predictable, and the fixed-MGF
martingale assembler yields radius
`2*sqrt(V*log_+(1/delta))+log_+(1/delta)`.

The final theorem intersects the mixed and realized variance-good events.
Both satisfy a pointwise budget-or-`sampledPredictableSparsityFailure`
alternative. The predictable three-event branch is restricted by the bad-set
complement, the realized-deviation tail remains global, and the outer joint
regret event is restricted by that same complement. The residual theorem then
adds the common set exactly once, and the practical consumer returns
`ofReal(delta)+ofReal(epsilon)` from the exact same-measure failure premise.
The modules are root imported, focused/root built, and externally canaried.

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityTuning`
now closes eta tuning. It reuses the compiled sparse scale and learning rate
`eta=sqrt(log K / scale)`, bounds entropy plus stability by
`3*sqrt(log K*scale)` under `K>=2` and `0<gamma<=1/2`, and retains
`sampledRealizedPredictableVarianceRadius (S*T) (delta/4)` unchanged. Its
off-bad, residual, and practical `delta+epsilon` endpoints all use the same
internally tuned generated measure.

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityExplicitTuning`
now closes large-horizon gamma scheduling. It augments the old sparse
pathwise raw schedule by
`sqrt(S*log(4/delta)/T)` and clips the maximum at `1/2`. The four named
contracts are
`4*S*log K<=T`,
`32*K*S*log(K)^2*log(4/delta)<=T^3`,
`8*K*log(4/delta)<=T`, and
`4*S*log(4/delta)<=T`. They imply the quadratic, fifth-power, cubic, and
selected-loss quadratic dominance conditions. In particular,
`sampledRealizedPredictableVarianceRadius(S*T,delta/4)<=3*gamma*T`,
so the full tuned threshold is at most `16*gamma*T`.

The module exposes gamma-characterized and fully clipped off-bad, residual,
and practical `delta+epsilon` endpoints under one identical internally
eta/gamma-tuned generated measure. It is root imported, focused-built, and
externally instantiated at all three surfaces in `Tests.Basic`.

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityAllHorizon`
now closes the all-horizon fixed-comparator presentation. Its named condition
packages those same four contracts. The threshold is the exact explicit
branch, hence at most `16*gamma*T`, when the condition holds and strict
`T+1` otherwise. Both branches retain the same internal eta, clipped gamma,
and generated trajectory measure.

The off-bad theorem proves `mu(regretBad\sparsityFailure)<=ofReal(delta)`;
the residual adds the common bad event once; and the practical endpoint uses
the exact same-measure premise to return `ofReal(delta)+ofReal(epsilon)`.
The module is root imported, focused-built, and externally instantiated at
all three surfaces in `Tests.Basic`.

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityBestArmAllHorizon`
now closes finite hindsight best-supported-arm transport. Its threshold calls
the exact fixed-comparator all-horizon threshold at `delta/K`. The shared
`Exp3BestArm` order lemma rewrites best-arm regret as a finite comparator
union; each off-bad tail uses the same eta, gamma, and generated measure;
finite-union and ENNReal cancellation produce total confidence `delta`.

The common sparsity-failure set is removed before the union, then added once.
Consequently the residual is `ofReal(delta)+mu(bad)` and the practical theorem
needs only `mu(bad)<=ofReal(epsilon)`, not epsilon/K. The module is root
imported, focused/root and `Tests.Basic` built, and externally instantiated at
off-bad and practical surfaces.

Failure policy: eta, explicit gamma, every-positive-horizon coverage, finite
hindsight best-arm transport, and single common-bad charging are closed for
the exact double-variance route. The `delta/K` schedule retains log-K cost and
the fallback remains deliberately coarse strict `T+1`. This is not
stochastic-mean or first-order regret, sharp clipping, general Freedman,
anytime/self-normalized control, or ideal EXP3.P.

## Predictable-Compensator Fixed-Tilt Tail

`BanditRLProof.ConcentrationFixedMGF` now compiles
`measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt`. Its event
retains a random cumulative compensator:
`threshold<=sum Y` together with `sum V<=varianceBudget` has probability at
most `ofReal(exp(-tilt*threshold+varianceCoeff*varianceBudget))` whenever the
compensated increments have unit-tilt zero-budget initial and successor
conditional-MGF witnesses.

The local route is the existing fixed-tilt MGF sum theorem followed by one
real-measure/ENNReal conversion and a monotone event inclusion. Required
regularity is Standard Borel, finite zero-or-probability measure, strong
adaptedness, source MGF integrability, and nonnegative coefficients. No
independence or deterministic variance cap is introduced.

The existing realized predictable-variance EXP3 fixed-tilt endpoint was
refactored to consume this leaf at coefficient `tilt^2`, and `Tests.Basic`
contains a direct external canary. Remaining concentration gaps are one-step
MGF construction in new models, mixture/maximal tilts, and
maximal/anytime/self-normalized control; this theorem alone is not general
Freedman.

## Quadratic Fixed-MGF Delta Tail

`BanditRLProof.ConcentrationQuadraticFixedMGF` now proves
`measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail`.
For positive `c`, `V`, `cap`, and `delta`, a fixed-tail family
`P(radius<=D, W<=V)<=exp(-tilt*radius+c*tilt^2*V)` for every
`tilt in [0,cap]` yields probability at most `ofReal(delta)` at radius
`2*sqrt(c*V*log_+(1/delta))+log_+(1/delta)/cap`.

The proof uses the migrated exact quadratic tilt optimizer and a separate
`exp(-log_+)` calibration valid without `delta<=1`. The realized selected-loss
and mixed-square predictable-variance EXP3 delta theorems now call this API,
so the abstraction has two compiled consumers. A direct external canary is in
`Tests.Basic`.

Regularity at this layer is deliberately minimal: measurable ambient space,
positive scalar contracts, and the fixed-tail family. Probability,
filtration, adaptedness, conditional MGF, bounded increments, and law
transport remain obligations of each producer. Quadratic fixed-horizon
optimization is closed; one-step MGF production, maximal/anytime mixtures,
self-normalized optional stopping, and a general Freedman theorem remain open.

## Finite-Prefix Quadratic Maximal Tail

`BanditRLProof.ConcentrationQuadraticMaximal` now proves
`measure_biUnion_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail`.
For a nonempty finite `times`, every event is assigned confidence
`delta/times.card`; the compiled quadratic optimizer supplies its bound, the
Mathlib-backed finite outer-measure union sums them, and ENNReal cardinality
cancellation returns `ofReal(delta)`.

`BanditRLProof.Exp3RealizedPredictableVarianceMaximal` instantiates the route
for every `t<horizon`, hence prefix lengths `1` through `horizon` inclusive,
using the existing
realized selected-loss fixed-tilt producer and one common predictable-variance
budget. Both generic and generated-trajectory theorem surfaces have external
`Tests.Basic` canaries.

The generic contracts are measurable ambient space, decidable nonempty finite
index set, positive scale/budget/cap/delta, and fixed-tail families. The EXP3
consumer adds the probability prior, Standard Borel spaces, finite action-law
regularity, legal exploration, and predictable `[0,1]` losses. No event
measurability, independence, stationarity, `delta<=1`, or new law assumption
is added. The result has an equal-share log-cardinality cost and must not be
reported as Ville/Doob, mixture, optional-stopping, horizon-free anytime,
self-normalized, or general Freedman concentration.

## Practical selected-policy finite-sum concentration update

The `COND-EXPECT-REWARD` route now has a compiled arbitrary-ambient probability
consumer from the policy-selected reward-coordinate law to a fixed-horizon
centered-reward sum tail:
`ConditionalExpectationReward.centeredRewardSuccProcess_sum_tail_ennreal_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
It closes the analytic assembly from generated-history adaptedness and the
existing practical one-step conditional MGF to Mathlib's finite-sum
Azuma-Hoeffding API. Contracts remain explicit: probability measure, Standard
Borel sample space, countable measurable actions with measurable singletons,
timewise measurable rewards, measurable context/state/mean, raw/mean ranges,
centered kernel laws, selected-history variance ceilings, and the trim-a.e.
selected reward map law at every time.

Remaining gaps are model-side production of that selected conditional reward
law and variance domination, plus arm-wise empirical-mean/confidence and final
bandit consumers. This result covers centered rewards `1..n-1`; it does not
close confidence inversion, anytime concentration, or regret.

## Two-sided delta-confidence update

The generic concentration layer now includes the absolute-deviation ENNReal
tail, the `sqrt(2 V log(2/delta))` radius and algebraic calibration, and the
delta-valued fixed-horizon theorem for strongly adapted conditional
sub-Gaussian processes. The practical selected-policy endpoint consumes the
compiled conditional reward-law producer and returns the matching absolute
centered-sum event bound by `ENNReal.ofReal delta`.

Regularity is not hidden: finite/probability measure instances, Standard Borel
sample space, StronglyAdapted increments and conditional MGFs at the generic
layer; plus countable measurable actions, selected reward map laws,
raw/selected-mean ranges, centered kernel law, selected-history ceilings,
positive total ceiling variance, and `0 < delta <= 1` at the practical layer.
The union is an outer-measure bound, so event measurability is not added.
Arm-wise empirical means, random pull-count indexing, anytime/self-normalized
concentration, and final bandit/RL theorems remain open.

## Fixed-sample average delta-confidence update

Closed locally: deterministic positive-denominator sum-to-average event
transport, the generic strongly-adapted conditional sub-Gaussian average
theorem, and its full practical selected-policy reward-law instantiation. The
practical event averages exactly the successor rewards `1..m` by using
`range (m+1)` with a zero initial slot and divisor `m`; generic and practical
external canaries compile.

Regularity remains explicit: `m>0`, positive total proxy variance, and
`0<delta<=1`, in addition to the prior probability/Standard-Borel,
adaptedness/conditional-MGF, selected conditional reward law, measurable
surfaces, raw/mean ranges, centered kernel law, and selected-history variance
contracts. No event measurability or independence is introduced. Still open:
arm-restricted empirical means, random pull-count transport, confidence
sequences, anytime/self-normalized/Freedman bounds, and regret consumers.

## Product arm-stream fixed-sample arm confidence

Closed locally: the independent two-sided finite-sum and exact `range k`
average delta theorem, plus the stationary product arm-stream specialization
for a single arm's empirical mean. The concrete theorem derives aggregate
proxy positivity from `k>0` and `sigma2!=0`; generic and model-level external
canaries compile.

Contracts are finite measure and `iIndepFun` at the generic layer; Markov arm
kernel, stationary double-`infinitePi` arm-stream law, centered per-coordinate
`HasSubgaussianMGF`, `k>0`, nonzero proxy, and `0<delta<=1` at the UCB layer.
No filtration, conditional expectation, Standard Borel, event measurability,
or caller-supplied total variance is added. Still open on this branch are
non-product/selected-policy arm-law transport and anytime/self-normalized
confidence. Adaptive pull counts are not open in the canonical UCB route:
they are handled separately by the existing peeling/index-tail theorem.

## Selected-policy fixed-arm masked concentration

Closed locally: `ProbabilityTheory.HasCondSubgaussianMGF.indicator` preserves a
conditional sub-Gaussian witness under an event measurable in the conditioning
sigma-algebra. The practical consumer proves the generated action at `i+1` is
measurable at `F_i`, constructs a strongly adapted fixed-arm masked centered
reward process, and proves
`ConditionalExpectationReward.armMaskedCenteredRewardSuccProcess_sum_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.

The result is for one fixed arm and one fixed horizon. It retains the full
selected reward-law, raw/mean range, centered-kernel, selected-history variance,
positive total proxy, and `0<delta<=1` contracts. Its proxy is the deterministic
full `varianceCeiling i`. Missing `F_i` predictability or selected-law transport
must remain an explicit blocker. The adjacent predictable-variance leaf now
provides a separate masked-proxy route rather than silently strengthening this
older theorem.

## Conditional sub-Gaussian predictable-variance tail

Closed locally: at a fixed tilt,
`ProbabilityTheory.HasCondSubgaussianMGF.indicator_compensated_hasCondMGFUpperBoundAt`
subtracts the quadratic proxy only on a conditioning-measurable mask. The
generic finite-sum theorem retains the random cumulative masked proxy in the
joint bad event, and
`Concentration.condSubGaussian_indicator_sum_abs_tail_predictableVariance_delta`
uses the quadratic fixed-MGF optimizer plus a two-sided union to obtain an
`ENNReal.ofReal delta` bound.

Contracts are a probability/Standard Borel ambient space, filtration,
conditioning-measurable masks, StronglyAdapted masked increments and proxy
process, successor conditional sub-Gaussian witnesses, fixed horizon, positive
deterministic variance budget, and positive delta. This is not maximal,
anytime, self-normalized, or general Freedman concentration; it neither proves
the proxy-budget event nor performs peeling over arbitrary variance budgets.
Exact Nat-count peeling now compiles in the downstream generic and
selected-policy rows.

## Selected-policy successor-arm empirical mean

Closed locally: `successorArmPullCount`, `successorArmRewardSum`, and
`successorArmEmpiricalMean` align coordinates `1..n-1` with the zero-initialized
masked process. The finite-sum identity rewrites that process as selected
reward sum minus realized count times a stationary arm mean, and
`Concentration.measure_randomCount_average_abs_tail_le_of_measure_sum_abs_tail`
performs positive random-denominator transport. The practical endpoint
`ConditionalExpectationReward.successorArmEmpiricalMean_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
is externally canaried.

The older endpoint retains stationarity of the fixed arm mean across all
context histories, `DecidableEq Action`, positive full-proxy, and
`0<delta<=1`; its radius is the full horizon proxy divided by realized count.

The count-adaptive exact-fiber endpoint now also compiles:
`ConditionalExpectationReward.successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
Under a constant selected-history ceiling `sigma2`, the masked proxy identity is
exactly `sigma2 * successorArmPullCount`. On the fiber where that count equals
`k>0`, the empirical-mean confidence radius therefore charges `k*sigma2`, not
the full horizon proxy. Its additional contracts are positive coerced `sigma2`
and positive `delta`; it does not require `delta<=1` or positive full-horizon
variance.

The finite random-count endpoint now also compiles:
`ConditionalExpectationReward.successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
The generic declarations
`Concentration.measure_positive_randomCount_event_le_sum_exactCount` and
`Concentration.measure_positive_randomCount_event_le_of_exactCount_uniform`
cover a positive count event by exact fibers without measurability assumptions.
Here `successorArmPullCount_le_horizon` supplies ceiling `n`, every fiber receives
confidence `delta/n`, and the final radius is evaluated at the realized count.
The total failure is `ENNReal.ofReal delta`.

Additional contracts are `n>0`; the previous uniform `sigma2`, stationary arm
mean, selected law, and `delta>0` contracts remain. This one-arm/one-horizon
theorem is now consumed by the simultaneous endpoint below.

The finite-arm/time endpoint now compiles:
`ConditionalExpectationReward.successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
Its event is indexed by `arms.product (Finset.range T)` and evaluates each pair
at positive horizon `i+1`. `successorArmEmpiricalMeanFiniteArmTimeConfidenceShare`
allocates `delta / |arms × range T|`; each event then uses the existing internal
count peeling. `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`
normalizes the outer family, so the complete union has mass at most
`ENNReal.ofReal delta`.

The additional contracts are an explicit nonempty arm `Finset`, `T>0`, and a
stationary mean for every candidate arm; the practical selected-law,
uniform-`sigma2`, positive-`sigma2`, and positive-`delta` assumptions remain.

The random-width UCB consumer now compiles in
`BanditRLProof.Algorithms.UCBConditionalRewardLaw`. The source structure
`UCB.SelectedPolicySuccessorInitializedScoreMaxSource` records a finite set of
post-initialization times, best/chosen arm membership, positive realized counts,
and pointwise maximality of `UCB.selectedPolicySuccessorIndexAt`. Outside the
simultaneous event,
`meanGap_le_two_radius_of_not_badEvent` applies the existing deterministic UCB
algebra at the sample-dependent radius. Consequently
`measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
bounds any charged large-gap selection by `ENNReal.ofReal delta`.

The adapter intentionally does not use `UCB.finiteHorizonConfidenceBadEvent`:
that older API has a sample-independent radius, whereas this theorem uses the
realized pull count. Its additional compatibility contract is `Action : Type`,
matching the current universe-0 UCB score algebra. Failure policy moves to
the generated-policy leaf below, which now closes source construction,
initialization, and expected pull-count transport. Closed-form threshold
selection, regret assembly, and maximal/anytime/self-normalized or general
Freedman control remain open.

## Generated selected-policy UCB count closure

Card `LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-RANDOM-WIDTH-PULLCOUNT` is now
`leanCompiled`. Its Lean surface constructs the finite-history policy,
generated action trace, pair-history reconstruction invariant, one-pass
initialization, positive-count schedule, and concrete initialized score-max
source. Exceeding a threshold `B` yields a selected post-initialization time
whose prior chosen-arm count is at least `B`; the previous random-width
large-gap theorem then supplies the tail.

The remaining radius algebra is explicit rather than abstract: with `L_T`
equal to `selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta`, the two
contracts are `32*sigma2*L_T < gap^2*B` and `4*L_T < gap*B`. They compile to
the high-probability count bound and, using a measurable bounded Nat
integration lemma, the ENNReal expectation bound `B + T*ofReal(delta)`.
Focused, root, and `Tests.Basic` builds pass. Retrieval evidence is local
compiled Mathlib-backed code through the prior large-gap, finite arm/time,
Finset pull-count, measure, integral, log, and sqrt APIs; theorem cards and
weapon-only entries are not proof evidence.

The closed-form integer threshold now compiles in the next leaf. The remaining
gap is regret assembly and concrete-model selected-law production, not policy
construction, threshold inversion, or expected-count transport.

## Explicit threshold and practical expected count closure

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-EXPLICIT-THRESHOLD-EXPECTED-PULLCOUNT`
is `leanCompiled`. The threshold is `Nat.ceil (max quadratic linear) + 1`, with
quadratic term `32*sigma2*L_T/gap^2` and linear term `4*L_T/gap`. `Nat.le_ceil`
and positive denominator transport establish both strict inequalities, so the
random-width radius inversion is fully internal.

A concrete-source large-gap producer now names the practical selected-law
instantiation that was previously hidden inside the threshold-parametric count
theorem. The final public theorem combines that producer with measurable Nat
count integration and yields the explicit-threshold ENNReal expected count
under the complete practical law surface. It requires a positive chosen-arm
gap but no external large-gap event, integer threshold, radius condition, or
numeric inequality.

Focused module, root, and `Tests.Basic` builds pass, and the declaration is
externally canaried. Retrieval evidence is local compiled code plus Mathlib
`Nat.ceil`, order/division, measure, and lower-integral APIs; theorem-card and
weapon-only text is not proof evidence. The finite-arm pseudo-regret consumer
now compiles in the next leaf.

## Practical selected-policy UCB pseudo-regret closure

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-EXPLICIT-THRESHOLD-PSEUDOREGRET`
is `leanCompiled`. Its successor-action adapter maps generated coordinates
`1..T` onto pseudo-regret coordinates `0..T-1`, proves the corresponding
pull-count equality, and aligns the model's Real mean gap with its rational
`FiniteBanditModel.gap`.

The generic ENNReal assembly theorem uses the existing scalar pseudo-regret
pull-count identity, finite `lintegral` summation, constant multiplication, and
model gap nonnegativity. Only positive-gap arms require count bounds; zero-gap
terms disappear. The practical specialization supplies every such bound from
the explicit-threshold selected-law theorem and produces the finite sum of gap
times threshold plus gap times `T*ofReal(delta)`.

The full selected reward law, measurability, range, centered-kernel,
stationary-model-mean, positive uniform variance, probability/Standard-Borel,
positive horizon, and positive delta contracts remain explicit. Focused,
root, and `Tests.Basic` builds pass. Compiled local declarations and Mathlib
Finset/measure/lower-integral APIs are retrieval evidence; theorem cards and
weapon-only routes are not proofs. The closed gap is finite-arm ENNReal
pseudo-regret assembly including zero-gap arms. The textbook RHS simplification
now compiles downstream.

## Practical UCB textbook gap-sum closure

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-TEXTBOOK-GAP-SUM-PSEUDOREGRET` is
`leanCompiled`. The one-arm route proves
`gap * threshold <= 32*sigma2*L_T/gap + 4*L_T + 2*gap`: it reuses the canonical
`Nat.ceil_lt_add_one` pattern, bounds the nonnegative `max` by the sum of its
branches, and normalizes positive-gap divisions. The ENNReal wrapper then
transports this Real inequality without an infinity side condition.

The finite consumer filters `Finset.univ` to positive model gaps. Zero-gap
arms are discharged from `FiniteBanditModel.gap_nonneg`; the original
`gap*T*ofReal(delta)` failure contribution is unchanged. The end-to-end
selected-law theorem composes this bound with the already compiled practical
pseudo-regret endpoint and exposes the textbook filtered finite sum directly.

Focused module, root, and `Tests.Basic` builds pass. Local compiled declarations
plus Mathlib ceil, order, field, Finset filter, and ENNReal cast APIs are the
retrieval evidence; theorem cards and weapon-only routes are not proofs. The
closed gap includes threshold removal, reciprocal-gap simplification, and
zero-gap filtering. Its UCB canonical-law specialization and reward-only
trajectory theorem now compile downstream.

## Canonical reward-only trajMeasure closure

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-CANONICAL-REWARD-TRAJMEASURE-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The module defines the generated-UCB reward-history step
kernel family, proves every member is Markov, exposes the corresponding
`Kernel.trajMeasure` and probability instance, packages the canonical
finite-pair selected-reward source, and exports the exact trim-a.e.
`historyFiltrationSucc` `condExpKernel.map` law.

The final canonical theorem consumes that law internally and applies the
already compiled practical textbook finite-sum endpoint. Its proof route is
the canonical trim selected-law theorem, comap-to-history-filtration source
transport, source projection, and practical pseudo-regret composition.
Required contracts are a probability initial reward law; measurable context,
state and mean; Markov reward kernel; centered reward-kernel law; stationary
model means; positive selected-history variance; `K,T>0`; `delta>0`; mean
range; and pointwise raw range.

Focused module, root, and `Tests.Basic` canaries are the local evidence, with
Mathlib kernel/trajectory/measure APIs as upstream evidence. The generated-UCB
canonical law premise is closed. The stronger centered-kernel endpoint below
also closes the obsolete pointwise `hraw` and mean-range surface.

## Centered-kernel no-range canonical closure

Card
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. Audit of the old concentration chain showed that
`CenteredRewardKernelLaw` already contains the exact selected-law centered
integrability, zero integral, and sub-Gaussian MGF facts. The range source was
therefore redundant rather than a genuine support obligation.

The replacement route transfers the target-law MGF through the canonical
trim-a.e. selected reward-map identity, constructs the successor conditional
MGF under `historyFiltrationSucc`, masks by the predictable arm event, and
uses the random predictable proxy `sigma2 * successorArmPullCount`. Exact
positive-count confidence, finite count peeling, finite arms-times union,
generated-UCB large-gap control, explicit expected counts, pseudo-regret
assembly, and textbook threshold simplification all compile in one module.

The final canonical theorem requires only probability initial law, measurable
context and mean, `CenteredRewardKernelLaw`, stationary model means, positive
selected-history variance ceiling, positive `K,T`, and positive `delta`. It
has no raw or mean range, no support restriction, and no caller law premise.
Focused, root, and `Tests.Basic` builds pass; compiled declarations plus the
Mathlib conditional-MGF, predictable-variance, finite-union, and integration
APIs are direct evidence. This canonical ENNReal UCB textbook pseudo-regret
route is closed, and its Real/Bochner presentation is closed downstream.
Common bounded context-independent centered-kernel constructors also compile
downstream; no context-dependent, anytime/Freedman, or unrelated final theorem
is claimed.

## Canonical Real expectation closure

Card
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The audit found no missing probabilistic leaf: the only gap
between the canonical ENNReal endpoint and a textbook Real expectation was
finite-horizon integrability plus finite ENNReal normalization.

`integrable_real_pullCount_of_measurable_action` now supplies the generic
bounded-measurable pull-count adapter under `IsFiniteMeasure`.
`integrable_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction`
combines it with the existing finite-arm pseudo-regret decomposition. The final
canonical theorem proves pointwise nonnegativity, applies
`ofReal_integral_eq_lintegral_ofReal`, consumes the prior centered-kernel
lintegral theorem, proves the positive-gap finite sum is finite, and converts
every sum/addition/product/`ofReal` term to the explicit Real expression.

The final API has no external integrability hypothesis and no `.toReal` RHS.
Its probability, measurability, centered-kernel, stationary-mean, variance,
horizon, and confidence contracts are unchanged. Focused and `Tests.Basic`
builds pass. The exact compiled declarations plus Mathlib Bochner integral and
ENNReal conversion APIs are direct evidence. This Real presentation gap is
closed and consumed by the bounded finite-arm route below.

## Bounded finite-arm law closure

Card
`LOCAL-LEAF-UCB-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The prior abstract final theorem required callers to provide
`CenteredRewardKernelLaw`, a measurable mean, a selected-history variance
ceiling, and a compatible canonical trajectory setup. For stationary bounded
finite-arm laws those obligations are now constructed internally.

The generic direct-subGaussian constructor derives centered integrability and
zero integral from the MGF witness plus the exact raw mean. The bounded
constructor derives the MGF through
`boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`. A separate strict-
positivity leaf closes the nondegenerate interval proxy obligation. The UCB
consumer then specializes to `Unit` context, constant model means and variance,
the context-independent arm-law kernel, and the default-arm initial law.

The final external contracts are per-arm probability measures, common
`lo < hi`, a.e. measurable reward casts, common a.s. interval support, exact
integrals equal to `model.mean`, a default arm, positive horizon, and positive
delta. No abstract centered law, selected law, trajectory law, variance bound,
or integrability witness remains. Focused and `Tests.Basic` builds pass, and
the card plus retrieval indexes record the older ETC constructor as discovery
evidence rather than a UCB dependency. This common-interval stationary finite-
arm UCB Real expected-regret route is closed and consumed by the armwise route.

## Armwise bounded finite-arm law closure

Card
`LOCAL-LEAF-UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The remaining unequal-range gap was not probabilistic: each
arm already had a bounded centered MGF, but UCB needed one positive deterministic
proxy. The new supporting leaves define that proxy as the finite supremum of
the armwise interval proxies, prove every arm is dominated by it, and prove it
strictly positive from `model.hK` and pointwise nondegenerate intervals.

`contextIndependentArmwiseBoundedCenteredRewardKernelLaw` packages the per-arm
bounded MGF witnesses without collapsing the ranges. The final theorem selects
the finite maximum internally and reuses the canonical Real theorem. Its only
external contracts are per-arm probability laws, per-arm measurable bounded
support with `lo arm < hi arm`, exact model means, a default arm, positive
horizon, and positive delta. No common range or caller variance ceiling remains.

Focused module and `Tests.Basic` builds pass. Exact declarations, `Finset.sup`,
`Finset.le_sup`, the Mathlib-backed bounded MGF wrapper, and the prior canonical
Real theorem are direct evidence. Armwise stationary bounded finite-arm UCB is
closed; context-dependent/nonstationary, anytime/Freedman, cross-toolchain, and
other algorithm routes remain separate.

## Direct sub-Gaussian finite-arm law closure

Card
`LOCAL-LEAF-UCB-SUBGAUSSIAN-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The audit separates two obligations that bounded support had
previously discharged together: producing centered MGF witnesses and choosing
one deterministic positive UCB proxy. The new endpoint accepts the MGF
witnesses directly and computes the proxy as the finite supremum of their
armwise `NNReal` parameters.

The maximum-proxy leaves prove selected-arm domination with `Finset.le_sup` and
strict positivity from the existence of one positive proxy. The existing
context-independent direct constructor derives centered integrability and zero
integral from the MGF witness and exact mean. The final theorem then reuses the
canonical Real trajectory theorem with no support or range assumptions.

Focused, root, and `Tests.Basic` builds pass. Exact declarations,
`MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-FINSET-SUMS`, `Finset.sup`,
`Finset.le_sup`, and the canonical Real card are direct evidence. The stationary
finite-arm direct-subGaussian UCB route is closed. An all-zero-proxy/noiseless
special theorem, context-dependent/nonstationary rewards, anytime/Freedman,
cross-toolchain import, and other algorithms remain separate.

## Context-dependent bounded reward-kernel closure

Card
`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-BOUNDED-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The earlier canonical Real theorem already accepted an
arbitrary context-dependent centered reward kernel, but callers still had to
assemble `CenteredRewardKernelLaw` and its integrability/centering obligations.
The new algorithm-independent constructors close that gap for both direct
pointwise MGF witnesses and common bounded selected laws.

`centeredRewardKernelLaw_of_hasSubgaussianMGF` obtains centered integrability
from `HasSubgaussianMGF.integrable`, raw integrability by adding the mean, and
zero centered integral with `integral_sub`. The bounded constructor applies the
existing Mathlib-backed Hoeffding MGF wrapper at every context/action pair.
`RewardKernel.isProbabilityMeasure_apply` supplies the selected-law instances.

The UCB endpoint allows reward distributions to vary with context/action while
requiring exact stationary arm means and common nondegenerate support. It
constructs the interval proxy and every selected-law/trajectory/regularity
witness internally, then returns the explicit Real positive-gap textbook sum.
Context-dependent means are outside the stationary pseudo-regret contract;
context/action-dependent ranges, direct sub-Gaussian ceilings, nonstationary
regret, and anytime/Freedman routes remain open.

## Context-dependent direct sub-Gaussian reward-kernel closure

Card
`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The bounded route's generic direct-MGF constructor now feeds
a public canonical Real UCB theorem without passing an abstract
`CenteredRewardKernelLaw` through the theorem boundary.

The external probability contract is exact pointwise selected-law means equal
to `model.mean arm`, centered `HasSubgaussianMGF` witnesses with proxies
`varianceProxy ctx arm`, one positive global `sigma2`, and uniform domination
`varianceProxy ctx arm <= sigma2`. MGF regularity supplies centered
integrability; adding the mean supplies raw integrability; `integral_sub`
supplies zero centering. The canonical route constructs selected law and
trajectory law internally and returns the explicit Real textbook gap sum.

No bounded support, reward-range premise, context independence, caller
centered-law, selected-law transport, trajectory law, or integrability witness
remains. The caller ceiling is not an avoidable artifact: automatic maxima need
finite/compact/bounded context structure. Such automatic ceilings, noiseless
zero-proxy models, context-dependent means/nonstationary regret, and
anytime/Freedman routes remain open.
