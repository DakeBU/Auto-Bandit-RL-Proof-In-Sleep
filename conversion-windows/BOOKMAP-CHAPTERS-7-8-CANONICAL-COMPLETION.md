# Conversion Window: Book Map Chapters 7--8 canonical completion

Task id: `BOOKMAP-CHAPTERS-7-8-CANONICAL-COMPLETION`

## Child gates

| Gate | Natural-language target | Exact local terminal | Status |
| --- | --- | --- | --- |
| `CH7-EXP3-CANONICAL-COMPLETION` | canonical generated EXP3 has the scoped expected, fixed-window best-arm, fixed-process all-prefix, and sparse/variance-sensitive endpoints | `Exp3.sampledPredictable_expectedRegret_le_four_mul_sqrt`, `Exp3.sampledPredictable_allHorizonBernsteinSquareBestArmRealizedRegret_tail`, `Exp3.measure_sampledRealizedRegretGeometricAllTimeFailureSet_le`, and the sparse terminal | accepted |
| `CH8-TSALLIS-FTRL-CANONICAL-COMPLETION` | canonical scheduled half-Tsallis FTRL generated on IID bounded finite-arm reward laws reaches a logarithmic reciprocal-gap expected-regret theorem | `Tsallis.integral_sampledScheduledHalfTsallisFiniteArmIIDRewardLawRegret_le_log` | accepted |

## Chapter 7 symbol mapping

| Mathematical object | Lean surface | Status |
| --- | --- | --- |
| potential one-step | `Exp3.exp_neg_mul_le_one_sub_add_sq_of_nonneg`, `Exp3.log_totalWeight_succ_sub_le_of_nonneg` | compiled local |
| deterministic Hedge | `Exp3.hedge_regret_le_log_card_div_add_eta_mul_mixedSquaredLoss_of_nonneg` | compiled local |
| IW first/second moments | `Exp3.sum_prob_mul_importanceWeightedLoss_eq_loss`, `Exp3.sum_prob_mul_mixedSquaredImportanceWeightedLoss_eq_sum_loss_sq` | compiled local |
| recursive generated law | `Exp3.exploredHistoryAlgorithm`, `Exp3.sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment` | compiled local |
| predictable observed moments | `Exp3.sampledPredictableObserved_finiteHorizon_first_second_moment` | compiled local |
| exploration bias | `Exp3.sampledTrajectory_finiteHorizon_explorationBias_secondMoment` | compiled local |
| tuned expected regret | `Exp3.sampledPredictable_expectedRegret_le_four_mul_sqrt` | compiled local; horizon-indexed tuning |
| fixed-window best arm | `Exp3.sampledPredictable_allHorizonBernsteinSquareBestArmRealizedRegret_tail` | compiled local; horizon-indexed law |
| all-prefix parents | `Exp3.measure_sampledPredictableRegretGeometricAllTimeFailureSet_le`, `Exp3.measure_sampledRealizedDeviationGeometricAllTimeFailureSet_le`, `Exp3.sampledTrajectoryRealizedRegret_eq_predictableRegret_add_realizedDeviation` | compiled local; fixed process/comparator |
| all-prefix terminal | `Exp3.measure_sampledRealizedRegretGeometricAllTimeFailureSet_le` | compiled local |
| sparse extension | `Exp3.sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_sparsityFailure_le` | compiled local; explicit sparsity-failure budget |

## Chapter 8 symbol mapping

| Mathematical object | Lean surface | Status |
| --- | --- | --- |
| half-Tsallis regularizer/minimizer | `Tsallis.negEntropyRegularizer`, `Tsallis.halfTsallisMinimizer` | compiled local |
| one-step stability | `Tsallis.sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_powerSum_half_of_minimizers` | compiled local |
| scheduled generated selector | `Tsallis.canonicalHalfTsallisScheduleGeneratedSelectorMeasurability` | compiled local |
| generated conditional action law | `Tsallis.sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment` | compiled local |
| score/probability alignment | `Tsallis.halfTsallisScheduledMinimizer_observedEstimatedLoss_eq_probabilityAtTime` | compiled local |
| pathwise stability plus penalty | `Tsallis.sampledScheduledHalfTsallisEstimatedRegret_pointMass_le_stability_add_penalty` | compiled local |
| all-rate expected stability | `Tsallis.integral_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound` | compiled local |
| generated expected regret | `Tsallis.integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_allRateBound` | compiled local |
| fixed-gap self bound | `Tsallis.integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_fixedGap` | compiled local |
| finite IID law/gap bridge | `Tsallis.iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap` | compiled local producer |
| finite IID terminal | `Tsallis.integral_sampledScheduledHalfTsallisFiniteArmIIDRewardLawRegret_le_log` | compiled local |

## Retrieval and scope boundary

- EXP3: `MLIB-FINSET-SUMS`, `MLIB-EXP-LOG-INEQUALITIES`,
  `MLIB-ORDER-ALGEBRA`, `MLIB-PROBABILITY-KERNEL`, and
  `MLIB-MEASURE-INTEGRAL`.
- Tsallis-FTRL: `MLIB-REAL-RPOW-TSALLIS`, `MLIB-CONVEX-LINALG`,
  `MLIB-FINSET-SUMS`, `MLIB-EXP-LOG-INEQUALITIES`,
  `MLIB-MEASURE-INTEGRAL`, and `MLIB-ASYMPTOTICS`.
- The exact nonclaims and extensions are listed in the task packet.  A compiled
  chapter may retain visibly partial/planned/blocked results outside its
  canonical completion definition.
