# Conversion Window: Book Map Chapters 5--6 canonical completion

Task id: `BOOKMAP-CHAPTERS-5-6-CANONICAL-COMPLETION`

## Child gates

| Gate | Natural-language target | Exact local terminal | Status |
| --- | --- | --- | --- |
| `CH5-OFUL-CANONICAL-COMPLETION` | one finite-action, finite-feature, horizon-free telescoping OFUL policy has generated all-time confidence, all-horizon high-probability pseudo-regret, and explicit stopping consumers; a separate horizon-indexed fixed-model family has expected-average consistency | `OFUL.telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization` plus the expected/stopping terminals | accepted: canary, full gate, site, and independent review pass |
| `CH6-THOMPSON-STATIONARY-CANONICAL-COMPLETION` | the recursive posterior-sampling policy probability-matches on its actual generated history and its stationary latent-stream trajectory has the stated Bayesian regret bound | `Thompson.stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le` | accepted: concrete canary, optimality contract, full gate, site, and independent review pass |

## Chapter 5 symbol mapping

| Mathematical object | Lean surface | Source status |
| --- | --- | --- |
| clipped inverse-Gram widths | `OFUL.sum_range_min_prefix_update_le_two_trace_average_log` | compiled local |
| conditional MGF | `OFUL.fixedDirectionCompensatedScore_hasMGFUpperBoundAt` | compiled local |
| ridge confidence ellipsoid | `OFUL.measure_finiteHorizonRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le` | compiled local |
| horizon-free policy | `OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm` | compiled local |
| reward-law producer | `OFUL.CanonicalLinearSubgaussianEnvironmentLaw` and `canonicalScheduledPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment` | compiled local producer |
| all-time confidence | `measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le_of_linearSubgaussianEnvironment` | compiled local |
| all-horizon regret | `telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization` | compiled local |
| expected consistency | `canonicalStandardExpectedAveragePseudoRegret_tendsto_zero` | compiled local |
| bounded stopping | `integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_endpoint_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization` | compiled local and typed canary |
| unbounded stopping | `integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_stoppingTimeRoundSecondMoment_add_initialGap_mul_sqrt_stoppingTimeRoundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime` | compiled local |

The telescoping policy constructor has no terminal horizon argument.  The same
syntactic policy/environment/trajectory-measure chain occurs in the all-time,
all-horizon, bounded-stopping, and square-integrable-stopping typed canaries.
Expected-average consistency is a separate horizon-indexed policy family using
confidence `1 / (horizon + 1)^2`; it is not evidence about that one telescoping
policy.  The reward-law structure contains
theta norm plus initial/successor centered sub-Gaussian kernel laws; it does
not contain confidence or regret conclusions.

## Chapter 6 symbol mapping

| Mathematical object | Lean surface | Source status |
| --- | --- | --- |
| posterior law | `PosteriorKernel.canonicalPosterior_kernel_ae_eq_condDistrib_of_pair_map_eq` | compiled local |
| one-step matching | `Thompson.canonicalSampler_condDistrib_action_ae_eq_bestAction` | compiled local |
| recursive policy | `Thompson.uniformReferenceThompsonAlgorithm` | compiled local |
| actual-history matching | `uniformReferenceThompsonAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction` | compiled local |
| Bayes decomposition | `integral_trajectoryBayesMeanRegret_eq_add_historyScore`, `integral_trajectoryBayesMeanRegret_eq_add_clippedUCB` | compiled local |
| stream support | `canonicalLatentArmStreamTrajectory_reward_eq_rewardFromArmStream_ae` | compiled local |
| two confidence consumers | `stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_sum_mean_bestAction_sub_clippedUCB_le`, `stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_sum_clippedUCB_action_sub_mean_le` | compiled local |
| mean-optimal selector contract | `IsOptimalMeanSelector mean bestAction` | compiled local and discharged by concrete canary |
| stationary terminal | `stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le` | compiled local and concrete canary |

## Assumption ledger

| Route | Explicit contracts |
| --- | --- |
| OFUL | `0<K`; finite/decidable/nonempty feature type; positive `lambda` and `R`; `0<delta<=1`; nonnegative `S,L2`; feature norm-square bounded by `L2<=lambda`; optimal arm; canonical kernel-level centered sub-Gaussian producer; stopping endpoint additionally requires its canonical filtration and `SquareIntegrableFiniteStoppingTime` |
| Thompson | probability prior; Standard Borel/nonempty environment; finite/nonempty actions; Markov reward kernel; measurable best action; pointwise `IsOptimalMeanSelector mean bestAction`; measurable mean surface; `l<=u`; all means in `[l,u]`; centered `HasSubgaussianMGF`; nonzero `sigma2`; canonical augmented latent stream |

## Retrieval and status boundary

- OFUL cards: `MLIB-CONVEX-LINALG`, `MLIB-MARTINGALE-STOCHASTIC`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-REAL-LOG-SQRT`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-ASYMPTOTICS`.
- Thompson cards: `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-POSTERIOR`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`.
- LML declarations remain `card-only`/toolchain-blocked for literal identity.
  Local mathematical compatibility is not an upstream import.

## Scope boundary

The exact nonclaims and extensions are listed in the task packet.  A compiled
chapter may contain visibly partial/planned/blocked extensions outside its
canonical completion definition.
