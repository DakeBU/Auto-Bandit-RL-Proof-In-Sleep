# Proof Export: Chapter 13 Lower-Bound Basic Ideas and Gaussian Testing

Task id: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Status: `partial` whole-chapter contract; compiled core theorem route and new
semantic/testing leaves.

## Model and notation

For a fixed-horizon expected pseudo-regret functional `R`, an explicit policy
class `P`, and an environment class `E`, the worst-case value is
`sup_(nu in E) R(pi,nu)` and the minimax value is the infimum of this quantity
over `pi in P`. A policy is minimax optimal only when it is admissible and
attains this infimum for the same classes and horizon-indexed `R`.

For the opening two-point test in Section 13.1, the distribution-level
sample-mean observation law is `N(mu,1/n)`. The midpoint decision returns
`Delta` when the observation is at least `Delta/2`, and zero otherwise.
The canonical finite product of `n>0` copies of `N(mu,1)` is mapped by the
arithmetic mean to exactly this law.

## Compiled proof map

1. `worstCaseExpectedRegret` and `minimaxExpectedRegret` implement the source
   supremum/infimum order. `IsMinimaxOptimal` packages admissibility and
   attainment without claiming that a general infimum has a minimizer.
2. `gaussianIIDSumLaw` identifies the canonical finite-product sum as
   `N(n*mu,n)`, and `gaussianIIDSampleMeanLaw` scales it to `N(mu,1/n)`.
   `twoPointGaussianThresholdDecision_zero_error_event` and
   `twoPointGaussianThresholdDecision_gap_error_event` identify the exact
   midpoint error sets. `hasSubgaussianMGF_id_gaussianReal_zero` and
   `hasSubgaussianMGF_gap_sub_id_gaussianReal` derive the centered and
   reflected Gaussian sub-Gaussian proxies from Mathlib's exact MGF.
   `gaussianSampleMeanThresholdRisk_le_exp` then proves the honest
   `exp(-n*Delta^2/8)` maximum-error Chernoff bound for both hypotheses.
3. `exists_leastExploredAlternative` chooses the least-sampled alternative
   from the exact expected pull budget. `baseEnvironmentRegret` and
   `changedEnvironmentRegretLowerBound` encode Eqs. (13.2)--(13.3), while
   `max_base_changed_regretLowerBound_ge_half_sub_error` keeps the cross-law
   discrepancy as a visible premise.
4. The separately compiled Chapter 14--15 history-KL/testing construction
   supplies the missing information bridge. The caller-free
   `unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` then
   proves Theorem 13.1 for unit-variance Gaussian means in `[0,1]^k`, `k>1`,
   and `n>=k`, with the explicit universal constant `1/54`.

## Exact compiled declarations

- `LowerBounds.worstCaseExpectedRegret`
- `LowerBounds.minimaxExpectedRegret`
- `LowerBounds.IsMinimaxOptimal`
- `LowerBounds.IsMinimaxOptimal.mem_policyClass`
- `LowerBounds.IsMinimaxOptimal.eq_minimaxExpectedRegret`
- `LowerBounds.expectedRegret_le_worstCaseExpectedRegret`
- `LowerBounds.minimaxExpectedRegret_le_worstCaseExpectedRegret`
- `LowerBounds.le_minimaxExpectedRegret`
- `LowerBounds.exists_alternative_le_average`
- `LowerBounds.alternativeExpectedPullBudget_le`
- `LowerBounds.exists_leastExploredAlternative`
- `LowerBounds.baseEnvironmentRegret`
- `LowerBounds.changedEnvironmentRegretLowerBound`
- `LowerBounds.max_base_changed_regretLowerBound_ge_half_sub_error`
- `LowerBounds.max_base_changed_regretLowerBound_ge_half`
- `LowerBounds.gaussianSampleMeanVariance`
- `LowerBounds.gaussianSampleMeanVariance_pos`
- `LowerBounds.gaussianSampleMeanLaw`
- `LowerBounds.gaussianIIDObservationLaw`
- `LowerBounds.gaussianCoordinateAverage`
- `LowerBounds.gaussianIIDSumLaw`
- `LowerBounds.gaussianIIDSampleMeanLaw`
- `LowerBounds.twoPointGaussianThresholdDecision`
- `LowerBounds.twoPointGaussianThresholdDecision_zero_error_event`
- `LowerBounds.twoPointGaussianThresholdDecision_gap_error_event`
- `LowerBounds.gaussianSampleMeanZeroErrorProbability`
- `LowerBounds.gaussianSampleMeanGapErrorProbability`
- `LowerBounds.hasSubgaussianMGF_id_gaussianReal_zero`
- `LowerBounds.hasSubgaussianMGF_gap_sub_id_gaussianReal`
- `LowerBounds.gaussianReal_zero_Ici_le_exp_neg_sq_div_two_variance`
- `LowerBounds.gaussianReal_gap_Iio_half_le_exp_neg_sq_div_two_variance`
- `LowerBounds.gaussianSampleMeanZeroErrorProbability_le_exp`
- `LowerBounds.gaussianSampleMeanGapErrorProbability_le_exp`
- `LowerBounds.gaussianSampleMeanThresholdRisk`
- `LowerBounds.gaussianSampleMeanThresholdRisk_le_exp`
- `LowerBounds.unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt`

## Required blockers and optional boundary

### MOSS source-policy layer (focused compilation)

Write L(x)=log(max(1,x)) and b(n,k,s)=sqrt(4 L(n/(ks))/s).
The new `MOSS` namespace defines `logPlus`, `radius`, `index`, `action`,
`historyAction` and `historyAlgorithm`. At zero-based times t<k, the action
is arm t; afterward it maximizes empiricalMean+b using the existing real
argmax. Inclusive history at t supplies the action at t+1.
`measurable_historyAction` composes measurable history means/counts with
the count-indexed radius and existing measurable finite argmax; the
deterministic kernels and initial Dirac arm form the common history policy.

`radius_sq` retains the exact source factor four.
`action_initial_arm`, `action_index_max`, `historyAction_initialization`,
`historyAction_index_max`, and `historyAlgorithm_policy_apply` certify
these equations. `selected_index_gt_mean_add_half_gap` proves the
source proof step: from bestIndex >= bestMean-d and gap>2d, maximality
implies selectedIndex > selectedMean+gap/2, by linear arithmetic.
`logPlus_nonneg`, `radius_nonneg`, `radius_zero`, and `action_of_lt`
cover basic and initialization branches.

These modules and `Tests/MOSSCanary.lean` compile with baseline axioms only.
The new root/Tests integration run is separate from the completed exact
Gaussian gate. No expected-regret theorem follows yet: the probabilistic
optimism-deficit bound, maximal inequality/peeling and occupancy integration
remain required.

- Compiled: both printed Mills-ratio bounds in Eq. (13.4) and their exact
  Eq. (13.1) rescaling. Public endpoints are
  `LowerBounds.gaussianMills_lower_integral`,
  `LowerBounds.gaussianMills_upper_integral`, and
  `LowerBounds.gaussianSampleMeanZeroErrorProbability_source_bounds`.
  The latter assumes n>0 and Delta>0, sets q=n*Delta^2, and bounds the
  zero-mean midpoint error between sqrt(8/pi)*exp(-q/8) divided by
  sqrt(q)+sqrt(q+16) (lower) and sqrt(q)+sqrt(q+32/pi) (upper).
  Proof: derivative comparison and improper FTC for the lower integral;
  single-turning-point error comparison for the upper integral; Gaussian
  density standardization and square-root rescaling for the probability.
  These are independent of the weaker Chernoff companion.
- Required connected claim: compile the MOSS/Algorithm 7 upper theorem on the
  stated finite-arm 1-subgaussian class before claiming the main-prose
  constant-factor near-minimax consequence.
- Optional: Notes 13.2 and Exercises 13.1--13.2 are not formalized and do not
  block the frozen whole-main-text contract.
