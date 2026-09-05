# Proof Export: ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory

Task id: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

Status: compiled main-text proof export. Definition 16.1, the source
mean-to-gap producer, Theorem 16.2, Lemma 16.3, and Theorem 16.4 compile.

## Compiled Lean declarations

The source-environment bridge uses:

- `LowerBounds.FiniteMeanBanditEnvironment`
- `LowerBounds.FiniteMeanBanditEnvironment.gap`
- `LowerBounds.FiniteMeanBanditEnvironment.gap_nonneg`
- `LowerBounds.FiniteMeanBanditEnvironment.mean_eq_of_armLaw_eq`
- `LowerBounds.oneArmMeanIncrease`
- `LowerBounds.oneArmChangedMargin`
- `LowerBounds.oneArmMeanIncrease_sub_gap_eq_changedMargin`
- `LowerBounds.oneArmMeanChange_produces_gap_contract`

The exact finite-time terminal uses:

- `LowerBounds.expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed`
- `LowerBounds.expectedPullCount_ge_log_regret_changeOfMeasure`

The Gaussian specialization and aggregation use:

- `LowerBounds.UnitVarianceGaussianBanditEnvironment`
- `LowerBounds.UnitVarianceGaussianBanditEnvironment.gap`
- `LowerBounds.UnitVarianceGaussianBanditEnvironment.toFiniteMean`
- `LowerBounds.chapter16GaussianChangedMean`
- `LowerBounds.chapter16GaussianChangedEnvironment`
- `LowerBounds.chapter16GaussianChangedEnvironment_uniqueBest`
- `LowerBounds.chapter16GaussianChangedEnvironment_sameArmLaw`
- `LowerBounds.chapter16GaussianChangedEnvironment_changedMargin`
- `LowerBounds.chapter16GaussianChangedEnvironment_armKL`
- `LowerBounds.chapter16GaussianChangedEnvironment_armKL_toReal`
- `LowerBounds.InChapter16GaussianLocalClass`
- `LowerBounds.inChapter16GaussianLocalClass_self`
- `LowerBounds.inChapter16GaussianLocalClass_changed`
- `LowerBounds.canonicalGapExpectedPseudoRegretReal_eq_sum_expectedPulls`
- `LowerBounds.unitVarianceGaussianExpectedPseudoRegret`
- `LowerBounds.gapPseudoRegret_add_pos_of_only_arm_changed`
- `LowerBounds.gaussianExpectedPullCount_ge_finiteTimeInstanceDependent`
- `LowerBounds.chapter16Gaussian_finiteTime_log_identity`
- `LowerBounds.gaussianExpectedRegret_ge_finiteTimeInstanceDependent`

## Natural-language proof

For a finite-armed product environment, each arm mean is definitionally tied
to the integral of that arm's probability law. Hence unchanged arm laws have
unchanged finite means. Suppose arm `i` is suboptimal in `nu`, only its law is
changed, and it is uniquely optimal in `nu'`. The bridge proves that the
original gap `Delta_i(nu)` and the changed optimality margin
`lambda-Delta_i(nu)` are positive, and that the latter is no larger than every
unchanged-arm gap in `nu'`.

The existing one-arm history-KL identity and majority-event regret charges
therefore apply to the same randomized, nonanticipating policy in both
environments. Bretagnolle--Huber yields the exact factor `1/4`. Taking logs
gives

```text
E_nu[T_i(n)] >=
  (log(min{lambda-Delta_i(nu),Delta_i(nu)}/4)
    + log(n) - log(R_n(nu)+R_n(nu')))
  / D(P_i,P_i').
```

This is Lemma 16.3 with original-law expected pulls and KL direction
`P_i -> P_i'`. If the KL is zero, equality of laws would contradict the
strictly different certified means. Finite positive KL uses the logarithmic
consumer; infinite KL is handled explicitly by the extended-real convention
whose real quotient is zero.

For Theorem 16.4, increase a positive-gap unit-Gaussian arm by
`(1+epsilon) Delta_i`. The changed arm is uniquely optimal, the other laws are
unchanged, the changed mean vector lies in the source's coordinatewise local
class, and the directed arm KL is
`((1+epsilon) Delta_i)^2/2`. Applying Lemma 16.3 under the two `C n^p` regret
bounds, normalizing the logarithm to

```text
(1-p) log(n) + log(epsilon Delta_i/(8C)),
```

then multiplying by the gap, taking the positive part, and summing all
positive-gap arms proves exactly

```text
R_n(nu) >= 2/(1+epsilon)^2
  * sum_{i: Delta_i>0}
      (((1-p)log(n)+log(epsilon Delta_i/(8C)))/Delta_i)^+.
```

The statement retains the nonempty horizon set, `C>0`, `p in (0,1)`,
`epsilon in (0,1]`, every horizon in the set, and every environment in the
local Gaussian class.

## Theorem 16.2: asymptotic product-class bound

The compiled terminal is
`LowerBounds.consistentPolicy_liminf_expectedRegret_div_log_ge`, supported by
`LowerBounds.consistentPolicy_liminf_expectedPull_div_log_ge_inv_dInf`.
The exact horizon sequences `finiteMeanExpectedRegret` and
`finiteMeanExpectedPullCount` are zero at horizon zero and use the canonical
inclusive history at horizon n+1. For each admissible alternative, replace
only the selected arm, preserving product-class membership. Consistency of
both environments and Lemma 16.3 imply every strict reciprocal-KL lower
bound eventually, hence the extended-real per-alternative liminf bound.

The identity `(sInf S)^(-1) = sup_{a in S} a^(-1)` aggregates all alternative
costs without assuming a minimizer. Infinite costs contribute zero, an empty
alternative class has inverse cost zero, and zero infimum yields an infinite
lower bound. Multiplying by the nonnegative gaps and applying Fatou on the
finite counting measure proves exactly

```text
liminf_{n -> infinity} R_n / log(n)
  >= sum_{i: Delta_i>0} Delta_i / d_inf(P_i,muStar,M_i).
```

The liminf and quotients remain extended-real. No convergence assumption or
assumed per-arm terminal replaces the source consistency premise.
