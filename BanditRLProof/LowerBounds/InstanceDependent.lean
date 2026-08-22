import BanditRLProof.LowerBounds.Minimax
import BanditRLProof.LowerBounds.BanditHistoryKL
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Instance-dependent lower-bound dependencies

This file starts the source-faithful Chapter 16 spine for Lattimore--Szepesvári,
*Bandit Algorithms* (2020).  The compiled surface freezes the exact
subpolynomial consistency quantifier, the distribution-class `d_inf`
definition, the exact unit-Gaussian row of Table 16.1, and the one-arm
change-of-measure/event-information layer built on the compiled Chapter 15
history-KL identity.  It also isolates the elementary asymptotic and scalar
logarithmic steps used by the source proof.

It deliberately does **not** claim Theorem 16.2, Lemma 16.3, or Theorem 16.4.
The remaining finite-time bridge must still derive the two majority-event
error bounds from the source's expected pseudo-regrets in the original and
changed stochastic environments.  The asymptotic theorem additionally needs
the zero/finite/infinite information branches and final `liminf` extraction.
-/

namespace BanditRLProof
namespace LowerBounds

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

/-- The exact scalar asymptotic quantifier in Definition 16.1: a nonnegative
regret sequence is smaller than every positive polynomial order.  Regret
nonnegativity is kept outside this analytic predicate so callers must expose
the model-specific fact explicitly. -/
def IsConsistentRegret (regret : Nat -> Real) : Prop :=
  forall p : Real, 0 < p ->
    Tendsto (fun n : Nat => regret n / (n : Real) ^ p) atTop (nhds 0)

/-- Definition 16.1 over an abstract policy/environment regret interface.
This preserves the source quantifier order: one policy, every environment in
the class, and every positive real exponent. -/
def IsConsistentPolicyOver
    {Policy Environment : Type*}
    (environmentClass : Set Environment)
    (regret : Policy -> Environment -> Nat -> Real)
    (policy : Policy) : Prop :=
  forall environment, environment ∈ environmentClass ->
    IsConsistentRegret (regret policy environment)

/-- The sum of two source-consistent regret sequences is still consistent.
This is the closure step used for `R_n(nu) + R_n(nu')` in the proof of
Theorem 16.2. -/
theorem IsConsistentRegret.add
    {first second : Nat -> Real}
    (hfirst : IsConsistentRegret first)
    (hsecond : IsConsistentRegret second) :
    IsConsistentRegret (fun n => first n + second n) := by
  intro p hp
  simpa only [add_div, zero_add] using (hfirst p hp).add (hsecond p hp)

/-- Two consistent regret sequences are eventually at most `n^p` for every
positive exponent `p`.  This is a stronger eventual form of the source's
auxiliary `C_p n^p` bound and avoids introducing an opaque constant. -/
theorem IsConsistentRegret.eventually_add_le_rpow
    {first second : Nat -> Real}
    (hfirst : IsConsistentRegret first)
    (hsecond : IsConsistentRegret second)
    {p : Real} (hp : 0 < p) :
    ∀ᶠ n : Nat in atTop,
      first n + second n <= (n : Real) ^ p := by
  have hlimit := hfirst.add hsecond p hp
  have hratio : ∀ᶠ n : Nat in atTop,
      (first n + second n) / (n : Real) ^ p < 1 :=
    hlimit.eventually_lt_const zero_lt_one
  filter_upwards [hratio, eventually_gt_atTop (0 : Nat)] with n hn hnpos
  have hcast : (0 : Real) < n := by exact_mod_cast hnpos
  have hpow : (0 : Real) < (n : Real) ^ p := Real.rpow_pos_of_pos hcast p
  have := (div_le_iff₀ hpow).mp hn.le
  simpa using this

/-- Eventually, the logarithmic growth ratio of a positive sum of two
consistent regrets is at most every positive exponent.  This is the
direction-correct analytic leaf used before the source takes a limsup. -/
theorem IsConsistentRegret.eventually_log_add_div_log_le
    {first second : Nat -> Real}
    (hfirst : IsConsistentRegret first)
    (hsecond : IsConsistentRegret second)
    (hpositive : ∀ᶠ n : Nat in atTop, 0 < first n + second n)
    {p : Real} (hp : 0 < p) :
    ∀ᶠ n : Nat in atTop,
      Real.log (first n + second n) / Real.log n <= p := by
  filter_upwards [hfirst.eventually_add_le_rpow hsecond hp, hpositive,
      eventually_gt_atTop (1 : Nat)] with n hupper hsum hn
  have hnreal : (1 : Real) < n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : Real) := Real.log_pos hnreal
  have hlogle : Real.log (first n + second n) <=
      Real.log ((n : Real) ^ p) :=
    Real.log_le_log hsum hupper
  rw [Real.log_rpow (zero_lt_one.trans hnreal) p] at hlogle
  exact (div_le_iff₀ hlogpos).2 hlogle

/-- The source quantity
`d_inf(P, muStar, M) = inf {D(P,P') : P' in M, mean(P') > muStar}`.
The value is extended-real, so an empty alternative set has infimum `∞` and
support failures remain visible. -/
def divergenceInfimum
    {Reward : Type*} [MeasurableSpace Reward]
    (P : Measure Reward) (muStar : Real)
    (distributionClass : Set (Measure Reward))
    (mean : Measure Reward -> Real) : ENNReal :=
  sInf {cost : ENNReal |
    exists P' : Measure Reward,
      P' ∈ distributionClass /\ muStar < mean P' /\
        cost = relativeEntropy P P'}

/-- Any admissible confusing alternative upper-bounds `d_inf`, with KL in the
source direction from the original law to the alternative law. -/
theorem divergenceInfimum_le
    {Reward : Type*} [MeasurableSpace Reward]
    {P P' : Measure Reward} {muStar : Real}
    {distributionClass : Set (Measure Reward)}
    {mean : Measure Reward -> Real}
    (hclass : P' ∈ distributionClass)
    (hbetter : muStar < mean P') :
    divergenceInfimum P muStar distributionClass mean <=
      relativeEntropy P P' := by
  apply sInf_le
  exact ⟨P', hclass, hbetter, rfl⟩

/-- Parameterized form of `d_inf`, useful when a distribution class is
presented by a family of laws rather than an injective set-level mean map. -/
def parametricDivergenceInfimum
    {Reward Parameter : Type*} [MeasurableSpace Reward]
    (law : Parameter -> Measure Reward) (mean : Parameter -> Real)
    (parameter : Parameter) (muStar : Real) : ENNReal :=
  sInf {cost : ENNReal |
    exists alternative : Parameter,
      muStar < mean alternative /\
        cost = relativeEntropy (law parameter) (law alternative)}

/-- Candidate inequality for the parameterized `d_inf` surface. -/
theorem parametricDivergenceInfimum_le
    {Reward Parameter : Type*} [MeasurableSpace Reward]
    {law : Parameter -> Measure Reward} {mean : Parameter -> Real}
    {parameter alternative : Parameter} {muStar : Real}
    (hbetter : muStar < mean alternative) :
    parametricDivergenceInfimum law mean parameter muStar <=
      relativeEntropy (law parameter) (law alternative) := by
  apply sInf_le
  exact ⟨alternative, hbetter, rfl⟩

/-- Unit-variance Gaussian specialization of the source `d_inf`. -/
abbrev unitGaussianDivergenceInfimum (mu muStar : Real) : ENNReal :=
  parametricDivergenceInfimum unitGaussianArm id mu muStar

/-- A Gaussian alternative with mean `muStar + epsilon` is admissible and has
the exact arm-level information cost shown here.  Taking `epsilon -> 0` is a
separate infimum/limit leaf and is not hidden in this theorem. -/
theorem unitGaussianDivergenceInfimum_le_perturbed
    (mu muStar epsilon : Real) (hepsilon : 0 < epsilon) :
    unitGaussianDivergenceInfimum mu muStar <=
      ENNReal.ofReal (((muStar - mu) + epsilon) ^ 2 / 2) := by
  calc
    unitGaussianDivergenceInfimum mu muStar <=
        relativeEntropy (unitGaussianArm mu)
          (unitGaussianArm (muStar + epsilon)) := by
      apply parametricDivergenceInfimum_le
      simpa using lt_add_of_pos_right muStar hepsilon
    _ = ENNReal.ofReal ((mu - (muStar + epsilon)) ^ 2 / 2) :=
      klDiv_gaussianReal_one mu (muStar + epsilon)
    _ = ENNReal.ofReal (((muStar - mu) + epsilon) ^ 2 / 2) := by
      congr 1
      ring

/-- Every strictly better unit-Gaussian alternative costs at least the
boundary value from Table 16.1. -/
theorem unitGaussianDivergenceInfimum_ge
    (mu muStar : Real) (hmu : mu < muStar) :
    ENNReal.ofReal ((muStar - mu) ^ 2 / 2) <=
      unitGaussianDivergenceInfimum mu muStar := by
  apply le_sInf
  intro cost hcost
  rcases hcost with ⟨alternative, hbetter, rfl⟩
  change muStar < alternative at hbetter
  change ENNReal.ofReal ((muStar - mu) ^ 2 / 2) <=
    InformationTheory.klDiv (unitGaussianArm mu)
      (unitGaussianArm alternative)
  rw [klDiv_gaussianReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hbase : 0 <= muStar - mu := sub_nonneg.mpr hmu.le
  have halternative : 0 <= alternative - mu :=
    sub_nonneg.mpr (hmu.trans hbetter).le
  have hdistance : muStar - mu <= alternative - mu := by linarith
  have hsquare : (muStar - mu) ^ 2 <= (alternative - mu) ^ 2 :=
    (sq_le_sq₀ hbase halternative).2 hdistance
  nlinarith [hsquare]

/-- Exact unit-variance Gaussian row of Table 16.1.  The strict alternative
mean means the boundary law is not itself admissible; the reverse inequality
is obtained from positive perturbations tending to zero. -/
theorem unitGaussianDivergenceInfimum_eq
    (mu muStar : Real) (hmu : mu < muStar) :
    unitGaussianDivergenceInfimum mu muStar =
      ENNReal.ofReal ((muStar - mu) ^ 2 / 2) := by
  apply le_antisymm
  · have hinv : Tendsto (fun n : Nat => 1 / ((n + 1 : Nat) : Real))
        atTop (nhds 0) := by
      convert
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := Real) 1).comp
          (tendsto_add_atTop_nat 1) using 1
    have hreal : Tendsto
        (fun n : Nat =>
          (((muStar - mu) + 1 / ((n + 1 : Nat) : Real)) ^ 2 / 2))
        atTop (nhds ((muStar - mu) ^ 2 / 2)) := by
      simpa using ((tendsto_const_nhds.add hinv).pow 2).div_const (2 : Real)
    have hennreal : Tendsto
        (fun n : Nat => ENNReal.ofReal
          (((muStar - mu) + 1 / ((n + 1 : Nat) : Real)) ^ 2 / 2))
        atTop (nhds (ENNReal.ofReal ((muStar - mu) ^ 2 / 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hreal
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hennreal fun n =>
      unitGaussianDivergenceInfimum_le_perturbed
        mu muStar (1 / ((n + 1 : Nat) : Real)) (by positivity)
  · exact unitGaussianDivergenceInfimum_ge mu muStar hmu

/-- Chapter 16's one-arm change-of-measure specialization of Lemma 15.1.
When two stationary bandit environments differ only at `changedArm`, the
directed relative entropy of their finite histories is exactly the
first-environment expected number of pulls of that arm times its arm-law
relative entropy.  The algorithm is one common, possibly randomized,
nonanticipating history policy in both environments. -/
theorem banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (changedArm : Fin K) (lastRound : Nat)
    (hsame : forall arm, arm ≠ changedArm ->
      armLaw arm = referenceArmLaw arm) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound) =
      canonicalRealizedExpectedPullCountThrough
          algorithm armLaw lastRound changedArm *
        InformationTheory.klDiv
          (armLaw changedArm) (referenceArmLaw changedArm) := by
  classical
  rw [banditHistoryRelativeEntropy_eq_expectedPulls_sum]
  apply Finset.sum_eq_single changedArm
  · intro arm _harm hne
    rw [hsame arm hne, InformationTheory.klDiv_self, mul_zero]
  · simp

/-- The source majority event `A = {T_i(n) > n/2}` in the repository's
inclusive convention, where `lastRound` contains `lastRound + 1` pulls. -/
def oneArmMajorityPullEvent
    {K : Nat} {Reward : Type*}
    (changedArm : Fin K) (lastRound : Nat) :
    Set (History.FinitePairHistory (Fin K) Reward lastRound) :=
  {history |
    (lastRound + 1 : ENNReal) <
      2 * finiteHistoryPullCountENNReal lastRound history changedArm}

theorem measurableSet_oneArmMajorityPullEvent
    {K : Nat} {Reward : Type*} [MeasurableSpace Reward]
    (changedArm : Fin K) (lastRound : Nat) :
    MeasurableSet
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound) := by
  exact measurableSet_lt measurable_const
    (measurable_const.mul
      (measurable_finiteHistoryPullCountENNReal lastRound changedArm))

/-- Chapter 16's measurable-event information constraint before regret
calibration.  It instantiates Bretagnolle--Huber on the exact majority event
and rewrites the full history KL using the compiled one-arm specialization of
Lemma 15.1. -/
theorem bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (changedArm : Fin K) (lastRound : Nat)
    (hsame : forall arm, arm ≠ changedArm ->
      armLaw arm = referenceArmLaw arm) :
    bretagnolleHuberScale
        (canonicalRealizedExpectedPullCountThrough
            algorithm armLaw lastRound changedArm *
          InformationTheory.klDiv
            (armLaw changedArm) (referenceArmLaw changedArm)) <=
      (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound) +
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound)ᶜ := by
  have htesting := bretagnolleHuber
    (P := canonicalBanditHistoryMeasure algorithm armLaw lastRound)
    (Q := canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound)
    (measurableSet_oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound)
  change bretagnolleHuberScale
      (InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound)) <=
    _ at htesting
  rw [banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed
    algorithm armLaw referenceArmLaw changedArm lastRound hsame] at htesting
  exact htesting

/-- Finite-information evaluation of the testing scale used when Chapter 16
passes from extended-real KL to the real logarithmic inequality. -/
theorem bretagnolleHuberScale_mul_eq_exp
    {expectedPull armInformation : ENNReal}
    (hpull : expectedPull ≠ ∞) (hinformation : armInformation ≠ ∞) :
    bretagnolleHuberScale (expectedPull * armInformation) =
      (1 / 2 : Real) * Real.exp
        (-(expectedPull.toReal * armInformation.toReal)) := by
  have hproduct : expectedPull * armInformation ≠ ∞ :=
    ENNReal.mul_ne_top hpull hinformation
  simp [bretagnolleHuberScale, hproduct, ENNReal.toReal_mul]

/-- Deterministic assembly of the two majority-event regret charges with the
Bretagnolle--Huber testing error. -/
theorem exp_testing_bound_of_majority_regret_bounds
    (expectedPull information gap changedMargin horizon
      originalError changedError originalRegret changedRegret : Real)
    (hgap : 0 < gap) (hmargin : 0 < changedMargin)
    (hhorizon : 0 < horizon)
    (horiginalError : 0 <= originalError)
    (hchangedError : 0 <= changedError)
    (htesting :
      (1 / 2 : Real) * Real.exp (-(expectedPull * information)) <=
        originalError + changedError)
    (horiginalRegret :
      horizon * gap / 2 * originalError <= originalRegret)
    (hchangedRegret :
      horizon * changedMargin / 2 * changedError <= changedRegret) :
    horizon * min gap changedMargin / 4 *
        Real.exp (-(expectedPull * information)) <=
      originalRegret + changedRegret := by
  have hmin : 0 < min gap changedMargin := lt_min hgap hmargin
  have hscale : 0 <= horizon * min gap changedMargin / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left htesting hscale
  have hminGap : min gap changedMargin <= gap := min_le_left _ _
  have hminMargin : min gap changedMargin <= changedMargin := min_le_right _ _
  have horiginalScaled :
      horizon * min gap changedMargin / 2 * originalError <=
        originalRegret := by
    refine le_trans ?_ horiginalRegret
    gcongr
  have hchangedScaled :
      horizon * min gap changedMargin / 2 * changedError <=
        changedRegret := by
    refine le_trans ?_ hchangedRegret
    gcongr
  nlinarith

/-- The exact logarithmic rearrangement used in Lemma 16.3.  This theorem is
only the scalar consumer of the testing inequality; the bandit theorem must
still produce `htesting` from the common-policy history law, the majority
event, and the two expected pseudo-regrets. -/
theorem expectedPullCount_ge_log_regret_of_exp_testing_bound
    (expectedPull information gap changedMargin horizon regretSum : Real)
    (hinformation : 0 < information)
    (hgap : 0 < gap) (hmargin : 0 < changedMargin)
    (hhorizon : 0 < horizon)
    (htesting :
      horizon * min gap changedMargin / 4 *
          Real.exp (-(expectedPull * information)) <= regretSum) :
    (Real.log (min gap changedMargin / 4) + Real.log horizon -
        Real.log regretSum) / information <= expectedPull := by
  have hmin : 0 < min gap changedMargin := lt_min hgap hmargin
  have hfactor : 0 < horizon * min gap changedMargin / 4 := by positivity
  have hleft : 0 <
      horizon * min gap changedMargin / 4 *
        Real.exp (-(expectedPull * information)) := mul_pos hfactor (Real.exp_pos _)
  have hlog := Real.log_le_log hleft htesting
  have hfactorEq :
      horizon * min gap changedMargin / 4 =
        horizon * (min gap changedMargin / 4) := by ring
  rw [hfactorEq,
    Real.log_mul
      (mul_ne_zero hhorizon.ne'
        (div_ne_zero hmin.ne' (by norm_num : (4 : Real) ≠ 0)))
      (Real.exp_ne_zero _),
    Real.log_mul hhorizon.ne'
      (div_ne_zero hmin.ne' (by norm_num : (4 : Real) ≠ 0)),
    Real.log_exp] at hlog
  apply (div_le_iff₀ hinformation).2
  nlinarith

end

end LowerBounds
end BanditRLProof
