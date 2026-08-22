import BanditRLProof.LowerBounds.Minimax
import BanditRLProof.LowerBounds.BanditHistoryKL
import BanditRLProof.LowerBounds.GaussianMinimax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Instance-dependent lower-bound dependencies

This file starts the source-faithful Chapter 16 spine for Lattimore--Szepesvári,
*Bandit Algorithms* (2020).  The compiled surface freezes the exact
subpolynomial consistency quantifier, the distribution-class `d_inf`
definition, the exact unit-Gaussian row of Table 16.1, the one-arm
change-of-measure/event-information layer built on the compiled Chapter 15
history-KL identity, and the canonical gap-times-pull-count event-to-regret
producers.  It also isolates the elementary asymptotic and scalar logarithmic
steps used by the source proof.

It deliberately does **not** claim Theorem 16.2, Lemma 16.3, or Theorem 16.4.
The gap-vector finite-time consumer still needs a source-environment producer
identifying its gaps with finite arm-law means.  The asymptotic theorem
additionally needs the zero/finite/infinite information branches and final
`liminf` extraction.
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

/-- Gap-times-pull-count pseudo-regret on one realized finite history.  The
gap vector is kept explicit so the later Chapter 16 environment layer must
identify it with `muStar - mu_i`; no scalar regret hypothesis is hidden here. -/
noncomputable def finiteHistoryGapPseudoRegret
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound) : ENNReal :=
  ∑ arm : Fin K,
    ENNReal.ofReal (gap arm) *
      finiteHistoryPullCountENNReal lastRound history arm

/-- Expected gap pseudo-regret under the canonical law generated by one
possibly randomized history policy and one stationary arm kernel. -/
noncomputable def canonicalGapExpectedPseudoRegret
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (lastRound : Nat) : ENNReal :=
  ∫⁻ history,
    finiteHistoryGapPseudoRegret gap lastRound history
    ∂canonicalBanditHistoryMeasure algorithm armLaw lastRound

theorem measurable_finiteHistoryGapPseudoRegret
    {K : Nat} {Reward : Type*} [MeasurableSpace Reward]
    (gap : Fin K -> Real) (lastRound : Nat) :
    Measurable (finiteHistoryGapPseudoRegret
      (Reward := Reward) gap lastRound) := by
  classical
  unfold finiteHistoryGapPseudoRegret
  exact Finset.measurable_sum Finset.univ fun arm _harm =>
    measurable_const.mul
      (measurable_finiteHistoryPullCountENNReal lastRound arm)

theorem finiteHistoryGapPseudoRegret_ne_top
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound) :
    finiteHistoryGapPseudoRegret gap lastRound history ≠ ∞ := by
  classical
  unfold finiteHistoryGapPseudoRegret
  exact ENNReal.sum_ne_top.mpr fun arm _harm =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteHistoryPullCountENNReal_ne_top lastRound history arm)

theorem finiteHistoryGapPseudoRegret_toReal
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound)
    (hgap : forall arm, 0 <= gap arm) :
    (finiteHistoryGapPseudoRegret gap lastRound history).toReal =
      ∑ arm : Fin K,
        gap arm * finiteHistoryPullCountReal lastRound history arm := by
  classical
  unfold finiteHistoryGapPseudoRegret
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro arm _harm
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hgap arm)]
    rfl
  · intro arm _harm
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteHistoryPullCountENNReal_ne_top lastRound history arm)

/-- The expected realized pull counts of all arms sum to the inclusive horizon
for every Markov arm kernel, not only for the Gaussian Chapter 15 instance. -/
theorem sum_canonicalRealizedExpectedPullCountThrough_general
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (lastRound : Nat) :
    ∑ arm : Fin K,
        canonicalRealizedExpectedPullCountThrough
          algorithm armLaw lastRound arm = lastRound + 1 := by
  classical
  unfold canonicalRealizedExpectedPullCountThrough
  rw [← MeasureTheory.lintegral_finset_sum]
  · simp_rw [sum_finiteHistoryPullCountENNReal]
    simp
  · intro arm _harm
    exact measurable_finiteHistoryPullCountENNReal lastRound arm

theorem canonicalRealizedExpectedPullCountThrough_ne_top
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (lastRound : Nat) (arm : Fin K) :
    canonicalRealizedExpectedPullCountThrough
      algorithm armLaw lastRound arm ≠ ∞ := by
  have hle : canonicalRealizedExpectedPullCountThrough
      algorithm armLaw lastRound arm <=
      ∑ other : Fin K,
        canonicalRealizedExpectedPullCountThrough
          algorithm armLaw lastRound other :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ arm)
  rw [sum_canonicalRealizedExpectedPullCountThrough_general] at hle
  exact ne_top_of_le_ne_top (by simp) hle

theorem canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (lastRound : Nat) :
    canonicalGapExpectedPseudoRegret algorithm armLaw gap lastRound =
      ∑ arm : Fin K,
        ENNReal.ofReal (gap arm) *
          canonicalRealizedExpectedPullCountThrough
            algorithm armLaw lastRound arm := by
  classical
  unfold canonicalGapExpectedPseudoRegret finiteHistoryGapPseudoRegret
  rw [MeasureTheory.lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro arm _harm
    rw [MeasureTheory.lintegral_const_mul _
      (measurable_finiteHistoryPullCountENNReal lastRound arm)]
    rfl
  · intro arm _harm
    exact measurable_const.mul
      (measurable_finiteHistoryPullCountENNReal lastRound arm)

theorem canonicalGapExpectedPseudoRegret_ne_top
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (lastRound : Nat) :
    canonicalGapExpectedPseudoRegret algorithm armLaw gap lastRound ≠ ∞ := by
  rw [canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls]
  exact ENNReal.sum_ne_top.mpr fun arm _harm =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (canonicalRealizedExpectedPullCountThrough_ne_top
        algorithm armLaw lastRound arm)

/-- Real-valued presentation of the finite expected pseudo-regret.  Finiteness
is proved above rather than assumed by the Chapter 16 consumer. -/
noncomputable def canonicalGapExpectedPseudoRegretReal
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (lastRound : Nat) : Real :=
  (canonicalGapExpectedPseudoRegret algorithm armLaw gap lastRound).toReal

/-- On the source majority event, the original environment pays at least half
the horizon times the changed arm's positive gap. -/
theorem oneArmMajority_forces_gapPseudoRegret
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (hchanged : 0 < gap changedArm)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound)
    (hA : history ∈ oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound) :
    ENNReal.ofReal
        (((lastRound + 1 : Nat) : Real) * gap changedArm / 2) <=
      finiteHistoryGapPseudoRegret gap lastRound history := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (finiteHistoryGapPseudoRegret_ne_top gap lastRound history)).mpr
  rw [finiteHistoryGapPseudoRegret_toReal gap lastRound history hgap]
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin K)))
    (f := fun arm => gap arm *
      finiteHistoryPullCountReal lastRound history arm)
    (fun arm _harm => mul_nonneg (hgap arm)
      (finiteHistoryPullCountReal_nonneg lastRound history arm))
    (Finset.mem_univ changedArm)
  have hAreal : ((lastRound + 1 : Nat) : Real) <
      2 * finiteHistoryPullCountReal lastRound history changedArm := by
    have hconverted := (ENNReal.toReal_lt_toReal
      (by simp : (lastRound + 1 : ENNReal) ≠ ∞)
      (ENNReal.mul_ne_top (by simp)
        (finiteHistoryPullCountENNReal_ne_top
          lastRound history changedArm))).2 hA
    simpa [finiteHistoryPullCountReal] using hconverted
  nlinarith

/-- On the complement of the majority event, every non-changed arm charged by
at least `changedMargin` forces half-horizon pseudo-regret. -/
theorem oneArmMajority_compl_forces_gapPseudoRegret
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (changedMargin : Real)
    (hmargin : 0 < changedMargin)
    (hother : forall arm, arm ≠ changedArm -> changedMargin <= gap arm)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound)
    (hAc : history ∈ (oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound)ᶜ) :
    ENNReal.ofReal
        (((lastRound + 1 : Nat) : Real) * changedMargin / 2) <=
      finiteHistoryGapPseudoRegret gap lastRound history := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (finiteHistoryGapPseudoRegret_ne_top gap lastRound history)).mpr
  rw [finiteHistoryGapPseudoRegret_toReal gap lastRound history hgap]
  have hnot : ¬ (lastRound + 1 : ENNReal) <
      2 * finiteHistoryPullCountENNReal lastRound history changedArm := by
    simpa [oneArmMajorityPullEvent] using hAc
  have hcountENN : 2 * finiteHistoryPullCountENNReal
      lastRound history changedArm <= lastRound + 1 := le_of_not_gt hnot
  have hcount : 2 * finiteHistoryPullCountReal
      lastRound history changedArm <= ((lastRound + 1 : Nat) : Real) := by
    have hconverted := ENNReal.toReal_mono
      (by simp : (lastRound + 1 : ENNReal) ≠ ∞) hcountENN
    simpa [finiteHistoryPullCountReal] using hconverted
  have htotal := sum_finiteHistoryPullCountReal lastRound history
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin K))
    (fun arm => finiteHistoryPullCountReal lastRound history arm)
    (Finset.mem_univ changedArm)
  have hotherCount :
      (∑ arm ∈ (Finset.univ : Finset (Fin K)).erase changedArm,
        finiteHistoryPullCountReal lastRound history arm) =
        ((lastRound + 1 : Nat) : Real) -
          finiteHistoryPullCountReal lastRound history changedArm := by
    norm_num [Nat.cast_add, Nat.cast_one] at htotal ⊢
  have hcharged :
      changedMargin *
          (∑ arm ∈ (Finset.univ : Finset (Fin K)).erase changedArm,
            finiteHistoryPullCountReal lastRound history arm) <=
        ∑ arm ∈ (Finset.univ : Finset (Fin K)).erase changedArm,
          gap arm * finiteHistoryPullCountReal lastRound history arm := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro arm harm
    exact mul_le_mul_of_nonneg_right
      (hother arm (by simpa using harm))
      (finiteHistoryPullCountReal_nonneg lastRound history arm)
  have hfull :
      (∑ arm ∈ (Finset.univ : Finset (Fin K)).erase changedArm,
          gap arm * finiteHistoryPullCountReal lastRound history arm) <=
        ∑ arm : Fin K,
          gap arm * finiteHistoryPullCountReal lastRound history arm := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin K))
      (fun arm => gap arm * finiteHistoryPullCountReal lastRound history arm)
      (Finset.mem_univ changedArm)
    rw [← hsum]
    exact le_add_of_nonneg_right
      (mul_nonneg (hgap changedArm)
        (finiteHistoryPullCountReal_nonneg lastRound history changedArm))
  rw [hotherCount] at hcharged
  refine le_trans ?_ (hcharged.trans hfull)
  nlinarith

/-- Original-environment event probability charged to the actual canonical
gap pseudo-regret. -/
theorem oneArmMajority_probability_charge_le_expectedPseudoRegret
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (hchanged : 0 < gap changedArm)
    (lastRound : Nat) :
    ((lastRound + 1 : Nat) : Real) * gap changedArm / 2 *
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound) <=
      canonicalGapExpectedPseudoRegretReal
        algorithm armLaw gap lastRound := by
  have hENN := ofReal_mul_probReal_le_lintegral_of_event
    (mu := canonicalBanditHistoryMeasure algorithm armLaw lastRound)
    (measurableSet_oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound)
    (show 0 <= ((lastRound + 1 : Nat) : Real) * gap changedArm / 2 by
      positivity)
    (oneArmMajority_forces_gapPseudoRegret
      gap hgap changedArm hchanged lastRound)
  have hreal := ENNReal.toReal_mono
    (canonicalGapExpectedPseudoRegret_ne_top
      algorithm armLaw gap lastRound) hENN
  have hleft : 0 <=
      ((lastRound + 1 : Nat) : Real) * gap changedArm / 2 *
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound) := by positivity
  rw [ENNReal.toReal_ofReal hleft] at hreal
  simpa only [canonicalGapExpectedPseudoRegretReal] using hreal

/-- Changed-environment complement probability charged to the actual
canonical gap pseudo-regret. -/
theorem oneArmMajority_compl_probability_charge_le_expectedPseudoRegret
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (changedMargin : Real)
    (hmargin : 0 < changedMargin)
    (hother : forall arm, arm ≠ changedArm -> changedMargin <= gap arm)
    (lastRound : Nat) :
    ((lastRound + 1 : Nat) : Real) * changedMargin / 2 *
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound)ᶜ <=
      canonicalGapExpectedPseudoRegretReal
        algorithm armLaw gap lastRound := by
  have hENN := ofReal_mul_probReal_le_lintegral_of_event
    (mu := canonicalBanditHistoryMeasure algorithm armLaw lastRound)
    (measurableSet_oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound).compl
    (show 0 <= ((lastRound + 1 : Nat) : Real) * changedMargin / 2 by
      positivity)
    (oneArmMajority_compl_forces_gapPseudoRegret
      gap hgap changedArm changedMargin hmargin hother lastRound)
  have hreal := ENNReal.toReal_mono
    (canonicalGapExpectedPseudoRegret_ne_top
      algorithm armLaw gap lastRound) hENN
  have hleft : 0 <=
      ((lastRound + 1 : Nat) : Real) * changedMargin / 2 *
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound)ᶜ := by positivity
  rw [ENNReal.toReal_ofReal hleft] at hreal
  simpa only [canonicalGapExpectedPseudoRegretReal] using hreal

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

/-- Chapter 16's finite-time change-of-measure calculation with the actual
canonical gap pseudo-regrets produced above.  This closes the common-policy,
one-arm-KL, majority-event, exact `1/4`, and logarithmic assembly route for
explicit nonnegative gap vectors.  It is intentionally not named as source
Lemma 16.3: a later environment layer must still prove that these vectors are
the mean gaps of finite-mean arm laws and discharge the finite-positive-KL
branch from that source contract. -/
theorem expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (originalGap referenceGap : Fin K -> Real)
    (horiginalGap : forall arm, 0 <= originalGap arm)
    (hreferenceGap : forall arm, 0 <= referenceGap arm)
    (changedArm : Fin K) (changedMargin : Real)
    (hchangedGap : 0 < originalGap changedArm)
    (hmargin : 0 < changedMargin)
    (hother : forall arm, arm ≠ changedArm ->
      changedMargin <= referenceGap arm)
    (lastRound : Nat)
    (hsame : forall arm, arm ≠ changedArm ->
      armLaw arm = referenceArmLaw arm)
    (hinformation_ne_top :
      InformationTheory.klDiv
        (armLaw changedArm) (referenceArmLaw changedArm) ≠ ∞)
    (hinformation_pos : 0 <
      (InformationTheory.klDiv
        (armLaw changedArm) (referenceArmLaw changedArm)).toReal) :
    (Real.log (min (originalGap changedArm) changedMargin / 4) +
          Real.log ((lastRound + 1 : Nat) : Real) -
          Real.log
            (canonicalGapExpectedPseudoRegretReal
                algorithm armLaw originalGap lastRound +
              canonicalGapExpectedPseudoRegretReal
                algorithm referenceArmLaw referenceGap lastRound)) /
        (InformationTheory.klDiv
          (armLaw changedArm) (referenceArmLaw changedArm)).toReal <=
      (canonicalRealizedExpectedPullCountThrough
        algorithm armLaw lastRound changedArm).toReal := by
  let expectedPull := canonicalRealizedExpectedPullCountThrough
    algorithm armLaw lastRound changedArm
  let information := InformationTheory.klDiv
    (armLaw changedArm) (referenceArmLaw changedArm)
  let horizon : Real := (lastRound + 1 : Nat)
  let originalError :=
    (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound)
  let referenceError :=
    (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound).real
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound)ᶜ
  let originalRegret := canonicalGapExpectedPseudoRegretReal
    algorithm armLaw originalGap lastRound
  let referenceRegret := canonicalGapExpectedPseudoRegretReal
    algorithm referenceArmLaw referenceGap lastRound
  have hpull : expectedPull ≠ ∞ := by
    exact canonicalRealizedExpectedPullCountThrough_ne_top
      algorithm armLaw lastRound changedArm
  have htesting :=
    bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
      algorithm armLaw referenceArmLaw changedArm lastRound hsame
  have htestingReal :
      (1 / 2 : Real) * Real.exp
          (-(expectedPull.toReal * information.toReal)) <=
        originalError + referenceError := by
    change bretagnolleHuberScale (expectedPull * information) <=
      originalError + referenceError at htesting
    have hinformation : information ≠ ∞ := hinformation_ne_top
    rw [bretagnolleHuberScale_mul_eq_exp hpull hinformation] at htesting
    exact htesting
  have horiginal :
      horizon * originalGap changedArm / 2 * originalError <=
        originalRegret := by
    exact oneArmMajority_probability_charge_le_expectedPseudoRegret
      algorithm armLaw originalGap horiginalGap changedArm hchangedGap lastRound
  have hreference :
      horizon * changedMargin / 2 * referenceError <=
        referenceRegret := by
    exact oneArmMajority_compl_probability_charge_le_expectedPseudoRegret
      algorithm referenceArmLaw referenceGap hreferenceGap changedArm
        changedMargin hmargin hother lastRound
  have hassembled := exp_testing_bound_of_majority_regret_bounds
    expectedPull.toReal information.toReal (originalGap changedArm)
      changedMargin horizon originalError referenceError
      originalRegret referenceRegret hchangedGap hmargin
      (by dsimp [horizon]; positivity) measureReal_nonneg measureReal_nonneg
      htestingReal horiginal hreference
  exact expectedPullCount_ge_log_regret_of_exp_testing_bound
    expectedPull.toReal information.toReal (originalGap changedArm)
      changedMargin horizon (originalRegret + referenceRegret)
      hinformation_pos hchangedGap hmargin
      (by dsimp [horizon]; positivity) hassembled

end

end LowerBounds
end BanditRLProof
