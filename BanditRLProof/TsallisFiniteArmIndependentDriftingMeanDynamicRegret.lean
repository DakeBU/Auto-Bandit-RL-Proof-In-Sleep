import BanditRLProof.TsallisFiniteArmIndependentDriftingMeanAllRegimes
import BanditRLProof.FiniteBanditModelInvariants
import Mathlib.Data.Finset.Max

/-!
# Dynamic regret for independent reward laws with drifting means

This module upgrades the fixed-baseline all-regimes theorem to the comparator
that maximizes the actual reward mean at every round. The dynamic regret is
decomposed into fixed-`model.bestArm` regret and the actual mean advantage of
the moving comparator. The supplied armwise mean-deviation envelope controls
that second term.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

universe u v

/-- Predictable environment regret against a deterministic comparator that may
change with the round. -/
noncomputable def sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (comparator : Nat -> Action) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (Exp3.predictableLossAt loss t sample) -
      Exp3.predictableLossAt loss t sample (comparator t))

/-- Moving-comparator regret is fixed-comparator regret plus the cumulative
loss advantage of the moving comparator over the fixed arm. -/
theorem sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret_eq_fixed_add
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms)
    (comparator : Nat -> Action) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta loss comparator horizon sample =
      sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta loss (pointMass best) horizon sample +
        (Finset.range (horizon + 1)).sum (fun t =>
          Exp3.predictableLossAt loss t sample best -
            Exp3.predictableLossAt loss t sample (comparator t)) := by
  unfold sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
    sampledScheduledHalfTsallisPredictableEnvironmentRegret
  simp_rw [linearLoss_pointMass arms hbest]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- An actual-mean maximizing arm at round `t`. The finite action space is
nonempty because it comes from a `FiniteBanditModel`. -/
noncomputable def finiteArmIndependentBestArmAt {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (t : Nat) : Fin K := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  exact Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset (Fin K))
      (finiteArmIndependentRewardMean armLaw t) Finset.univ_nonempty)

/-- The selected dynamic arm maximizes the actual roundwise reward mean. -/
theorem finiteArmIndependentRewardMean_le_bestArmAt {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (t : Nat) (arm : Fin K) :
    finiteArmIndependentRewardMean armLaw t arm <=
      finiteArmIndependentRewardMean armLaw t
        (finiteArmIndependentBestArmAt model armLaw t) := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  have hspec :=
    Classical.choose_spec
      (Finset.exists_max_image (Finset.univ : Finset (Fin K))
        (finiteArmIndependentRewardMean armLaw t) Finset.univ_nonempty)
  exact hspec.2 arm (Finset.mem_univ arm)

/-- Extra envelope budget needed to move from the fixed model comparator to
the actual-mean maximizing arm at every included round. -/
noncomputable def finiteArmIndependentDynamicComparatorPenalty {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat)
    (meanDeviation : Nat -> Fin K -> Real) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    if finiteArmIndependentBestArmAt model armLaw t = model.bestArm then
      0
    else
      meanDeviation t (finiteArmIndependentBestArmAt model armLaw t) +
        meanDeviation t model.bestArm)

/-- With one arm the dynamic comparator cannot move, so its extra penalty is
zero. -/
@[simp]
theorem finiteArmIndependentDynamicComparatorPenalty_fin_one
    (model : FiniteBanditModel 1)
    (armLaw : Nat -> Fin 1 -> Measure Rat) (horizon : Nat)
    (meanDeviation : Nat -> Fin 1 -> Real) :
    finiteArmIndependentDynamicComparatorPenalty
        model armLaw horizon meanDeviation = 0 := by
  unfold finiteArmIndependentDynamicComparatorPenalty
  apply Finset.sum_eq_zero
  intro t _ht
  rw [if_pos (Subsingleton.elim _ _)]

/-- The actual-mean advantage of any arm over the fixed baseline best arm is
controlled by the two corresponding mean-deviation envelopes. -/
theorem finiteArmIndependentRewardMean_sub_bestArm_le_meanDeviation
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (meanDeviation : Nat -> Fin K -> Real)
    (hmeanDeviation : forall t arm,
      |finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real)| <= meanDeviation t arm)
    (t : Nat) (arm : Fin K) :
    finiteArmIndependentRewardMean armLaw t arm -
        finiteArmIndependentRewardMean armLaw t model.bestArm <=
      meanDeviation t arm + meanDeviation t model.bestArm := by
  have hmodel :
      ((model.mean arm : Rat) : Real) <=
        ((model.mean model.bestArm : Rat) : Real) := by
    exact_mod_cast FiniteBanditModel.mean_le_bestArm_mean model arm
  have harm :
      finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real) <= meanDeviation t arm :=
    (le_abs_self _).trans (hmeanDeviation t arm)
  have hbest :
      ((model.mean model.bestArm : Rat) : Real) -
          finiteArmIndependentRewardMean armLaw t model.bestArm <=
        meanDeviation t model.bestArm := by
    calc
      ((model.mean model.bestArm : Rat) : Real) -
          finiteArmIndependentRewardMean armLaw t model.bestArm <=
          |((model.mean model.bestArm : Rat) : Real) -
            finiteArmIndependentRewardMean armLaw t model.bestArm| :=
        le_abs_self _
      _ = |finiteArmIndependentRewardMean armLaw t model.bestArm -
          ((model.mean model.bestArm : Rat) : Real)| := abs_sub_comm _ _
      _ <= meanDeviation t model.bestArm :=
        hmeanDeviation t model.bestArm
  linarith

/-- For the concrete independent nonidentical generated law, integrated
moving-comparator regret is fixed-baseline regret plus the exact cumulative
actual-mean advantage of the comparator. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentMovingComparatorRewardLawRegret_eq_fixed_add_meanAdvantage
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (comparator : Nat -> Fin K) (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIndependentRewardVectorLaw armLaw
    let value := fun _ : Nat => finiteArmIIDRewardVectorLoss
    let loss := iidTimeVaryingLossStatePredictableLossVector value
      (fun _ => measurable_finiteArmIIDRewardVectorLoss)
      (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
      (fun _ => finiteArmIIDRewardVectorLoss_le_one)
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi law
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    integral mu
        (sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
          (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
          sampledScheduledHalfTsallisSqrtSchedule loss comparator horizon) =
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
          sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass model.bestArm) horizon) +
        (Finset.range (horizon + 1)).sum (fun t =>
          finiteArmIndependentRewardMean armLaw t (comparator t) -
            finiteArmIndependentRewardMean armLaw t model.bestArm) := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (t : Nat) (arm : Fin K) :
      IsProbabilityMeasure (armLaw t arm) := hprob t arm
  letI (t : Nat) :
      IsProbabilityMeasure (finiteArmIndependentRewardVectorLaw armLaw t) := by
    rw [finiteArmIndependentRewardVectorLaw, finiteArmIIDRewardVectorLaw]
    infer_instance
  dsimp only
  let value : Nat -> (Fin K -> Rat) -> Fin K -> Real :=
    fun _ => finiteArmIIDRewardVectorLoss
  let loss := iidTimeVaryingLossStatePredictableLossVector value
    (fun _ => measurable_finiteArmIIDRewardVectorLoss)
    (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
    (fun _ => finiteArmIIDRewardVectorLoss_le_one)
  let arms : Finset (Fin K) := Finset.univ
  let harms : arms.Nonempty := Finset.univ_nonempty
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    arms harms eta loss
  let trajectoryKernel := sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let prior := Measure.infinitePi
    (finiteArmIndependentRewardVectorLaw armLaw)
  let mu := prior ⊗ₘ trajectoryKernel
  let actualGap := fun t arm =>
    independentLossStateTimeVaryingMeanGap
      (finiteArmIndependentRewardVectorLaw armLaw)
      (fun _ => finiteArmIIDRewardVectorLoss)
      t model.bestArm arm
  haveI : IsProbabilityMeasure prior := inferInstance
  haveI : IsProbabilityMeasure mu := inferInstance
  have hfactor : HasScheduledIIDPrefixKernelFactorization trajectoryKernel
      horizon := by
    simpa only [trajectoryKernel, selector, eta, loss, value] using
      hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisTimeVaryingTrajectoryKernel
        (fun _ : Fin K => (0 : Rat))
        (fun _ : Nat => finiteArmIIDRewardVectorLoss)
        (fun _ => measurable_finiteArmIIDRewardVectorLoss)
        (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
        (fun _ => finiteArmIIDRewardVectorLoss_le_one)
        arms harms eta selector.finiteHistory horizon
  have hindependent : HasScheduledTimeVaryingIndependentMeanGapLaw
      mu arms loss model.bestArm actualGap horizon := by
    simpa only [mu, prior, actualGap, loss, value] using
      hasScheduledTimeVaryingIndependentMeanGapLaw_of_independentLossState
        (finiteArmIndependentRewardVectorLaw armLaw)
        (fun _ : Nat => finiteArmIIDRewardVectorLoss)
        (fun _ => measurable_finiteArmIIDRewardVectorLoss)
        (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
        (fun _ => finiteArmIIDRewardVectorLoss_le_one)
        arms model.bestArm horizon trajectoryKernel hfactor
  let advantage := fun
      (sample : (Nat -> Fin K -> Rat) × ((k : Nat) -> Fin K × Real)) =>
    (Finset.range (horizon + 1)).sum (fun t =>
      Exp3.predictableLossAt loss t sample model.bestArm -
        Exp3.predictableLossAt loss t sample (comparator t))
  have hfixedIntegrable :
      Integrable (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass model.bestArm) horizon) mu := by
    have hroute :=
      integral_sampledScheduledHalfTsallisPredictableEstimatedRegret_eq_environmentRegret
        prior arms harms eta loss (pointMass model.bestArm)
          (finiteSimplex_pointMass arms (Finset.mem_univ model.bestArm))
          horizon
    simpa only [mu, trajectoryKernel, selector] using hroute.2.1
  have hadvantageIntegrable : Integrable advantage mu := by
    unfold advantage
    exact IntegrabilitySums.integrable_finset_sum mu
      (Finset.range (horizon + 1))
      (fun t sample =>
        Exp3.predictableLossAt loss t sample model.bestArm -
          Exp3.predictableLossAt loss t sample (comparator t))
      (fun t _ht =>
        (Exp3.integrable_predictableLossAt mu loss t model.bestArm).sub
          (Exp3.integrable_predictableLossAt mu loss t (comparator t)))
  have hpointwise :
      sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms eta loss comparator horizon =
        fun sample =>
          sampledScheduledHalfTsallisPredictableEnvironmentRegret
              arms harms eta loss (pointMass model.bestArm) horizon sample +
            advantage sample := by
    funext sample
    exact
      sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret_eq_fixed_add
        arms harms eta loss (Finset.mem_univ model.bestArm)
          comparator horizon sample
  rw [hpointwise, integral_add hfixedIntegrable hadvantageIntegrable]
  congr 1
  rw [ExpectationBochnerSums.integral_finset_sum mu
    (Finset.range (horizon + 1))]
  · apply Finset.sum_congr rfl
    intro t ht
    have ht' : t <= horizon :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    by_cases hcomparator : comparator t = model.bestArm
    · simp [hcomparator]
    · have hgap :=
        (hindependent t ht' (comparator t)
          (Finset.mem_erase.mpr
            ⟨hcomparator, Finset.mem_univ (comparator t)⟩)).2
      have hbestIntegrable :=
        Exp3.integrable_predictableLossAt mu loss t model.bestArm
      have hcomparatorIntegrable :=
        Exp3.integrable_predictableLossAt mu loss t (comparator t)
      rw [integral_sub hbestIntegrable hcomparatorIntegrable]
      rw [integral_sub hcomparatorIntegrable hbestIntegrable] at hgap
      dsimp only [actualGap] at hgap
      rw [
        independentLossStateTimeVaryingMeanGap_finiteArmIndependentRewardVectorLoss_eq_mean_sub
          armLaw hprob hbound] at hgap
      linarith
  · intro t _ht
    exact
      (Exp3.integrable_predictableLossAt mu loss t model.bestArm).sub
        (Exp3.integrable_predictableLossAt mu loss t (comparator t))

/-- Dynamic all-regimes bound: fixed-baseline all-regimes regret plus the
explicit envelope cost of following the actual-mean maximizing arm. -/
noncomputable def finiteArmIndependentDriftingMeanDynamicAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat)
    (meanDeviation : Nat -> Fin K -> Real) : Real :=
  finiteArmIndependentDriftingMeanAllRegimeBound
      model horizon meanDeviation +
    finiteArmIndependentDynamicComparatorPenalty
      model armLaw horizon meanDeviation

@[simp]
theorem finiteArmIndependentDriftingMeanDynamicAllRegimeBound_fin_one
    (model : FiniteBanditModel 1)
    (armLaw : Nat -> Fin 1 -> Measure Rat) (horizon : Nat)
    (meanDeviation : Nat -> Fin 1 -> Real) :
    finiteArmIndependentDriftingMeanDynamicAllRegimeBound
        model armLaw horizon meanDeviation =
      1 + Real.log (((horizon + 1 : Nat) : Real)) := by
  simp [finiteArmIndependentDriftingMeanDynamicAllRegimeBound]

/-- Generated scheduled half-Tsallis dynamic regret against the arm with the
largest actual reward mean at each round. No caller supplies the dynamic
comparator, a refined-window proof, or a nonempty-suboptimal-arm proof. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanDynamicRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (meanDeviation : Nat -> Fin K -> Real)
    (hmeanDeviation : forall t arm,
      |finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real)| <= meanDeviation t arm)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIndependentRewardVectorLaw armLaw
    let value := fun _ : Nat => finiteArmIIDRewardVectorLoss
    let loss := iidTimeVaryingLossStatePredictableLossVector value
      (fun _ => measurable_finiteArmIIDRewardVectorLoss)
      (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
      (fun _ => finiteArmIIDRewardVectorLoss_le_one)
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi law
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    integral mu
        (sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
          (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
          sampledScheduledHalfTsallisSqrtSchedule loss
          (finiteArmIndependentBestArmAt model armLaw) horizon) <=
      finiteArmIndependentDriftingMeanDynamicAllRegimeBound
        model armLaw horizon meanDeviation := by
  dsimp only
  have hdecomposition :=
    integral_sampledScheduledHalfTsallisFiniteArmIndependentMovingComparatorRewardLawRegret_eq_fixed_add_meanAdvantage
      model armLaw hprob hbound
        (finiteArmIndependentBestArmAt model armLaw) horizon
  dsimp only at hdecomposition
  rw [hdecomposition]
  have hfixed :=
    integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLawRegret_le_allRegimes
      model armLaw hprob hbound meanDeviation hmeanDeviation
        hgapPos hgapLeOne horizon
  dsimp only at hfixed
  have hdynamic :
      (Finset.range (horizon + 1)).sum (fun t =>
          finiteArmIndependentRewardMean armLaw t
              (finiteArmIndependentBestArmAt model armLaw t) -
            finiteArmIndependentRewardMean armLaw t model.bestArm) <=
        finiteArmIndependentDynamicComparatorPenalty
          model armLaw horizon meanDeviation := by
    unfold finiteArmIndependentDynamicComparatorPenalty
    apply Finset.sum_le_sum
    intro t _ht
    by_cases hsame :
        finiteArmIndependentBestArmAt model armLaw t = model.bestArm
    · simp [hsame]
    · simp only [hsame, if_false]
      exact
        finiteArmIndependentRewardMean_sub_bestArm_le_meanDeviation
          model armLaw meanDeviation hmeanDeviation t
            (finiteArmIndependentBestArmAt model armLaw t)
  unfold finiteArmIndependentDriftingMeanDynamicAllRegimeBound
  exact add_le_add hfixed hdynamic

end Tsallis
end BanditRLProof
