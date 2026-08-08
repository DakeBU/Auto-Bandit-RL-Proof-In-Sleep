import BanditRLProof.TsallisFiniteArmIIDRewardLaw
import BanditRLProof.TsallisScheduledIIDTimeVaryingMeanGap
import BanditRLProof.TsallisScheduledIndependentMeanGap

/-!
# Finite-arm independent nonidentical reward laws for scheduled half-Tsallis

Each round may use a different probability law for every arm, while all
roundwise arm laws retain the means of one fixed finite-bandit model. The
roundwise product reward vectors are independent across time but need not be
identically distributed.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

/-- The independent finite-arm reward-vector law used at round `t`. -/
noncomputable def finiteArmIndependentRewardVectorLaw {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) (t : Nat) :
    Measure (Fin K -> Rat) :=
  finiteArmIIDRewardVectorLaw (armLaw t)

/-- Every roundwise loss gap has the fixed finite-bandit model gap when the
possibly time-varying arm laws preserve the model means. -/
theorem independentLossStateTimeVaryingMeanGap_finiteArmIndependentRewardVectorLoss_eq_gap
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall t arm,
      integral (armLaw t arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (t : Nat) (arm : Fin K) :
    independentLossStateTimeVaryingMeanGap
        (finiteArmIndependentRewardVectorLaw armLaw)
        (fun _ => finiteArmIIDRewardVectorLoss)
        t model.bestArm arm =
      ((model.gap arm : Rat) : Real) := by
  simpa only [finiteArmIndependentRewardVectorLaw,
    independentLossStateTimeVaryingMeanGap, iidLossStateMeanGap] using
    (iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap
      model (armLaw t) (hprob t) (hbound t) (hmean t) arm)

/-- Independent roundwise product reward vectors with fixed arm means supply
the fixed model-gap law required by the scheduled self-bounding route. -/
theorem hasScheduledIndependentMeanGapLaw_of_finiteArmIndependentRewardVectorLaw
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall t arm,
      integral (armLaw t arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (horizon : Nat)
    (trajectoryKernel : Kernel (Nat -> Fin K -> Rat)
      ((k : Nat) -> Fin K × Real))
    [IsMarkovKernel trajectoryKernel]
    (hfactor : HasScheduledIIDPrefixKernelFactorization
      trajectoryKernel horizon) :
    let law := finiteArmIndependentRewardVectorLaw armLaw
    let value := fun _ : Nat => finiteArmIIDRewardVectorLoss
    let prior := Measure.infinitePi law
    let mu := prior ⊗ₘ trajectoryKernel
    HasScheduledIndependentMeanGapLaw mu (Finset.univ : Finset (Fin K))
      (iidTimeVaryingLossStatePredictableLossVector value
        (fun _ => measurable_finiteArmIIDRewardVectorLoss)
        (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
        (fun _ => finiteArmIIDRewardVectorLoss_le_one))
      model.bestArm (fun arm => ((model.gap arm : Rat) : Real)) horizon := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (t : Nat) (arm : Fin K) :
      IsProbabilityMeasure (armLaw t arm) := hprob t arm
  letI (t : Nat) :
      IsProbabilityMeasure (finiteArmIndependentRewardVectorLaw armLaw t) := by
    rw [finiteArmIndependentRewardVectorLaw, finiteArmIIDRewardVectorLaw]
    infer_instance
  dsimp only
  have htime :=
    hasScheduledTimeVaryingIndependentMeanGapLaw_of_independentLossState
      (law := finiteArmIndependentRewardVectorLaw armLaw)
      (value := fun _ : Nat => finiteArmIIDRewardVectorLoss)
      (fun _ => measurable_finiteArmIIDRewardVectorLoss)
      (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
      (fun _ => finiteArmIIDRewardVectorLoss_le_one)
      (Finset.univ : Finset (Fin K)) model.bestArm horizon
      trajectoryKernel hfactor
  intro t ht arm harm
  rcases htime t ht arm harm with ⟨hindep, hgap⟩
  refine ⟨hindep, ?_⟩
  rw [hgap]
  exact
    independentLossStateTimeVaryingMeanGap_finiteArmIndependentRewardVectorLoss_eq_gap
      model armLaw hprob hbound hmean t arm

/-- A time-varying collection of bounded rational arm-reward laws with fixed
finite-bandit means supplies a concrete independent, nonidentically
distributed stochastic model for the generated scheduled half-Tsallis
logarithmic regret theorem. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentRewardLawRegret_le_log
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall t arm,
      integral (armLaw t arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (horizon : Nat) (corruption : Real) (hcorruption : 0 <= corruption) :
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
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) + corruption := by
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
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule loss
  let trajectoryKernel := sampledScheduledHalfTsallisTrajectoryKernel
    (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
    sampledScheduledHalfTsallisSqrtSchedule
    selector.finiteHistory loss.environment
  have hfactor : HasScheduledIIDPrefixKernelFactorization trajectoryKernel
      horizon := by
    simpa only [trajectoryKernel, selector, loss, value] using
      hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisTimeVaryingTrajectoryKernel
        (fun _ : Fin K => (0 : Rat))
        (fun _ : Nat => finiteArmIIDRewardVectorLoss)
        (fun _ => measurable_finiteArmIIDRewardVectorLoss)
        (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
        (fun _ => finiteArmIIDRewardVectorLoss_le_one)
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule selector.finiteHistory horizon
  have hgapLaw :
      let prior := Measure.infinitePi
        (finiteArmIndependentRewardVectorLaw armLaw)
      let mu := prior ⊗ₘ trajectoryKernel
      HasScheduledIndependentMeanGapLaw mu
        (Finset.univ : Finset (Fin K)) loss model.bestArm
        (fun arm => ((model.gap arm : Rat) : Real)) horizon := by
    simpa only [loss, value] using
      hasScheduledIndependentMeanGapLaw_of_finiteArmIndependentRewardVectorLaw
        model armLaw hprob hbound hmean horizon trajectoryKernel hfactor
  simpa only [loss, value, selector, trajectoryKernel] using
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_independentMeanGap
      (Measure.infinitePi (finiteArmIndependentRewardVectorLaw armLaw))
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty loss
      (Finset.mem_univ model.bestArm) horizon
      (fun arm => ((model.gap arm : Rat) : Real))
      (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
      hgapLaw corruption hcorruption

end Tsallis
end BanditRLProof
