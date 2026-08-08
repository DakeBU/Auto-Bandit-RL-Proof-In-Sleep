import BanditRLProof.Algorithms.UCBFiniteArmSubGaussianSampledAsymptotics

/-!
# Sampled-pair UCB consistency for armwise bounded finite-arm laws

This module derives the direct centered sub-Gaussian contracts required by the
stationary finite-arm sampled-pair consistency theorem from arm-dependent
almost-sure reward intervals and exact arm means.
-/

open scoped BigOperators ENNReal NNReal

open Filter MeasureTheory ProbabilityTheory
open Asymptotics

namespace BanditRLProof
namespace UCB

/--
Exact sampled-successor expected pseudo-regret for stationary finite-arm laws
bounded almost surely in arm-dependent intervals. The parent practical route
pads the finite maximum of the genuine armwise Hoeffding proxies.
-/
noncomputable def selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (defaultAction : Fin K)
    (T : Nat) : Real :=
  selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret
    model armLaw hprob
      (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
      defaultAction T

/--
The exact armwise-bounded sampled-successor expected pseudo-regret is
nonnegative and satisfies the fixed-model logarithmic envelope at every large
horizon.
-/
theorem selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret_nonneg_and_le
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc (lo arm) (hi arm)
          ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K)
    (T : Nat) (hlarge : 2 * K <= T + 1) :
    0 <= selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret
        model armLaw hprob lo hi defaultAction T /\
      selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret
          model armLaw hprob lo hi defaultAction T <=
        selectedPolicySuccessorAsymptoticModelCoefficient model
            (Concentration.finiteArmPositiveVarianceProxy fun arm =>
              Concentration.intervalVarianceProxy (lo arm) (hi arm)) *
          (1 + Real.log (((T + 1 : Nat) : Real))) := by
  let law :=
    RewardKernel.contextIndependentArmwiseBoundedCenteredRewardKernelLaw
      (Context := Unit) armLaw hprob model.mean lo hi hmeas hbound hmean
  have hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => (((reward - model.mean arm : Rat) : Real)))
        (Concentration.intervalVarianceProxy (lo arm) (hi arm))
        (armLaw arm) := by
    intro arm
    simpa [RewardKernel.selectedMeasure_contextIndependentOfActionLaws] using
      law.hasSubgaussianMGF () arm
  simpa [selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret] using
    (selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_nonneg_and_le
      model armLaw hprob
        (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
        hmean hsubG defaultAction T hlarge)

/-- The exact armwise-bounded expected pseudo-regret family is logarithmic. -/
theorem selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret_isBigO_log
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc (lo arm) (hi arm)
          ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K) :
    (selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret
      model armLaw hprob lo hi defaultAction) =O[atTop]
      (fun T : Nat => Real.log (((T + 1 : Nat) : Real))) := by
  let law :=
    RewardKernel.contextIndependentArmwiseBoundedCenteredRewardKernelLaw
      (Context := Unit) armLaw hprob model.mean lo hi hmeas hbound hmean
  have hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => (((reward - model.mean arm : Rat) : Real)))
        (Concentration.intervalVarianceProxy (lo arm) (hi arm))
        (armLaw arm) := by
    intro arm
    simpa [RewardKernel.selectedMeasure_contextIndependentOfActionLaws] using
      law.hasSubgaussianMGF () arm
  simpa [selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret] using
    (selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_isBigO_log
      model armLaw hprob
        (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
        hmean hsubG defaultAction)

/-- The exact armwise-bounded expected pseudo-regret is little-o of `T + 1`. -/
theorem selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret_isLittleO_natCast_succ
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc (lo arm) (hi arm)
          ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K) :
    (selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret
      model armLaw hprob lo hi defaultAction) =o[atTop]
      (fun T : Nat => (((T + 1 : Nat) : Real))) :=
  (selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret_isBigO_log
    model armLaw hprob lo hi hmeas hbound hmean
      defaultAction).trans_isLittleO
        log_natCast_succ_isLittleO_natCast_succ

/-- Expected armwise-bounded sampled-successor regret normalized by `T + 1`. -/
noncomputable def
    selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedAveragePseudoRegret
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (defaultAction : Fin K)
    (T : Nat) : Real :=
  selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret
      model armLaw hprob lo hi defaultAction T /
    (((T + 1 : Nat) : Real))

/--
For stationary finite-arm reward laws bounded almost surely in arm-dependent
intervals, the expected pseudo-regret of the horizon-indexed canonical
sampled-pair UCB family, normalized by `T + 1`, tends to zero.

No pointwise nondegeneracy premise `lo arm < hi arm` is needed because the
parent practical route pads the finite maximum of the genuine Hoeffding
proxies before using it as the UCB parameter.
-/
theorem selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedAveragePseudoRegret_tendsto_zero
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc (lo arm) (hi arm)
          ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K) :
    Tendsto
      (selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedAveragePseudoRegret
        model armLaw hprob lo hi defaultAction)
      atTop (nhds 0) := by
  have hlimit :=
    (selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret_isLittleO_natCast_succ
      model armLaw hprob lo hi hmeas hbound hmean
        defaultAction).tendsto_div_nhds_zero
  convert hlimit using 1

end UCB
end BanditRLProof
