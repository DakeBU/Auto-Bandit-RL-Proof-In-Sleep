import BanditRLProof.Algorithms.UCBFiniteArmSubGaussianSampledAsymptotics

/-!
# Sampled-pair UCB consistency for bounded finite-arm laws

This module derives the direct centered sub-Gaussian contracts required by the
stationary finite-arm sampled-pair consistency theorem from a common almost-
sure reward interval and exact arm means.
-/

open scoped BigOperators ENNReal NNReal

open Filter MeasureTheory ProbabilityTheory
open Asymptotics

namespace BanditRLProof
namespace UCB

/--
Exact sampled-successor expected pseudo-regret for stationary finite-arm laws
bounded almost surely in a common interval. The genuine armwise proxy is the
common Hoeffding proxy; the parent practical route pads its finite maximum.
-/
noncomputable def selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (defaultAction : Fin K)
    (T : Nat) : Real :=
  selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret
    model armLaw hprob
      (fun _ => Concentration.intervalVarianceProxy lo hi)
      defaultAction T

/-- The exact common-bounded expected pseudo-regret family is logarithmic. -/
theorem selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret_isBigO_log
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc lo hi ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K) :
    (selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret
      model armLaw hprob lo hi defaultAction) =O[atTop]
      (fun T : Nat => Real.log (((T + 1 : Nat) : Real))) := by
  have hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => (((reward - model.mean arm : Rat) : Real)))
        (Concentration.intervalVarianceProxy lo hi) (armLaw arm) := by
    intro arm
    letI : IsProbabilityMeasure (armLaw arm) := hprob arm
    simpa [Rat.cast_sub] using
      (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mu := armLaw arm)
        (X := fun reward : Rat => ((reward : Rat) : Real))
        (lo := lo)
        (hi := hi)
        (mean := ((model.mean arm : Rat) : Real))
        (hmeas arm) (hbound arm) (hmean arm))
  simpa [selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret] using
    (selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_isBigO_log
      model armLaw hprob
        (fun _ => Concentration.intervalVarianceProxy lo hi)
        hmean hsubG defaultAction)

/-- The exact common-bounded expected pseudo-regret is little-o of `T + 1`. -/
theorem selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret_isLittleO_natCast_succ
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc lo hi ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K) :
    (selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret
      model armLaw hprob lo hi defaultAction) =o[atTop]
      (fun T : Nat => (((T + 1 : Nat) : Real))) :=
  (selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret_isBigO_log
    model armLaw hprob lo hi hmeas hbound hmean
      defaultAction).trans_isLittleO
        log_natCast_succ_isLittleO_natCast_succ

/-- Expected common-bounded sampled-successor regret normalized by `T + 1`. -/
noncomputable def
    selectedPolicySuccessorBoundedFiniteArmExpectedAveragePseudoRegret
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (defaultAction : Fin K)
    (T : Nat) : Real :=
  selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret
      model armLaw hprob lo hi defaultAction T /
    (((T + 1 : Nat) : Real))

/--
For stationary finite-arm reward laws bounded almost surely in a common
interval, the expected pseudo-regret of the horizon-indexed canonical
sampled-pair UCB family, normalized by `T + 1`, tends to zero.

No nondegeneracy premise `lo < hi` is needed because the parent practical
route pads the genuine Hoeffding proxy before using it as the UCB parameter.
-/
theorem selectedPolicySuccessorBoundedFiniteArmExpectedAveragePseudoRegret_tendsto_zero
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc lo hi ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K) :
    Tendsto
      (selectedPolicySuccessorBoundedFiniteArmExpectedAveragePseudoRegret
        model armLaw hprob lo hi defaultAction)
      atTop (nhds 0) := by
  have hlimit :=
    (selectedPolicySuccessorBoundedFiniteArmExpectedPseudoRegret_isLittleO_natCast_succ
      model armLaw hprob lo hi hmeas hbound hmean
        defaultAction).tendsto_div_nhds_zero
  convert hlimit using 1

end UCB
end BanditRLProof
