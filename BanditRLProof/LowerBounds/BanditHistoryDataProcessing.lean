import BanditRLProof.LowerBounds.BanditHistoryKL
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!
# Data processing for Chapter 15 bandit histories

This module proves the measurable-observation data-processing leaf needed by
the stopping-time extension in Lattimore--Szepesvari, *Bandit Algorithms*,
Exercise 15.7.  It also specializes the leaf to the compiled deterministic
finite-history divergence decomposition of Lemma 15.1.

The final stopping-time theorem needs an additional stopped-history law whose
KL cost contains only pulls through the stopping time.  The results below do
not assume or claim that missing identity.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v w

set_option maxHeartbeats 800000 in
/--
Kullback--Leibler divergence cannot increase under a measurable observation.

The proof uses Mathlib's identification of the pushed-forward Radon--Nikodym
derivative with a conditional expectation, followed by conditional Jensen for
the convex `klFun`.  The infinite-KL branch is kept explicit; in the finite
branch, data processing also proves finiteness of the observed KL rather than
assuming it.
-/
theorem klDiv_map_le
    {Source Target : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target]
    (mu nu : Measure Source) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (observe : Source -> Target) (hobserve : Measurable observe) :
    InformationTheory.klDiv (mu.map observe) (nu.map observe) <=
      InformationTheory.klDiv mu nu := by
  by_cases hsource : InformationTheory.klDiv mu nu = ∞
  · rw [hsource]
    exact le_top
  rcases InformationTheory.klDiv_ne_top_iff.mp hsource with ⟨h_ac, hllr⟩
  have hmap_ac : mu.map observe ≪ nu.map observe := h_ac.map hobserve
  let density : Source -> Real := fun x => (mu.rnDeriv nu x).toReal
  let observedDensity : Target -> Real := fun y =>
    ((mu.map observe).rnDeriv (nu.map observe) y).toReal
  have hdensity_integrable : Integrable density nu := by
    exact Measure.integrable_toReal_rnDeriv
  have hkl_integrable :
      Integrable (fun x => InformationTheory.klFun (density x)) nu := by
    exact (InformationTheory.integrable_klFun_rnDeriv_iff h_ac).2 hllr
  have hrn :
      (fun x => observedDensity (observe x)) =ᵐ[nu]
        nu[density | MeasurableSpace.comap observe ‹MeasurableSpace Target›] := by
    exact MeasureTheory.toReal_rnDeriv_map h_ac hobserve
  have hdensity_nonneg : ∀ᵐ x ∂nu, density x ∈ Set.Ici (0 : Real) := by
    exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  have hdensity_nonneg_ae : (0 : Source -> Real) ≤ᵐ[nu] density := by
    exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  have hjensen :
      (fun x => InformationTheory.klFun
        (nu[density | MeasurableSpace.comap observe ‹MeasurableSpace Target›] x))
        ≤ᵐ[nu]
      nu[(fun x => InformationTheory.klFun (density x)) |
        MeasurableSpace.comap observe ‹MeasurableSpace Target›] := by
    simpa [Function.comp_def] using
      (InformationTheory.convexOn_klFun.map_condExp_le
        (μ := nu) (m := MeasurableSpace.comap observe ‹MeasurableSpace Target›)
        hobserve.comap_le
        (InformationTheory.continuous_klFun.lowerSemicontinuous.lowerSemicontinuousOn
          (Set.Ici (0 : Real)))
        hdensity_nonneg isClosed_Ici hdensity_integrable
        (by simpa [Function.comp_def] using hkl_integrable))
  have hleft_integrable :
      Integrable
        (fun x => InformationTheory.klFun
          (nu[density | MeasurableSpace.comap observe ‹MeasurableSpace Target›] x)) nu := by
    refine (integrable_condExp
      (μ := nu) (m := MeasurableSpace.comap observe ‹MeasurableSpace Target›)
      (f := fun x => InformationTheory.klFun (density x))).mono' ?_ ?_
    · exact
        (InformationTheory.continuous_klFun.measurable.comp
          (stronglyMeasurable_condExp.mono hobserve.comap_le).measurable).aestronglyMeasurable
    · filter_upwards [condExp_nonneg hdensity_nonneg_ae, hjensen] with x hx hle
      rw [Real.norm_eq_abs,
        abs_of_nonneg (InformationTheory.klFun_nonneg hx)]
      exact hle
  have hobserved_comp_integrable :
      Integrable
        (fun x => InformationTheory.klFun (observedDensity (observe x))) nu := by
    refine hleft_integrable.congr ?_
    filter_upwards [hrn] with x hx
    rw [hx]
  have hobserved_integrable :
      Integrable (fun y => InformationTheory.klFun (observedDensity y))
        (nu.map observe) := by
    have hobservedDensity_measurable : Measurable observedDensity :=
      ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _)
    exact (integrable_map_measure
      (μ := nu) (f := observe)
      (g := fun y => InformationTheory.klFun (observedDensity y))
      (InformationTheory.continuous_klFun.measurable.comp
        hobservedDensity_measurable).aestronglyMeasurable
      hobserve.aemeasurable).2
        (by simpa [Function.comp_def] using hobserved_comp_integrable)
  have hmap_llr :
      Integrable (llr (mu.map observe) (nu.map observe)) (mu.map observe) := by
    exact (InformationTheory.integrable_klFun_rnDeriv_iff hmap_ac).1
      (by simpa [observedDensity] using hobserved_integrable)
  have htarget :
      InformationTheory.klDiv (mu.map observe) (nu.map observe) ≠ ∞ :=
    InformationTheory.klDiv_ne_top_iff.mpr ⟨hmap_ac, hmap_llr⟩
  apply (ENNReal.toReal_le_toReal htarget hsource).mp
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun hmap_ac,
    InformationTheory.toReal_klDiv_eq_integral_klFun h_ac]
  rw [integral_map hobserve.aemeasurable
    (by simpa [observedDensity] using hobserved_integrable.aestronglyMeasurable)]
  calc
    ∫ x, InformationTheory.klFun (observedDensity (observe x)) ∂nu =
        ∫ x, InformationTheory.klFun
          (nu[density | MeasurableSpace.comap observe
            ‹MeasurableSpace Target›] x) ∂nu := by
      exact integral_congr_ae (hrn.fun_comp InformationTheory.klFun)
    _ <= ∫ x,
        nu[(fun x => InformationTheory.klFun (density x)) |
          MeasurableSpace.comap observe ‹MeasurableSpace Target›] x ∂nu :=
      integral_mono_ae hleft_integrable integrable_condExp hjensen
    _ = ∫ x, InformationTheory.klFun (density x) ∂nu := by
      exact integral_condExp hobserve.comap_le

/--
Any measurable statistic of a deterministic finite bandit history has KL at
most the first-law expected pull-count-weighted arm information.

This is the data-processing half of Exercise 15.7 at a fixed horizon.  It is
not the stopping-time theorem because the right-hand side still counts all
pulls through `lastRound`.
-/
theorem klDiv_observedBanditHistory_le_expectedPulls_sum
    {K : Nat} {Reward : Type v} {Observation : Type w}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    [MeasurableSpace Observation]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (lastRound : Nat)
    (observe : History.FinitePairHistory (Fin K) Reward lastRound -> Observation)
    (hobserve : Measurable observe) :
    InformationTheory.klDiv
        ((canonicalBanditHistoryMeasure algorithm armLaw lastRound).map observe)
        ((canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound).map observe) <=
      ∑ arm : Fin K,
        canonicalRealizedExpectedPullCountThrough
            algorithm armLaw lastRound arm *
          InformationTheory.klDiv (armLaw arm) (referenceArmLaw arm) := by
  calc
    InformationTheory.klDiv
        ((canonicalBanditHistoryMeasure algorithm armLaw lastRound).map observe)
        ((canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound).map observe) <=
        InformationTheory.klDiv
          (canonicalBanditHistoryMeasure algorithm armLaw lastRound)
          (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound) :=
      klDiv_map_le _ _ observe hobserve
    _ = _ := banditHistoryRelativeEntropy_eq_expectedPulls_sum
      algorithm armLaw referenceArmLaw lastRound

end

end LowerBounds
end BanditRLProof
