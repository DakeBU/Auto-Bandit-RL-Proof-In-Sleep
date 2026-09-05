import BanditRLProof.LowerBounds.BanditHistoryKL
import BanditRLProof.LowerBounds.RelativeEntropyFiltration

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

/--
Kullback--Leibler divergence cannot increase under a measurable observation.

The proof reuses Chapter 14's map/trim identity and sub-sigma-algebra
KL contraction. The infinite-KL branch is explicit, so absolute continuity
is derived only in the finite branch and is not a caller assumption.
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
  have h_ac := (InformationTheory.klDiv_ne_top_iff.mp hsource).1
  change relativeEntropy (mu.map observe) (nu.map observe) ≤ relativeEntropy mu nu
  rw [relativeEntropy_map_eq_trim_of_absolutelyContinuous mu nu h_ac observe hobserve]
  exact relativeEntropy_trim_le hobserve.comap_le

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
