import BanditRLProof
import Mathlib.Tactic.NormNum

/-!
# Textbook Part IV Chapter 14 public canary

This root-import canary exercises the exact extended-real KL branches, the
event data-processing adapter, and the unconditional Bretagnolle--Huber
terminal.  It does not claim the adaptive-history KL decomposition deferred to
Chapter 15.
-/

namespace BanditRLProof.TextbookPartIVChapter14Canary

open MeasureTheory Set
open scoped ENNReal
open LowerBounds

section RelativeEntropySurface

example {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    (hPQ : ¬ P ≪ Q) :
    relativeEntropy P Q = ∞ :=
  relativeEntropy_eq_top_of_not_absolutelyContinuous hPQ

example {α : Type*} [MeasurableSpace α] {P Q : Measure α} :
    relativeEntropy P Q ≠ ∞ ↔
      P ≪ Q ∧ Integrable (llr P Q) P :=
  relativeEntropy_ne_top_iff

end RelativeEntropySurface

section BinaryTesting

example :
    bretagnolleHuberScale (bernoulliRelativeEntropy (1 / 4) (3 / 4)) ≤
      (1 / 4 : Real) + (1 - 3 / 4) := by
  apply binaryBretagnolleHuber
  · constructor <;> norm_num
  · constructor <;> norm_num

/-- A support-mismatched Bernoulli comparison takes the infinite-KL branch. -/
example : bretagnolleHuberScale (bernoulliRelativeEntropy 0 1) = 0 := by
  norm_num [bernoulliRelativeEntropy, KLUCB.bernoulliKL,
    KLUCB.IsBernoulliParameter, bretagnolleHuberScale]

end BinaryTesting

section EventTesting

variable {α : Type*} [MeasurableSpace α]
variable (P Q : Measure α)
variable [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
variable {A : Set α} (hA : MeasurableSet A)

example :
    bernoulliRelativeEntropy (P.real A) (Q.real A) ≤
      relativeEntropy P Q :=
  bernoulliRelativeEntropy_event_le hA

example :
    bretagnolleHuberScale (relativeEntropy P Q) ≤
      P.real A + Q.real Aᶜ :=
  bretagnolleHuber hA

end EventTesting

#print axioms LowerBounds.relativeEntropy
#print axioms LowerBounds.relativeEntropy_of_absolutelyContinuous_of_integrable
#print axioms LowerBounds.relativeEntropy_of_probability_absolutelyContinuous_of_integrable
#print axioms LowerBounds.relativeEntropy_eq_top_of_not_absolutelyContinuous
#print axioms LowerBounds.relativeEntropy_ne_top_iff
#print axioms LowerBounds.bernoulliRelativeEntropy
#print axioms LowerBounds.rnDeriv_restrict_restrict
#print axioms LowerBounds.relativeEntropy_restrict_add_compl
#print axioms LowerBounds.bernoulliKLCore_event_le
#print axioms LowerBounds.exp_neg_half_bernoulliKLCore_le_affinity
#print axioms LowerBounds.half_binaryAffinity_sq_le_eventError
#print axioms LowerBounds.binaryBretagnolleHuberCore
#print axioms LowerBounds.bretagnolleHuberScale
#print axioms LowerBounds.bretagnolleHuberScale_nonneg
#print axioms LowerBounds.binaryBretagnolleHuber
#print axioms LowerBounds.bernoulliRelativeEntropy_event_le
#print axioms LowerBounds.bretagnolleHuberScale_antitone
#print axioms LowerBounds.bretagnolleHuber

end BanditRLProof.TextbookPartIVChapter14Canary
