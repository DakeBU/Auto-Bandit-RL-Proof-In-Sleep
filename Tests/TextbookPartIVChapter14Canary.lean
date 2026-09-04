import BanditRLProof
import Mathlib.Tactic.NormNum

/-!
# Textbook Part IV Chapter 14 public canary

This root-import canary exercises the finite prefix-code/entropy surface, the
exact extended-real KL branches, the full sub-sigma-algebra and event data-
processing adapters, and the unconditional Bretagnolle--Huber terminal.  It
does not claim the adaptive-history KL decomposition deferred to Chapter 15.
-/

namespace BanditRLProof.TextbookPartIVChapter14Canary

open MeasureTheory Set
open scoped BigOperators ENNReal
open LowerBounds

section CodingAndEntropy

variable {Symbol : Type*} [Fintype Symbol] [DecidableEq Symbol]

/-- Concrete two-symbol code exercising every `BinaryPrefixCode` field. -/
def boolOneBitPrefixCode : BinaryPrefixCode Bool where
  encode bit := [bit]
  injective := by
    intro left right h
    simpa using h
  nonempty := by simp
  prefixFree := by
    intro left right h
    rcases h with ⟨tail, htail⟩
    simpa using congrArg List.head? htail

example : boolOneBitPrefixCode.encode false = [false] := rfl

example :
    InformationTheory.UniquelyDecodable
      (Set.range boolOneBitPrefixCode.encode) :=
  boolOneBitPrefixCode.uniquelyDecodable_range

example :
    ∑ word ∈ boolOneBitPrefixCode.codebook,
      (1 / 2 : Real) ^ word.length ≤ 1 :=
  boolOneBitPrefixCode.kraft_inequality

example :
    expectedCodeLength (fun _ : Bool => (1 / 2 : Real))
      boolOneBitPrefixCode = 1 := by
  norm_num [expectedCodeLength, boolOneBitPrefixCode]

example (code : BinaryPrefixCode Symbol) :
    ∑ word ∈ code.codebook, (1 / 2 : Real) ^ word.length ≤ 1 :=
  code.kraft_inequality

example (support : Finset Symbol) (probability : Symbol → Real) :
    discreteEntropyBaseTwo support probability =
      discreteEntropy support probability / Real.log 2 :=
  discreteEntropyBaseTwo_eq_div_log_two support probability

example (support : Finset Symbol) (probability : Symbol → Real)
    (hprobability : ∀ symbol ∈ support,
      0 ≤ probability symbol ∧ probability symbol ≤ 1) :
    0 ≤ discreteEntropy support probability :=
  discreteEntropy_nonneg support probability hprobability

end CodingAndEntropy

section RelativeEntropySurface

example {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    (hPQ : ¬ P ≪ Q) :
    relativeEntropy P Q = (⊤ : ENNReal) :=
  relativeEntropy_eq_top_of_not_absolutelyContinuous hPQ

example {α : Type*} [MeasurableSpace α] {P Q : Measure α} :
    relativeEntropy P Q ≠ (⊤ : ENNReal) ↔
      P ≪ Q ∧ Integrable (llr P Q) P :=
  relativeEntropy_ne_top_iff

example {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    relativeEntropy P Q = 0 ↔ P = Q :=
  relativeEntropy_eq_zero_iff

example {α : Type*} {m m₀ : MeasurableSpace α}
    {P Q : @Measure α m₀} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hm : m ≤ m₀) :
    @relativeEntropy α m (P.trim hm) (Q.trim hm) ≤
      @relativeEntropy α m₀ P Q :=
  relativeEntropy_trim_le hm

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
#print axioms boolOneBitPrefixCode
#print axioms LowerBounds.BinaryPrefixCode.uniquelyDecodable_range
#print axioms LowerBounds.BinaryPrefixCode.kraft_inequality
#print axioms LowerBounds.discreteEntropy
#print axioms LowerBounds.discreteEntropyBaseTwo
#print axioms LowerBounds.discreteEntropyBaseTwo_eq_div_log_two
#print axioms LowerBounds.discreteEntropy_nonneg
#print axioms LowerBounds.expectedCodeLength
#print axioms LowerBounds.expectedCodeLength_nonneg
#print axioms LowerBounds.relativeEntropy_of_absolutelyContinuous_of_integrable
#print axioms LowerBounds.relativeEntropy_of_probability_absolutelyContinuous_of_integrable
#print axioms LowerBounds.relativeEntropy_eq_top_of_not_absolutelyContinuous
#print axioms LowerBounds.relativeEntropy_ne_top_iff
#print axioms LowerBounds.relativeEntropy_eq_zero_iff
#print axioms LowerBounds.relativeEntropy_trim_le
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
