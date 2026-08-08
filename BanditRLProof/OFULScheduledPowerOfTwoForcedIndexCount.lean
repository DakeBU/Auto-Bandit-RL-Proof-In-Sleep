import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card

namespace BanditRLProof
namespace OFUL

/--
A horizon-independent forcing predicate for successor indices one below powers
of two. The `Nat.log2` equality makes the predicate decidable without a
classical search over exponents.
-/
def isPowerOfTwoForcedIndex (n : Nat) : Prop :=
  2 ^ Nat.log2 (n + 1) = n + 1

instance instDecidableIsPowerOfTwoForcedIndex (n : Nat) :
    Decidable (isPowerOfTwoForcedIndex n) := by
  unfold isPowerOfTwoForcedIndex
  infer_instance

/-- The computable predicate has the intended existential power-of-two semantics. -/
theorem isPowerOfTwoForcedIndex_iff {n : Nat} :
    isPowerOfTwoForcedIndex n <-> exists k, n + 1 = 2 ^ k := by
  constructor
  · intro hn
    exact ⟨Nat.log2 (n + 1), hn.symm⟩
  · rintro ⟨k, hk⟩
    unfold isPowerOfTwoForcedIndex
    rw [hk, Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two]

/-- Power-of-two forced successor indices strictly below `horizon`. -/
def powerOfTwoForcedIndexSet (horizon : Nat) : Finset Nat :=
  (Finset.range horizon).filter (fun n => isPowerOfTwoForcedIndex n)

/-- Membership combines the prefix bound with the intended power-of-two equation. -/
theorem mem_powerOfTwoForcedIndexSet_iff {horizon n : Nat} :
    n ∈ powerOfTwoForcedIndexSet horizon <->
      n < horizon ∧ exists k, n + 1 = 2 ^ k := by
  simp only [
    powerOfTwoForcedIndexSet,
    Finset.mem_filter,
    Finset.mem_range,
    isPowerOfTwoForcedIndex_iff]

@[simp]
theorem powerOfTwoForcedIndexSet_zero :
    powerOfTwoForcedIndexSet 0 = ∅ := by
  ext n
  simp [mem_powerOfTwoForcedIndexSet_iff]

/-- Index zero is forced exactly in nonempty horizon prefixes. -/
theorem zero_mem_powerOfTwoForcedIndexSet_iff {horizon : Nat} :
    0 ∈ powerOfTwoForcedIndexSet horizon <-> 0 < horizon := by
  constructor
  · intro h
    exact (mem_powerOfTwoForcedIndexSet_iff.mp h).1
  · intro h
    exact mem_powerOfTwoForcedIndexSet_iff.mpr ⟨h, 0, by simp⟩

/--
There are at most `Nat.log2 horizon + 1` power-of-two forced indices below a
horizon. Each member embeds into the image of the admissible exponent range.
-/
theorem card_powerOfTwoForcedIndexSet_le_log2_add_one (horizon : Nat) :
    (powerOfTwoForcedIndexSet horizon).card <= Nat.log2 horizon + 1 := by
  let exponentImage :=
    (Finset.range (Nat.log2 horizon + 1)).image (fun k => 2 ^ k - 1)
  have hsubset : powerOfTwoForcedIndexSet horizon ⊆ exponentImage := by
    intro n hn
    rcases mem_powerOfTwoForcedIndexSet_iff.mp hn with ⟨hn_lt, k, hk⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_range.mpr ?_, ?_⟩
    · apply Nat.lt_succ_iff.mpr
      apply (Nat.le_log2 (Nat.ne_of_gt (Nat.zero_lt_of_lt hn_lt))).mpr
      omega
    · omega
  calc
    (powerOfTwoForcedIndexSet horizon).card <= exponentImage.card :=
      Finset.card_le_card hsubset
    _ <= (Finset.range (Nat.log2 horizon + 1)).card := Finset.card_image_le
    _ = Nat.log2 horizon + 1 := Finset.card_range _

end OFUL
end BanditRLProof
