import BanditRLProof.LowerBounds.ShannonLengths
import Mathlib.Data.List.OfFn

namespace BanditRLProof.LowerBounds

/-- All words at depth n in the full binary tree. -/
def binaryWords (n : ℕ) : Finset (List Bool) :=
  Finset.univ.image (fun f : Fin n → Bool => List.ofFn f)

theorem card_binaryWords (n : ℕ) : (binaryWords n).card = 2 ^ n := by
  rw [binaryWords, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

theorem mem_binaryWords_iff (w : List Bool) (n : ℕ) :
    w ∈ binaryWords n ↔ w.length = n := by
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    simp
  · intro h
    subst n
    apply Finset.mem_image.mpr
    exact ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

/-- The descendants of a prefix after n additional bits. -/
def binaryExtensions (w : List Bool) (n : ℕ) : Finset (List Bool) :=
  (binaryWords n).image (fun v => w ++ v)

theorem card_binaryExtensions (w : List Bool) (n : ℕ) :
    (binaryExtensions w n).card = 2 ^ n := by
  rw [binaryExtensions, Finset.card_image_of_injective]
  · exact card_binaryWords n
  · intro a b h
    exact List.append_cancel_left h

theorem mem_binaryExtensions_iff (w v : List Bool) (n : ℕ) :
    v ∈ binaryExtensions w n ↔ w <+: v ∧ v.length = w.length + n := by
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
    exact ⟨List.prefix_append _ _, by simp [(mem_binaryWords_iff u n).1 hu]⟩
  · rintro ⟨⟨u, rfl⟩, hlen⟩
    apply Finset.mem_image.mpr
    refine ⟨u, (mem_binaryWords_iff u n).2 ?_, rfl⟩
    simpa using hlen

/-- Cylinders from incomparable prefixes are disjoint. -/
theorem binaryExtensions_disjoint_of_incomparable
    (u v : List Bool) (m n : ℕ) (huv : ¬ u <+: v) (hvu : ¬ v <+: u) :
    Disjoint (binaryExtensions u m) (binaryExtensions v n) := by
  apply Finset.disjoint_left.mpr
  intro w hu hv
  have h1 := (mem_binaryExtensions_iff u w m).1 hu
  have h2 := (mem_binaryExtensions_iff v w n).1 hv
  exact (List.prefix_or_prefix_of_prefix h1.1 h2.1).elim huv hvu

/-- A free word exists whenever previous prefixes occupy fewer than all level nodes. -/
theorem exists_binaryWord_avoiding_prefixes
    (S : Finset (List Bool)) (n : ℕ)
    (hlen : ∀ w ∈ S, w.length ≤ n)
    (hbudget : (∑ w ∈ S, 2 ^ (n - w.length)) < 2 ^ n) :
    ∃ v : List Bool, v.length = n ∧ ∀ w ∈ S, ¬ w <+: v := by
  let U := S.biUnion (fun w => binaryExtensions w (n - w.length))
  have hcard : U.card < (binaryWords n).card := by
    rw [card_binaryWords]
    calc
      U.card ≤ ∑ w ∈ S, (binaryExtensions w (n - w.length)).card :=
        Finset.card_biUnion_le
      _ = ∑ w ∈ S, 2 ^ (n - w.length) := by simp only [card_binaryExtensions]
      _ < _ := hbudget
  obtain ⟨v, hv, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨v, (mem_binaryWords_iff v n).1 hv, ?_⟩
  intro w hw hpre
  apply hnot
  apply Finset.mem_biUnion.mpr
  refine ⟨w, hw, (mem_binaryExtensions_iff w v (n - w.length)).2 ⟨hpre, ?_⟩⟩
  rw [(mem_binaryWords_iff v n).1 hv]
  have := hlen w hw
  omega

end BanditRLProof.LowerBounds
