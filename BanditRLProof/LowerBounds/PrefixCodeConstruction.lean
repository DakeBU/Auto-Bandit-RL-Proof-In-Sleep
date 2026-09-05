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

theorem binary_level_mul_kraft_weight {k n : ℕ} (h : k ≤ n) :
    (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k = 2 ^ (n - k) := by
  have hn : n = (n - k) + k := by omega
  nth_rw 1 [hn]
  rw [pow_add, one_div_pow]
  field_simp

/-- Real Kraft slack supplies the integer capacity needed to insert a word. -/
theorem exists_binaryWord_of_kraft_lt_one
    (S : Finset (List Bool)) (n : ℕ)
    (hlen : ∀ w ∈ S, w.length ≤ n)
    (hk : (∑ w ∈ S, (1 / 2 : ℝ) ^ w.length) < 1) :
    ∃ v : List Bool, v.length = n ∧ ∀ w ∈ S, ¬ w <+: v := by
  apply exists_binaryWord_avoiding_prefixes S n hlen
  have h := mul_lt_mul_of_pos_left hk (pow_pos (by norm_num : (0 : ℝ) < 2) n)
  rw [Finset.mul_sum, mul_one] at h
  have he : (∑ w ∈ S, (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ w.length) =
      ∑ w ∈ S, (2 : ℝ) ^ (n - w.length) := by
    exact Finset.sum_congr rfl fun w hw => binary_level_mul_kraft_weight (hlen w hw)
  rw [he] at h
  exact_mod_cast h

/-- The greedy insertion preserves prefix freedom in both directions. -/
theorem exists_prefixFree_insert_of_kraft_lt_one
    (S : Finset (List Bool)) (n : ℕ)
    (hfree : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b)
    (hlen : ∀ w ∈ S, w.length ≤ n)
    (hk : (∑ w ∈ S, (1 / 2 : ℝ) ^ w.length) < 1) :
    ∃ v : List Bool, v.length = n ∧ v ∉ S ∧
      ∀ a ∈ insert v S, ∀ b ∈ insert v S, a <+: b → a = b := by
  obtain ⟨v, hvlen, hv⟩ := exists_binaryWord_of_kraft_lt_one S n hlen hk
  have hvnot : v ∉ S := by
    intro h
    exact hv v h (by rfl)
  have hreverse : ∀ w ∈ S, ¬ v <+: w := by
    intro w hw hpre
    obtain ⟨t, rfl⟩ := hpre
    have ht : t.length = 0 := by
      have h := hlen (v ++ t) hw
      simp only [List.length_append, hvlen] at h
      omega
    have ht' : t = [] := List.length_eq_zero_iff.mp ht
    simp only [ht', List.append_nil] at hw
    exact hvnot hw
  refine ⟨v, hvlen, hvnot, ?_⟩
  intro a ha b hb hab
  by_cases hav : a = v
  · subst a
    by_cases hbv : b = v
    · exact hbv.symm
    · exact (hreverse b ((Finset.mem_insert.mp hb).resolve_left hbv) hab).elim
  · have haS := (Finset.mem_insert.mp ha).resolve_left hav
    by_cases hbv : b = v
    · subst b
      exact (hv a haS hab).elim
    · exact hfree a haS b ((Finset.mem_insert.mp hb).resolve_left hbv) hab

end BanditRLProof.LowerBounds
