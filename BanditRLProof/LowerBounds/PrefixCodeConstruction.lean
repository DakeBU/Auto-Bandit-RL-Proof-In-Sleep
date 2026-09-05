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

/-- Finite Kraft converse, retaining each prescribed length, including equality. -/
theorem exists_prefix_encoding_of_kraft_le_one
    {α : Type*} [DecidableEq α] (s : Finset α) (l : α → ℕ)
    (hk : (∑ i ∈ s, (1 / 2 : ℝ) ^ l i) ≤ 1) :
    ∃ c : α → List Bool, (∀ i ∈ s, (c i).length = l i) ∧
      (∀ i ∈ s, ∀ j ∈ s, c i <+: c j → i = j) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmax⟩ := s.exists_max_image l hs
      let t := s.erase a
      have ht : t ⊂ s := Finset.erase_ssubset ha
      have hkt : (∑ i ∈ t, (1 / 2 : ℝ) ^ l i) < 1 := by
        have he := Finset.sum_erase_add s (fun i => (1 / 2 : ℝ) ^ l i) ha
        have hp : 0 < (1 / 2 : ℝ) ^ l a := by positivity
        dsimp [t]
        linarith
      obtain ⟨c, hcl, hcf⟩ := ih t ht hkt.le
      let S := t.image c
      have hci : Set.InjOn c t := by
        intro i hi j hj hij
        exact hcf i hi j hj (by rw [hij])
      have hSl : ∀ w ∈ S, w.length ≤ l a := by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
        rw [hcl i hi]
        exact hmax i (Finset.mem_of_mem_erase hi)
      have hSk : (∑ w ∈ S, (1 / 2 : ℝ) ^ w.length) < 1 := by
        dsimp [S]
        rw [Finset.sum_image hci]
        have he : (∑ i ∈ t, (1 / 2 : ℝ) ^ (c i).length) =
            ∑ i ∈ t, (1 / 2 : ℝ) ^ l i :=
          Finset.sum_congr rfl fun i hi => by rw [hcl i hi]
        rw [he]
        exact hkt
      have hSf : ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v := by
        intro u hu v hv huv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
        rw [hcf i hi j hj huv]
      obtain ⟨v, hvl, hvnot, hvfree⟩ :=
        exists_prefixFree_insert_of_kraft_lt_one S (l a) hSf hSl hSk
      let d : α → List Bool := fun i => if i = a then v else c i
      have hdmem : ∀ i ∈ s, d i ∈ insert v S := by
        intro i hi
        by_cases hia : i = a
        · simp [d, hia]
        · simp only [d, if_neg hia]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨i, Finset.mem_erase.mpr ⟨hia, hi⟩, rfl⟩)
      have hdi : Set.InjOn d s := by
        intro i hi j hj hd
        by_cases hia : i = a
        · by_cases hja : j = a
          · exact hia.trans hja.symm
          · have hcj : c j ∈ S := Finset.mem_image.mpr
              ⟨j, Finset.mem_erase.mpr ⟨hja, hj⟩, rfl⟩
            have he : v = c j := by simpa [d, hia, hja] using hd
            exact (hvnot (he ▸ hcj)).elim
        · by_cases hja : j = a
          · have hci' : c i ∈ S := Finset.mem_image.mpr
              ⟨i, Finset.mem_erase.mpr ⟨hia, hi⟩, rfl⟩
            have he : c i = v := by simpa [d, hia, hja] using hd
            exact (hvnot (he ▸ hci')).elim
          · apply hci (Finset.mem_erase.mpr ⟨hia, hi⟩) (Finset.mem_erase.mpr ⟨hja, hj⟩)
            simpa [d, hia, hja] using hd
      refine ⟨d, ?_, ?_⟩
      · intro i hi
        by_cases hia : i = a
        · simpa [d, hia] using hvl
        · simpa [d, hia] using hcl i (Finset.mem_erase.mpr ⟨hia, hi⟩)
      · intro i hi j hj hpre
        exact hdi hi hj (hvfree _ (hdmem i hi) _ (hdmem j hj) hpre)
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨fun _ => [], by simp⟩

/-- Backwards-compatible strict version of the finite Kraft converse. -/
theorem exists_prefix_encoding_of_kraft_lt_one
    {α : Type*} [DecidableEq α] (s : Finset α) (l : α → ℕ)
    (hk : (∑ i ∈ s, (1 / 2 : ℝ) ^ l i) < 1) :
    ∃ c : α → List Bool, (∀ i ∈ s, (c i).length = l i) ∧
      (∀ i ∈ s, ∀ j ∈ s, c i <+: c j → i = j) :=
  exists_prefix_encoding_of_kraft_le_one s l hk.le

/-- Non-strict Kraft converse packaged as an actual binary prefix code. -/
theorem exists_binaryPrefixCode_of_kraft_le_one
    {α : Type*} [Fintype α] [DecidableEq α] (l : α → ℕ)
    (hl : ∀ i, 0 < l i) (hk : (∑ i, (1 / 2 : ℝ) ^ l i) ≤ 1) :
    ∃ code : BinaryPrefixCode α, ∀ i, (code.encode i).length = l i := by
  obtain ⟨c, hlen, hfree⟩ := exists_prefix_encoding_of_kraft_le_one Finset.univ l hk
  have hci : Function.Injective c := by
    intro i j hij
    exact hfree i (Finset.mem_univ _) j (Finset.mem_univ _) (by rw [hij])
  have hcne : ∀ i, c i ≠ [] := by
    intro i he
    have h := hlen i (Finset.mem_univ _)
    rw [he] at h
    have := hl i
    simp only [List.length_nil] at h
    omega
  refine ⟨⟨c, hci, hcne, ?_⟩, ?_⟩
  · intro i j hp
    exact hfree i (Finset.mem_univ _) j (Finset.mem_univ _) hp
  · intro i
    exact hlen i (Finset.mem_univ _)

/-- Backwards-compatible strict Kraft packaging. -/
theorem exists_binaryPrefixCode_of_kraft_lt_one
    {α : Type*} [Fintype α] [DecidableEq α] (l : α → ℕ)
    (hl : ∀ i, 0 < l i) (hk : (∑ i, (1 / 2 : ℝ) ^ l i) < 1) :
    ∃ code : BinaryPrefixCode α, ∀ i, (code.encode i).length = l i :=
  exists_binaryPrefixCode_of_kraft_le_one l hl hk.le

/-- Every finite uniquely decodable encoder has a prefix code with exactly
the same symbol lengths (the boxed assertion in Chapter 14, Section 14.1). -/
theorem exists_prefixCode_of_uniquelyDecodable
    {α : Type*} [Fintype α] (c : α → List Bool) (hinj : Function.Injective c)
    (hud : InformationTheory.UniquelyDecodable (Set.range c)) :
    ∃ code : BinaryPrefixCode α, ∀ i, (code.encode i).length = (c i).length := by
  classical
  have hl (i : α) : 0 < (c i).length := by
    have hn : c i ≠ [] := fun h => hud.epsilon_not_mem ⟨i, h⟩
    exact List.length_pos_iff.mpr hn
  have hset : ((Finset.univ.image c : Finset (List Bool)) : Set (List Bool)) =
      Set.range c := by ext w; simp
  have hk := InformationTheory.kraft_mcmillan_inequality (S := Finset.univ.image c)
    (hset.symm ▸ hud)
  have hki : (∑ i, (1 / 2 : ℝ) ^ (c i).length) ≤ 1 := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat,
      Finset.sum_image (fun i _ j _ h => hinj h)] using hk
  exact exists_binaryPrefixCode_of_kraft_le_one (fun i => (c i).length) hl hki

/-- A realizable finite prefix code attains the one-bit entropy sandwich.
This proves existence, not Huffman's algorithm or optimality. -/
theorem exists_binaryPrefixCode_entropy_sandwich
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∃ code : BinaryPrefixCode α,
      discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength p code ∧
      expectedCodeLength p code ≤ discreteEntropyBaseTwo Finset.univ p + 1 := by
  obtain ⟨l, hl, hk, he⟩ := exists_lengths_kraft_lt_one_entropy_bound p hp hs
  obtain ⟨code, hc⟩ := exists_binaryPrefixCode_of_kraft_lt_one l hl hk
  refine ⟨code, discreteEntropyBaseTwo_le_expectedCodeLength p hp hs code, ?_⟩
  simpa only [expectedCodeLength, hc] using he

end BanditRLProof.LowerBounds
