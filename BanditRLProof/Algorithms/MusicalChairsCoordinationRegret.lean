import BanditRLProof.Algorithms.MusicalChairsCoordinationTime

namespace BanditRLProof.MusicalChairs
open scoped Classical ENNReal
set_option autoImplicit false

noncomputable def fixedPlayers {n k : ℕ} (s : State n k) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s i ≠ none)

noncomputable def hitFixed {n k : ℕ} (s : State n k) (draw : Fin n → Fin k) :
    Finset (Fin n) := (fixedPlayers s).filter (fun i => ¬ CollisionFree (action s draw) i)

noncomputable def safeFixed {n k : ℕ} (s : State n k) (draw : Fin n → Fin k) :
    Finset (Fin n) := (fixedPlayers s) \ (hitFixed s draw)

theorem fixed_action_injective {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) : Set.InjOn (action s draw) (fixedPlayers s) := by
  intro i hi j hj heq
  have hi' : s i ≠ none := (Finset.mem_filter.mp hi).2
  have hj' : s j ≠ none := (Finset.mem_filter.mp hj).2
  cases hsi : s i with
  | none => exact False.elim (hi' hsi)
  | some a =>
    cases hsj : s j with
    | none => exact False.elim (hj' hsj)
    | some b =>
      have hab : a = b := by simpa [action, hsi, hsj] using heq
      exact hs i j a hsi (hsj.trans (congrArg some hab.symm))

theorem hitFixed_partner {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) (i : Fin n) (hi : i ∈ hitFixed s draw) :
    ∃ j, s j = none ∧ action s draw j = action s draw i := by
  obtain ⟨hif, hic⟩ := Finset.mem_filter.mp hi
  obtain ⟨j, hji, haj⟩ : ∃ j, j ≠ i ∧ action s draw j = action s draw i := by
    simpa [CollisionFree] using hic
  refine ⟨j, ?_, haj⟩
  by_contra hj
  have hjf : j ∈ fixedPlayers s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  exact hji (fixed_action_injective s draw hs hjf hif haj)

theorem hitFixed_card_le {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) : (hitFixed s draw).card ≤ unfixedCount s := by
  let f : Fin n → Fin n := fun i => if h : i ∈ hitFixed s draw then
    (hitFixed_partner s draw hs i h).choose else i
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    change i ∈ hitFixed s draw at hi
    change f i ∈ Finset.univ.filter (fun i => s i = none)
    have hf := (hitFixed_partner s draw hs i hi).choose_spec
    simp only [f, dif_pos hi, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hf.1
  · intro i hi j hj hij
    change i ∈ hitFixed s draw at hi
    change j ∈ hitFixed s draw at hj
    have hfi := (hitFixed_partner s draw hs i hi).choose_spec.2
    have hfj := (hitFixed_partner s draw hs j hj).choose_spec.2
    have heq : action s draw i = action s draw j := by
      rw [← hfi, ← hfj]
      congr 1
      simpa only [f, dif_pos hi, dif_pos hj] using hij
    exact fixed_action_injective s draw hs
      (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 heq

theorem safeFixed_count {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) : n ≤ (safeFixed s draw).card + 2 * unfixedCount s := by
  have hpartition : (fixedPlayers s).card + unfixedCount s = n := by
    simpa [fixedPlayers, unfixedCount] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (fun i => s i ≠ none)
  have hhit : hitFixed s draw ⊆ fixedPlayers s := Finset.filter_subset _ _
  have hsplit := Finset.card_sdiff_add_card_eq_card hhit
  have hle := hitFixed_card_le s draw hs
  change (safeFixed s draw).card + (hitFixed s draw).card = (fixedPlayers s).card at hsplit
  omega


noncomputable def roundMeanReward {n k : ℕ} (mu : Fin k → ℝ)
    (s : State n k) (draw : Fin n → Fin k) : ℝ :=
  ∑ i : Fin n, if CollisionFree (action s draw) i then mu (action s draw i) else 0

noncomputable def roundPseudoRegret {n k : ℕ} (S : Finset (Fin k)) (mu : Fin k → ℝ)
    (s : State n k) (draw : Fin n → Fin k) : ℝ :=
  (∑ a ∈ S, mu a) - roundMeanReward mu s draw

theorem safeFixed_mem {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (i : Fin n) (hi : i ∈ safeFixed s draw) :
    i ∈ fixedPlayers s ∧ CollisionFree (action s draw) i := by
  have h := Finset.mem_sdiff.mp hi
  refine ⟨h.1, ?_⟩
  by_contra hc
  exact h.2 (Finset.mem_filter.mpr ⟨h.1, hc⟩)

theorem safeFixed_arms_subset {n k : ℕ} (S : Finset (Fin k)) (s : State n k)
    (draw : Fin n → Fin k) (hw : FixedWithin (fun _ => S) s) :
    (safeFixed s draw).image (action s draw) ⊆ S := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  have hif := (safeFixed_mem s draw i hi).1
  have hn : s i ≠ none := (Finset.mem_filter.mp hif).2
  cases hsi : s i with
  | none => exact False.elim (hn hsi)
  | some a => simpa [action, hsi] using hw i a hsi

theorem safeFixed_reward_le {n k : ℕ} (mu : Fin k → ℝ)
    (hmu : ∀ a, 0 ≤ mu a) (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) :
    ∑ a ∈ (safeFixed s draw).image (action s draw), mu a ≤ roundMeanReward mu s draw := by
  rw [Finset.sum_image]
  · calc
      _ = ∑ i ∈ safeFixed s draw,
          if CollisionFree (action s draw) i then mu (action s draw i) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos (safeFixed_mem s draw i hi).2]
      _ ≤ roundMeanReward mu s draw := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro i _ _
        split_ifs
        · exact hmu _
        · exact le_rfl
  · intro i hi j hj heq
    exact fixed_action_injective s draw hs (safeFixed_mem s draw i hi).1
      (safeFixed_mem s draw j hj).1 heq

theorem roundPseudoRegret_le_twice_unfixed {n k : ℕ} (S : Finset (Fin k))
    (hcard : S.card = n) (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (s : State n k) (draw : Fin n → Fin k) (hs : DistinctFixed s)
    (hw : FixedWithin (fun _ => S) s) :
    roundPseudoRegret S mu s draw ≤ 2 * (unfixedCount s : ℝ) := by
  let A := (safeFixed s draw).image (action s draw)
  have hsub : A ⊆ S := safeFixed_arms_subset S s draw hw
  have hA : A.card = (safeFixed s draw).card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj heq
    exact fixed_action_injective s draw hs (safeFixed_mem s draw i hi).1
      (safeFixed_mem s draw j hj).1 heq
  have hmissing : (S \ A).card ≤ 2 * unfixedCount s := by
    have hp := Finset.card_sdiff_add_card_eq_card hsub
    have hc := safeFixed_count s draw hs
    omega
  have hsum : (∑ a ∈ S \ A, mu a) ≤ ((S \ A).card : ℝ) := by
    simpa using (S \ A).sum_le_card_nsmul mu (1 : ℝ) (fun a _ => (hmu a).2)
  have hreward := safeFixed_reward_le mu (fun a => (hmu a).1) s draw hs
  have hpartition := Finset.sum_sdiff hsub (f := mu)
  have hcast : ((S \ A).card : ℝ) ≤ 2 * (unfixedCount s : ℝ) := by exact_mod_cast hmissing
  change (∑ a ∈ S, mu a) - roundMeanReward mu s draw ≤ _
  change (∑ a ∈ A, mu a) ≤ _ at hreward
  linarith


theorem roundPseudoRegret_nonneg {n k : ℕ} (S : Finset (Fin k))
    (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a) (s : State n k)
    (draw : Fin n → Fin k) (hw : FixedWithin (fun _ => S) s)
    (hd : ∀ i, draw i ∈ S) : 0 ≤ roundPseudoRegret S mu s draw := by
  let J := Finset.univ.filter (fun i => CollisionFree (action s draw) i)
  have hinj : Set.InjOn (action s draw) J := by
    intro i hi j hj heq
    by_contra hij
    exact (Finset.mem_filter.mp hi).2 j (Ne.symm hij) heq.symm
  have hsub : J.image (action s draw) ⊆ S := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    cases hsi : s i with
    | none => simpa [action, hsi] using hd i
    | some a => simpa [action, hsi] using hw i a hsi
  have hrew : roundMeanReward mu s draw = ∑ a ∈ J.image (action s draw), mu a := by
    rw [Finset.sum_image hinj]
    simp [J, Finset.sum_filter, roundMeanReward]
  unfold roundPseudoRegret
  rw [sub_nonneg, hrew]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hmu a)

theorem expected_round_charge {n k : ℕ} (S : Finset (Fin k)) (hne : S.Nonempty)
    (hcard : S.card = n) (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (s : State n k) (hs : DistinctFixed s) (hw : FixedWithin (fun _ => S) s) :
    ∑ draw, (jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw *
      ENNReal.ofReal (roundPseudoRegret S mu s draw) ≤ 2 * (unfixedCount s : ℝ≥0∞) := by
  let q := jointDraw (fun _ : Fin n => S) (fun _ => hne)
  have hq : ∑ draw, q draw = 1 := by simpa [tsum_fintype] using q.tsum_coe
  calc
    _ ≤ ∑ draw, q draw * (2 * (unfixedCount s : ℝ≥0∞)) := by
      apply Finset.sum_le_sum
      intro draw _
      apply mul_le_mul_right
      have h := ENNReal.ofReal_le_ofReal (roundPseudoRegret_le_twice_unfixed
        S hcard mu hmu s draw hs hw)
      simpa using h
    _ = _ := by rw [← Finset.sum_mul, hq, one_mul]

noncomputable def expectedCoordinationRegret {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (mu : Fin k → ℝ) (T : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, ∑ s, (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s *
    ∑ draw, (jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw *
      ENNReal.ofReal (roundPseudoRegret S mu s draw)

theorem expectedCoordinationRegret_le {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (hcard : S.card = n) (mu : Fin k → ℝ)
    (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1) (T : ℕ) :
    expectedCoordinationRegret (n := n) S hne mu T ≤ 8 * (n : ℝ≥0∞)^2 := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, ∑ s,
        (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s *
          (2 * (unfixedCount s : ℝ≥0∞)) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro s _
      by_cases hp : s ∈ (stateLaw (fun _ : Fin n => S) (fun _ => hne) t).support
      · exact mul_le_mul_right (expected_round_charge S hne hcard mu hmu s
          (stateLaw_distinct _ _ t s hp) (stateLaw_within _ _ t s hp)) _
      · have hz : (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s = 0 := by
          simpa [PMF.mem_support_iff] using hp
        simp [hz]
    _ = 2 * (∑ t ∈ Finset.range T, ∑ s,
        (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s *
          (unfixedCount s : ℝ≥0∞)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ 2 * (4 * (n : ℝ≥0∞)^2) :=
      mul_le_mul_right (expected_unfixed_occupation_le S hne hcard T) _
    _ = _ := by ring


theorem expectedCoordinationRegret_toReal {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a) (T : ℕ) :
    (expectedCoordinationRegret (n := n) S hne mu T).toReal =
      ∑ t ∈ Finset.range T, ∑ s,
        ((stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s).toReal *
        ∑ draw, ((jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw).toReal *
          roundPseudoRegret S mu s draw := by
  unfold expectedCoordinationRegret
  rw [ENNReal.toReal_sum (by simp [ENNReal.mul_ne_top, PMF.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro t _
  rw [ENNReal.toReal_sum (by simp [ENNReal.mul_ne_top, PMF.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro s _
  rw [ENNReal.toReal_mul]
  by_cases hp : s ∈ (stateLaw (fun _ : Fin n => S) (fun _ => hne) t).support
  · rw [ENNReal.toReal_sum (by simp [ENNReal.mul_ne_top, PMF.apply_ne_top])]
    congr 1
    apply Finset.sum_congr rfl
    intro draw _
    rw [ENNReal.toReal_mul]
    by_cases hq : draw ∈ (jointDraw (fun _ : Fin n => S) (fun _ => hne)).support
    · rw [ENNReal.toReal_ofReal (roundPseudoRegret_nonneg S mu hmu s draw
        (stateLaw_within _ _ t s hp) (jointDraw_mem _ _ draw hq))]
    · have hz : (jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw = 0 := by
        simpa [PMF.mem_support_iff] using hq
      simp [hz]
  · have hz : (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s = 0 := by
      simpa [PMF.mem_support_iff] using hp
    simp [hz]

theorem expectedCoordinationRegret_real_le {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (hcard : S.card = n) (mu : Fin k → ℝ)
    (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∑ s,
      ((stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s).toReal *
      ∑ draw, ((jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw).toReal *
        roundPseudoRegret S mu s draw) ≤ 8 * (n : ℝ)^2 := by
  rw [← expectedCoordinationRegret_toReal S hne mu (fun a => (hmu a).1) T]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  simpa using expectedCoordinationRegret_le S hne hcard mu hmu T


end BanditRLProof.MusicalChairs
