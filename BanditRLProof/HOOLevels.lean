import BanditRLProof.HOOModel

/-! Finite complete levels of the infinite HOO covering tree. -/
namespace BanditRLProof.HOO

def nodesAtDepth (n : ℕ) : Finset Node :=
  (Finset.univ : Finset (Fin n → Bool)).image List.ofFn

@[simp] theorem mem_nodesAtDepth (v : Node) (n : ℕ) : v ∈ nodesAtDepth n ↔ v.length=n := by
  constructor
  · intro hv
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hv
    exact List.length_ofFn
  · intro hv
    subst n
    exact Finset.mem_image.mpr ⟨v.get, Finset.mem_univ _, List.ofFn_get v⟩

@[simp] theorem card_nodesAtDepth (n : ℕ) : (nodesAtDepth n).card = 2^n := by
  rw [nodesAtDepth, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

theorem Covering.exists_region_at_depth {X : Type*} (C : Covering X) (n : ℕ) (x : X) :
    ∃ v ∈ nodesAtDepth n, x ∈ C.region v := by
  induction n with
  | zero => exact ⟨[], by simp, by rw [C.root]; trivial⟩
  | succ n ih =>
    obtain ⟨v, hv, hx⟩ := ih
    rw [C.children v] at hx
    rcases hx with hx | hx
    · exact ⟨child v false, by simp [(mem_nodesAtDepth v n).mp hv], hx⟩
    · exact ⟨child v true, by simp [(mem_nodesAtDepth v n).mp hv], hx⟩

/-- Coarse-scale finite packing bound from A1 alone, valid for asymmetric
dissimilarities without a triangle inequality. -/
theorem RegularCovering.disjoint_ball_family_card_le {X I : Type*} [MeasurableSpace X]
    [Fintype I] (C : RegularCovering X) (centers : I → X) (ε : ℝ) (h : ℕ)
    (hε : C.nu1*C.rho^h < ε)
    (hd : Pairwise (fun i j => Disjoint {y | C.ell (centers i) y < ε}
      {y | C.ell (centers j) y < ε})) : Fintype.card I ≤ 2^h := by
  classical
  let g : I → {v // v ∈ nodesAtDepth h} := fun i =>
    ⟨(C.toCovering.exists_region_at_depth h (centers i)).choose,
      (C.toCovering.exists_region_at_depth h (centers i)).choose_spec.1⟩
  have hg (i : I) : centers i ∈ C.region (g i).val :=
    (C.toCovering.exists_region_at_depth h (centers i)).choose_spec.2
  have hi : Function.Injective g := by
    intro i j he
    by_contra hn
    have hp : 0 < ε := lt_of_le_of_lt (mul_nonneg C.nu1_pos.le (pow_nonneg C.rho_pos.le _)) hε
    have hj : centers j ∈ C.region (g i).val := by rw [he]; exact hg j
    have hdist := C.diameter_bound (g i).val (centers j) hj (centers i) (hg i)
    have hlen := (mem_nodesAtDepth _ h).mp (g i).property
    rw [hlen] at hdist
    exact (Set.disjoint_left.mp (hd hn))
      (by simpa only [Set.mem_setOf_eq, C.ell_self] using hp) (hdist.trans_lt hε)
  simpa only [Fintype.card_coe, card_nodesAtDepth] using Fintype.card_le_of_injective g hi

theorem RegularCovering.exists_finite_packing_bound {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ (I : Type) [Fintype I] (centers : I → X),
      Pairwise (fun i j => Disjoint {y | C.ell (centers i) y < ε}
        {y | C.ell (centers j) y < ε}) → Fintype.card I ≤ M := by
  obtain ⟨h, hh⟩ : ∃ h : ℕ, C.rho^h < ε/C.nu1 :=
    exists_pow_lt_of_lt_one (div_pos hε C.nu1_pos) C.rho_lt_one
  have he : C.nu1*C.rho^h < ε := by
    have hi := (lt_div_iff₀ C.nu1_pos).mp hh
    simpa only [mul_comm] using hi
  exact ⟨2^h, fun I _ centers hd => C.disjoint_ball_family_card_le centers ε h he hd⟩

end BanditRLProof.HOO
