import BanditRLProof.HOOModel

/-! A deterministic branch preserving regional suprema. No maximizer or
attainment of any regional supremum is assumed. -/
namespace BanditRLProof.HOO

theorem Covering.regionSup_children {X : Type*} (C : Covering X)
    (f : X → ℝ) (best : ℝ) (hf : ∀ x, f x ≤ best) (v : Node) :
    regionSup f (C.region v) =
      max (regionSup f (C.region (child v false))) (regionSup f (C.region (child v true))) := by
  have hb (w : Node) : BddAbove (f '' C.region w) := ⟨best, by
    rintro y ⟨x, _, rfl⟩; exact hf x⟩
  unfold regionSup
  rw [C.children v, Set.image_union]
  exact csSup_union (hb _) ((C.nonempty _).image f) (hb _) ((C.nonempty _).image f)

noncomputable def Covering.optimalChild {X : Type*} (C : Covering X) (f : X → ℝ) (v : Node) : Bool :=
  if regionSup f (C.region (child v true)) ≤ regionSup f (C.region (child v false))
  then false else true

theorem Covering.optimalChild_sup {X : Type*} (C : Covering X)
    (f : X → ℝ) (best : ℝ) (hf : ∀ x, f x ≤ best) (v : Node) :
    regionSup f (C.region (child v (C.optimalChild f v))) = regionSup f (C.region v) := by
  rw [C.regionSup_children f best hf v]
  unfold Covering.optimalChild
  split_ifs with h
  · exact (max_eq_left h).symm
  · exact (max_eq_right (le_of_not_ge h)).symm

noncomputable def Covering.optimalPath {X : Type*} (C : Covering X) (f : X → ℝ) : ℕ → Node
  | 0 => []
  | n+1 => child (C.optimalPath f n) (C.optimalChild f (C.optimalPath f n))

@[simp] theorem Covering.optimalPath_length {X : Type*} (C : Covering X) (f : X → ℝ) (n : ℕ) :
    (C.optimalPath f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [optimalPath, child_length, ih]

theorem Covering.optimalPath_sup {X : Type*} (C : Covering X)
    (f : X → ℝ) (best : ℝ) (hf : ∀ x, f x ≤ best) (n : ℕ) :
    regionSup f (C.region (C.optimalPath f n)) = regionSup f Set.univ := by
  induction n with
  | zero => simp only [optimalPath, C.root]
  | succ n ih => rw [optimalPath, C.optimalChild_sup f best hf, ih]

theorem Covering.optimalPath_prefix {X : Type*} (C : Covering X) (f : X → ℝ)
    {i j : ℕ} (hij : i ≤ j) : C.optimalPath f i <+: C.optimalPath f j := by
  induction j, hij using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ j _ ih => exact ih.trans (prefix_child _ _)

/-- Every finite expanded tree has a first missing node on this infinite
branch, bounded by its maximum depth plus one. -/
theorem Covering.exists_first_unexpanded {X : Type*} (C : Covering X)
    (f : X → ℝ) (S : Finset Node) :
    ∃ k ≤ depthBound S + 1, C.optimalPath f k ∉ S ∧
      ∀ j < k, C.optimalPath f j ∈ S := by
  have hex : ∃ k, C.optimalPath f k ∉ S := by
    refine ⟨depthBound S+1, ?_⟩
    apply not_mem_of_depth_lt
    simp only [C.optimalPath_length]
    omega
  refine ⟨Nat.find hex, Nat.find_le ?_, Nat.find_spec hex, ?_⟩
  · apply not_mem_of_depth_lt
    simp only [C.optimalPath_length]
    omega
  · intro j hj
    by_contra hnot
    exact (Nat.find_min hex hj) hnot

end BanditRLProof.HOO
