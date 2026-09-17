import BanditRLProof.HOOOptimalBranch
import BanditRLProof.Algorithms.HOOPrefix

/-! Actual HOO search-path comparison with a supremum-preserving branch. -/
namespace BanditRLProof.HOO

theorem Covering.branch_root_optimistic {X : Type*} (C : Covering X) (f : X → ℝ)
    (S : Finset Node) (U : Node → WithTop ℝ) (best : ℝ) (k : ℕ)
    (hk : C.optimalPath f k ∉ S)
    (hpre : ∀ j < k, C.optimalPath f j ∈ S)
    (hU : ∀ j < k, (best : WithTop ℝ) ≤ U (C.optimalPath f j)) :
    (best : WithTop ℝ) ≤ bValue S U [] := by
  have hrec : ∀ r j : ℕ, j+r=k → (best : WithTop ℝ) ≤ bValue S U (C.optimalPath f j) := by
    intro r
    induction r with
    | zero =>
      intro j hj
      have he : j=k := by omega
      rw [he, bValue_not_mem S U _ hk]
      exact le_top
    | succ r ih =>
      intro j hj
      have hjk : j < k := by omega
      have hh := ih (j+1) (by omega)
      rw [Covering.optimalPath] at hh
      rw [bValue_eq S U _ (hpre j hjk)]
      apply le_min (hU j hjk)
      cases hc : C.optimalChild f (C.optimalPath f j)
      · rw [hc] at hh
        exact hh.trans (le_max_left _ _)
      · rw [hc] at hh
        exact hh.trans (le_max_right _ _)
  exact hrec k 0 (by omega)

/-- If an expanded region lies on the actual selected path but has U below
`best`, some node of the comparison branch has U below `best`. The branch
need only be inspected through the finite tree's maximum depth. -/
theorem Covering.selected_underestimate_implies_branch_underestimate {X : Type*}
    (C : Covering X) (f : X → ℝ) (S : Finset Node) (U : Node → WithTop ℝ)
    (best : ℝ) (v : Node) (hv : v ∈ S) (hpath : v <+: select S U)
    (hU : U v < (best : WithTop ℝ)) :
    ∃ j ≤ depthBound S, U (C.optimalPath f j) < (best : WithTop ℝ) := by
  by_contra hn
  push_neg at hn
  obtain ⟨k, hk, hmissing, hpre⟩ := C.exists_first_unexpanded f S
  have hb := C.branch_root_optimistic f S U best k hmissing hpre
    (fun j hj => hn j (by omega))
  have hp : bValue S U [] ≤ bValue S U v :=
    bValue_le_prefix_walk S U (depthBound S+1) [] v List.nil_prefix hpath
  exact (not_lt_of_ge (hb.trans (hp.trans (bValue_le_upper S U v hv)))) hU

/-- The same comparison stated directly on the generated chronological state. -/
theorem Covering.history_selected_underestimate {X : Type*} (C : Covering X) (f : X → ℝ)
    (ν ρ best : ℝ) (Y : ℕ → ℝ) (n : ℕ) (v : Node)
    (hv : v ∈ expanded (history ν ρ Y n)) (hpath : v <+: action ν ρ Y n)
    (hu : upper ν ρ (history ν ρ Y n) v < (best : WithTop ℝ)) :
    ∃ j ≤ n, upper ν ρ (history ν ρ Y n) (C.optimalPath f j) < (best : WithTop ℝ) := by
  obtain ⟨j, hj, huj⟩ := C.selected_underestimate_implies_branch_underestimate f
    (expanded (history ν ρ Y n)) (upper ν ρ (history ν ρ Y n)) best v hv hpath hu
  exact ⟨j, hj.trans (depthBound_history ν ρ Y n), huj⟩

end BanditRLProof.HOO
