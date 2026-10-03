import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Infix
import Mathlib.Data.Real.Basic
import Mathlib.Order.WithBot
import Mathlib.Tactic

/-! Finite implementation of the infinite HOO binary-tree search. Fuel is an
implementation device; the depth proofs show it cannot truncate the search. -/
namespace BanditRLProof.HOO

abbrev Node := List Bool

def child (v : Node) (b : Bool) : Node := v ++ [b]

@[simp] theorem child_length (v : Node) (b : Bool) :
    (child v b).length = v.length + 1 := by simp [child]

theorem prefix_child (v : Node) (b : Bool) : v <+: child v b :=
  List.prefix_append _ _

def depthBound (S : Finset Node) : ℕ := S.sup List.length

theorem length_le_depthBound {S : Finset Node} {v : Node} (hv : v ∈ S) :
    v.length ≤ depthBound S := Finset.le_sup hv

theorem not_mem_of_depth_lt {S : Finset Node} {v : Node}
    (hv : depthBound S < v.length) : v ∉ S := by
  intro h
  exact (not_lt_of_ge (length_le_depthBound h)) hv

/-- Unexpanded nodes have infinity; expanded nodes use the source min/max rule. -/
noncomputable def backward (S : Finset Node) (U : Node → WithTop ℝ) :
    ℕ → Node → WithTop ℝ
  | 0, _ => ⊤
  | k+1, v => if v ∈ S then min (U v)
      (max (backward S U k (child v false)) (backward S U k (child v true))) else ⊤

theorem backward_not_mem (S : Finset Node) (U : Node → WithTop ℝ)
    (k : ℕ) (v : Node) (hv : v ∉ S) : backward S U k v = ⊤ := by
  cases k <;> simp [backward, hv]

/-- Increasing already sufficient fuel has no effect on B. -/
theorem backward_stable_succ (S : Finset Node) (U : Node → WithTop ℝ)
    (k : ℕ) (v : Node) (hk : depthBound S < v.length + k) :
    backward S U (k+1) v = backward S U k v := by
  induction k generalizing v with
  | zero =>
    have hv : v ∉ S := not_mem_of_depth_lt (by simpa using hk)
    simp [backward, hv]
  | succ k ih =>
    by_cases hv : v ∈ S
    · change (if v ∈ S then min (U v)
        (max (backward S U (k+1) (child v false)) (backward S U (k+1) (child v true))) else ⊤) =
        (if v ∈ S then min (U v)
        (max (backward S U k (child v false)) (backward S U k (child v true))) else ⊤)
      rw [if_pos hv, if_pos hv]
      rw [ih (child v false) (by simp only [child_length]; omega),
        ih (child v true) (by simp only [child_length]; omega)]
    · simp [backward, hv]

noncomputable def bValue (S : Finset Node) (U : Node → WithTop ℝ) (v : Node) :
    WithTop ℝ := backward S U (depthBound S + 1) v

theorem bValue_not_mem (S : Finset Node) (U : Node → WithTop ℝ)
    (v : Node) (hv : v ∉ S) : bValue S U v = ⊤ :=
  backward_not_mem S U _ v hv

/-- The actual finite computation satisfies the exact recursive B equation. -/
theorem bValue_eq (S : Finset Node) (U : Node → WithTop ℝ)
    (v : Node) (hv : v ∈ S) :
    bValue S U v = min (U v)
      (max (bValue S U (child v false)) (bValue S U (child v true))) := by
  unfold bValue
  conv_rhs =>
    rw [backward_stable_succ S U (depthBound S) (child v false)
      (by simp only [child_length]; omega),
      backward_stable_succ S U (depthBound S) (child v true)
      (by simp only [child_length]; omega)]
  simp only [backward, if_pos hv]

noncomputable def preferred (B : Node → WithTop ℝ) (v : Node) : Bool :=
  if B (child v true) ≤ B (child v false) then false else true

theorem preferred_max (B : Node → WithTop ℝ) (v : Node) :
    B (child v (preferred B v)) = max (B (child v false)) (B (child v true)) := by
  unfold preferred
  split
  · exact (max_eq_left ‹_›).symm
  · exact (max_eq_right (le_of_not_ge ‹_›)).symm

noncomputable def walk (S : Finset Node) (B : Node → WithTop ℝ) : ℕ → Node → Node
  | 0, v => v
  | k+1, v => if v ∈ S then walk S B k (child v (preferred B v)) else v

theorem walk_not_mem (S : Finset Node) (B : Node → WithTop ℝ)
    (k : ℕ) (v : Node) (hk : depthBound S < v.length + k) : walk S B k v ∉ S := by
  induction k generalizing v with
  | zero => exact not_mem_of_depth_lt (by simpa using hk)
  | succ k ih =>
    by_cases hv : v ∈ S
    · simp only [walk, if_pos hv]
      exact ih _ (by simp only [child_length]; omega)
    · simpa [walk, hv] using hv

theorem prefix_walk (S : Finset Node) (B : Node → WithTop ℝ) (k : ℕ) (v : Node) :
    v <+: walk S B k v := by
  induction k generalizing v with
  | zero => exact List.prefix_refl _
  | succ k ih =>
    by_cases hv : v ∈ S
    · simp only [walk, if_pos hv]
      exact (prefix_child v _).trans (ih _)
    · simpa [walk, hv] using List.prefix_refl v

theorem walk_length_le (S : Finset Node) (B : Node → WithTop ℝ) (k : ℕ) (v : Node) :
    (walk S B k v).length ≤ v.length + k := by
  induction k generalizing v with
  | zero => simp [walk]
  | succ k ih =>
    by_cases hv : v ∈ S
    · simp only [walk, if_pos hv]
      have h := ih (child v (preferred B v))
      simp only [child_length] at h
      omega
    · simp [walk, hv]

noncomputable def select (S : Finset Node) (U : Node → WithTop ℝ) : Node :=
  walk S (bValue S U) (depthBound S + 1) []

theorem select_not_mem (S : Finset Node) (U : Node → WithTop ℝ) : select S U ∉ S :=
  walk_not_mem S _ _ [] (by simp)

theorem select_length_le (S : Finset Node) (U : Node → WithTop ℝ) :
    (select S U).length ≤ depthBound S + 1 := by
  simpa only [List.length_nil, zero_add] using walk_length_le S (bValue S U) (depthBound S+1) []

/-- The recursive optimistic value cannot decrease along the selected path. -/
theorem bValue_le_walk (S : Finset Node) (U : Node → WithTop ℝ)
    (k : ℕ) (v : Node) : bValue S U v ≤ bValue S U (walk S (bValue S U) k v) := by
  induction k generalizing v with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hv : v ∈ S
    · change bValue S U v ≤ bValue S U
        (if v ∈ S then walk S (bValue S U) k (child v (preferred (bValue S U) v)) else v)
      rw [if_pos hv]
      apply LE.le.trans _ (ih _)
      rw [preferred_max (bValue S U) v, bValue_eq S U v hv]
      exact min_le_right _ _
    · simp [walk, hv]

end BanditRLProof.HOO
