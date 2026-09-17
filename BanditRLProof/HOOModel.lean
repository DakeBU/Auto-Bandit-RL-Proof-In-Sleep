import BanditRLProof.HOOGeometry
import BanditRLProof.Algorithms.HOOTrajectory

/-! Source tree-of-coverings assumptions and the actual arm/reward realization.
The infinite arm space is not replaced by a finite discretization. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory

structure Covering (X : Type*) where
  region : Node → Set X
  root : region [] = Set.univ
  children : ∀ v, region v = region (child v false) ∪ region (child v true)
  nonempty : ∀ v, (region v).Nonempty

theorem Covering.child_subset {X : Type*} (C : Covering X) (v : Node) (b : Bool) :
    C.region (child v b) ⊆ C.region v := by
  rw [C.children v]
  cases b
  · exact Set.subset_union_left
  · exact Set.subset_union_right

theorem Covering.append_subset {X : Type*} (C : Covering X) (v u : Node) :
    C.region (v ++ u) ⊆ C.region v := by
  induction u generalizing v with
  | nil => simp
  | cons b u ih =>
    have h := (ih (child v b)).trans (C.child_subset v b)
    simpa only [child, List.append_assoc, List.singleton_append] using h

theorem Covering.descendant_subset {X : Type*} (C : Covering X) {v w : Node}
    (h : v <+: w) : C.region w ⊆ C.region v := by
  obtain ⟨u, rfl⟩ := h
  exact C.append_subset v u

noncomputable def Covering.representative {X : Type*} (C : Covering X) (v : Node) : X :=
  (C.nonempty v).choose

theorem Covering.representative_mem {X : Type*} (C : Covering X) (v : Node) :
    C.representative v ∈ C.region v := (C.nonempty v).choose_spec

/-- A1, stated with pointwise diameter bounds equivalent to the source bound.
Inner balls need not be metric balls: asymmetry and lack of triangle inequality
are retained. -/
structure RegularCovering (X : Type*) [MeasurableSpace X] extends Covering X where
  measurable_region : ∀ v, MeasurableSet (region v)
  ell : X → X → ℝ
  ell_nonneg : ∀ x y, 0 ≤ ell x y
  ell_self : ∀ x, ell x x = 0
  nu1 : ℝ
  nu2 : ℝ
  rho : ℝ
  nu1_pos : 0 < nu1
  nu2_pos : 0 < nu2
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  diameter_bound : ∀ v, ∀ x ∈ region v, ∀ y ∈ region v, ell x y ≤ nu1*rho^v.length
  center : Node → X
  center_mem : ∀ v, center v ∈ region v
  ball_subset : ∀ v, {y | ell (center v) y < nu2*rho^v.length} ⊆ region v
  balls_disjoint : ∀ v w, v.length = w.length → v ≠ w →
    Disjoint {y | ell (center v) y < nu2*rho^v.length}
      {y | ell (center w) y < nu2*rho^w.length}

theorem RegularCovering.region_near_optimal {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best c : ℝ) (v : Node)
    (hw : WeaklyLipschitz f C.ell best)
    (hgap : best - regionSup f (C.region v) ≤ c*(C.nu1*C.rho^v.length))
    (y : X) (hy : y ∈ C.region v) :
    best - f y ≤ max (2*c) (c+1)*(C.nu1*C.rho^v.length) :=
  near_optimal_region f C.ell best _ c _ (C.nonempty v)
    (mul_nonneg C.nu1_pos.le (pow_nonneg C.rho_pos.le _)) hw
    (C.diameter_bound v) hgap y hy

/-- Fixed representatives are allowed by source Algorithm 1. Their countable
domain makes the arm-to-law map measurable without requiring a continuous
selector on the entire arm space. -/
noncomputable def Covering.nodeLaw {X : Type*} [MeasurableSpace X]
    (C : Covering X) (law : Kernel X ℝ) : Kernel Node ℝ :=
  law.comap C.representative (measurable_of_countable _)

instance Covering.nodeLaw_markov {X : Type*} [MeasurableSpace X]
    (C : Covering X) (law : Kernel X ℝ) [IsMarkovKernel law] :
    IsMarkovKernel (C.nodeLaw law) := by unfold Covering.nodeLaw; infer_instance

noncomputable def Covering.arm {X : Type*} (C : Covering X)
    (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) : X := C.representative (action ν ρ Y n)

theorem Covering.arm_mem {X : Type*} (C : Covering X)
    (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) : C.arm ν ρ Y n ∈ C.region (action ν ρ Y n) :=
  C.representative_mem _

theorem Covering.measurable_arm {X : Type*} [MeasurableSpace X] (C : Covering X)
    (ν ρ : ℝ) (n : ℕ) : Measurable (fun Y => C.arm ν ρ Y n) :=
  (measurable_of_countable C.representative).comp (measurable_action ν ρ n)

theorem Covering.stepKernel_actual_arm {X : Type*} [MeasurableSpace X] (C : Covering X)
    (law : Kernel X ℝ) (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    stepKernel ν ρ (C.nodeLaw law) n (Preorder.frestrictLe n Y) =
      law (C.arm ν ρ Y (n+1)) := by
  rw [stepKernel_apply_prefix]
  rfl

end BanditRLProof.HOO
