import BanditRLProof.OnlineGradientDescentSource
import Tests.OnlineGradientDescentCanary
import Tests.OnlineGradientDescentVariableCanary
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Set Finset Filter
open scoped InnerProductSpace Topology
open BanditRL.OnlineGradientDescent
namespace Tests.OnlineGradientDescentSource
namespace S := BanditRL.OnlineGradientDescentSource

abbrev Plane := EuclideanSpace ℝ (Fin 2)
def e0 : Plane := EuclideanSpace.single 0 1
def e1 : Plane := EuclideanSpace.single 1 1

@[simp] theorem e00 : inner ℝ e0 e0 = 1 := by
  simp [e0, EuclideanSpace.inner_single_left]
@[simp] theorem e01 : inner ℝ e0 e1 = 0 := by
  simp [e0, e1, EuclideanSpace.inner_single_left]
@[simp] theorem e10 : inner ℝ e1 e0 = 0 := by
  simp [e0, e1, EuclideanSpace.inner_single_left]
@[simp] theorem e11 : inner ℝ e1 e1 = 1 := by
  simp [e1, EuclideanSpace.inner_single_left]
@[simp] theorem norm_e0 : ‖e0‖ = 1 := by simp [e0]

def axis : Domain Plane where
  carrier := {z | inner ℝ e1 z = 0}
  nonempty := ⟨0, by simp⟩
  closed := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      isClosed_eq (InnerProductSpace.toDual ℝ Plane e1).continuous continuous_const
  convex := by
    intro x hx y hy a b ha hb hab
    simp only [mem_setOf_eq, inner_add_right, inner_smul_right, hx, hy, mul_zero, add_zero]

def maxExp (z : Plane) : ℝ := max (Real.exp (-inner ℝ e0 z)) (inner ℝ e1 z)
def smoothRegion : Set Plane := {z | inner ℝ e1 z < Real.exp (-inner ℝ e0 z)}

theorem region_open : IsOpen smoothRegion := by
  have h0 : Continuous (fun z : Plane => inner ℝ e0 z) := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      (InnerProductSpace.toDual ℝ Plane e0).continuous
  have h1 : Continuous (fun z : Plane => inner ℝ e1 z) := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      (InnerProductSpace.toDual ℝ Plane e1).continuous
  exact isOpen_lt h1 h0.neg.exp

theorem axis_in_region : axis.carrier ⊆ smoothRegion := by
  intro z hz
  change inner ℝ e1 z < Real.exp (-inner ℝ e0 z)
  change inner ℝ e1 z = 0 at hz
  rw [hz]
  exact Real.exp_pos _

theorem maxExp_on_region (z : Plane) (hz : z ∈ smoothRegion) :
    maxExp z = Real.exp (-inner ℝ e0 z) := max_eq_left_of_lt hz

theorem maxExp_eventually (z : Plane) (hz : z ∈ smoothRegion) :
    maxExp =ᶠ[𝓝 z] (fun w => Real.exp (-inner ℝ e0 w)) := by
  filter_upwards [region_open.mem_nhds hz] with w hw
  exact maxExp_on_region w hw

/-- The source predicate has a concrete arbitrary-open witness on an unbounded feasible line. -/
theorem maxExp_source : S.SourceRegularLoss axis maxExp := by
  refine ⟨smoothRegion, region_open, axis_in_region, ?_, ?_⟩
  · have hc : ConvexOn ℝ univ (fun z : Plane => Real.exp (-inner ℝ e0 z)) := by
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
        Real.convexOn_exp.comp_linearMap (-(InnerProductSpace.toDual ℝ Plane e0).toLinearMap)
    apply (hc.subset (subset_univ _) axis.convex).congr
    intro z hz
    exact (maxExp_on_region z (axis_in_region hz)).symm
  · intro z hz
    have hd : DifferentiableAt ℝ (fun w : Plane => Real.exp (-inner ℝ e0 w)) z := by
      simpa only [InnerProductSpace.toDual_apply_apply] using
        ((InnerProductSpace.toDual ℝ Plane e0).hasFDerivAt (x := z)).neg.exp.differentiableAt
    exact (hd.congr_of_eventuallyEq (maxExp_eventually z hz)).differentiableWithinAt

/-- The supplied neighborhood is genuinely nonconvex; no alternative-neighborhood claim. -/
theorem region_not_convex : ¬ Convex ℝ smoothRegion := by
  intro h
  have ha : -e0 + (2 : ℝ) • e1 ∈ smoothRegion := by
    change inner ℝ e1 (-e0 + (2 : ℝ) • e1) <
      Real.exp (-inner ℝ e0 (-e0 + (2 : ℝ) • e1))
    simpa using Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  have hb : e0 ∈ smoothRegion := axis_in_region (by simp [axis])
  have hm := h ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he : (1 / 2 : ℝ) • (-e0 + (2 : ℝ) • e1) + (1 / 2 : ℝ) • e0 = e1 := by
    module
  rw [he] at hm
  norm_num [smoothRegion] at hm

theorem gradient_at_zero : gradient maxExp (0 : Plane) = -e0 := by
  have hd : HasGradientAt (fun z : Plane => Real.exp (-inner ℝ e0 z)) (-e0) 0 := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa using ((InnerProductSpace.toDual ℝ Plane e0).hasFDerivAt (x := 0)).neg.exp
  exact (hd.congr_of_eventuallyEq
    (maxExp_eventually 0 (axis_in_region (by simp [axis])))).gradient

theorem project_e0 : project axis e0 = e0 := by
  apply project_eq_of_variational axis e0 e0 (by simp [axis])
  intro w hw
  simp

theorem axis_first_point : iterate axis 1 (fun _ => maxExp) 0 1 = e0 := by
  simp [iterate, step, gradient_at_zero, project_e0]

theorem maxExp_zero : maxExp (0 : Plane) = 1 := by simp [maxExp]
theorem maxExp_two : maxExp ((2 : ℝ) • e0) = Real.exp (-2) := by
  simp [maxExp, inner_smul_right, le_of_lt (Real.exp_pos (-2))]

theorem positive_regret :
    0 < regret axis 1 (fun _ => maxExp) 0 ((2 : ℝ) • e0) 1 := by
  have he : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  simpa [regret, iterate, maxExp_zero, maxExp_two] using sub_pos.mpr he

theorem terminal_distance :
    ‖iterate axis 1 (fun _ => maxExp) 0 1 - (2 : ℝ) • e0‖ ^ 2 = 1 := by
  rw [axis_first_point]
  have he : e0 - (2 : ℝ) • e0 = -e0 := by module
  rw [he]
  simp

/-- An actual nonzero gradient generates a distinct next play and positive regret/residual. -/
theorem source_nondegenerate : gradient maxExp (0 : Plane) = -e0 ∧
    ‖gradient maxExp (0 : Plane)‖ = 1 ∧
    iterate axis 1 (fun _ => maxExp) 0 1 = e0 ∧
    0 < regret axis 1 (fun _ => maxExp) 0 ((2 : ℝ) • e0) 1 ∧
    ‖iterate axis 1 (fun _ => maxExp) 0 1 - (2 : ℝ) • e0‖ ^ 2 = 1 := by
  exact ⟨gradient_at_zero, by rw [gradient_at_zero]; simp,
    axis_first_point, positive_regret, terminal_distance⟩

/-- Both comparisons are instantiated through the proved source adapter on this same loss/update. -/
theorem repaired_one_step :
    1 * (maxExp 0 - maxExp ((2 : ℝ) • e0)) ≤
      1 * inner ℝ (gradient maxExp 0) (0 - (2 : ℝ) • e0) ∧
    1 * inner ℝ (gradient maxExp 0) (0 - (2 : ℝ) • e0) ≤
      ‖(0 : Plane) - (2 : ℝ) • e0‖ ^ 2 / 2 -
        ‖step axis 1 maxExp 0 - (2 : ℝ) • e0‖ ^ 2 / 2 +
        1 ^ 2 / 2 * ‖gradient maxExp 0‖ ^ 2 :=
  S.lemma_2_12 axis maxExp (S.source_to_feasible axis maxExp maxExp_source)
    1 (by norm_num) 0 ((2 : ℝ) • e0) (by simp [axis]) (by simp [axis])

theorem repaired_fixed_endpoint :
    regret axis 1 (fun _ => maxExp) 0 ((2 : ℝ) • e0) 1 ≤
      ‖(0 : Plane) - (2 : ℝ) • e0‖ ^ 2 / (2 * 1) +
        1 / 2 * (∑ t ∈ range 1,
          ‖gradient maxExp (iterate axis 1 (fun _ => maxExp) 0 t)‖ ^ 2) -
        ‖iterate axis 1 (fun _ => maxExp) 0 1 - (2 : ℝ) • e0‖ ^ 2 / (2 * 1) :=
  S.theorem_2_13_fixed axis 1 (by norm_num) (fun _ => maxExp) 0 (by simp [axis]) 1
    (fun _ _ => S.source_to_feasible axis maxExp maxExp_source) ((2 : ℝ) • e0)
    (by simp [axis])

end Tests.OnlineGradientDescentSource
