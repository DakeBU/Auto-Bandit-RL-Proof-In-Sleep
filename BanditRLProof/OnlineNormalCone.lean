/-
Orabona v10 Example2.25 printed18/PDF30: ONE body example, THREE exact
normal-cone equalities and ONE complete retained owned definition.
Zero new mathematical or TEST declarations. The full feasible definition
requires x in V and every feasible displacement inner product nonpositive;
it has intrinsic real inner-product context, no finite-dimensional,
nonempty or convexity premise. All THREE theorem signatures explicitly
retain finite-dimensional real inner-product space; first TWO retain
nonempty convex V. No general closed or bounded V, relative interior,
positive dimension or extra completeness premise is introduced.
Generic shared support accepts wider EReal inputs than printed proper
functions. Nonempty V makes the zero/top constraint indicator proper.
Empty V is excluded: generic support of all-top differs from empty normals.
Actual support/properness derives query feasibility and outside emptiness.
Actual ambient interior ball and a positive displacement along nonzero g
force a contradiction; zero satisfies the full feasible inequalities.
Actual normalized nonzero g, Cauchy equality and zero squared difference
produce every closed-unit-ball boundary normal's nonnegative radial form;
zero uses scalar0 and converse covers ALL real scalars at least0.
Whole FOUR old canary proofs and TWO real2D basis definitions unchanged.
The singleton canary proves full support/7, not empty interior itself.
Two-dimensional canary includes outward2e0 and zero, excludes e1 and -e0.
Borrowed support/indicator/proper/domain APIs are shared, not owned/new.
ONE owned definition plus three retained proof refinements is reuse, not
new mathematical growth or a separate coordinate isometry certificate.
Next Theorem2.26 and all remaining Chapter1/2/appendix work required;
Chapter2 and persistent Chapters1-16 Goal remain incomplete.
-/
import BanditRLProof.OnlineSubgradientBasic

/-!
# Indicator supports and normal cones
Orabona, Online Learning: A Modern Introduction Using Convex Optimization,
arXiv:1912.13213v10, Example 2.25, printed page 18 / PDF page 30.
All three source claims are retained: the full indicator subdifferential equals
the normal cone, interior normals are exactly zero, and closed-unit-ball boundary
normals form the entire nonnegative radial ray. The definition explicitly
requires the query point to lie in the set, so it is empty outside the domain.
Source nonempty/convex and finite-dimensional premises remain explicit even
where direct inequality arguments prove stronger internal facts. No general
closedness or boundedness premise is added. This is not Chapter 2/book completion.
-/

noncomputable section
open Set
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Feasible query and all feasible displacement inner products nonpositive. -/
def SourceNormalCone (V : Set E) (x : E) : Set E :=
  {g | x ∈ V ∧ ∀ y ∈ V, inner ℝ g (y - x) ≤ 0}

theorem indicator_subdifferential_eq_normalCone [FiniteDimensional ℝ E]
    (V : Set E) (hVn : V.Nonempty) (hVc : Convex ℝ V) (x : E) :
    SourceSubdifferential (extendedIndicator V) x = SourceNormalCone V x := by
  classical
  ext g
  constructor
  · intro hg
    have hf : SourceProper (extendedIndicator V) := (sourceProper_indicator_iff V).mpr hVn
    have hxV : x ∈ V := by
      simpa only [effectiveDomain_indicator] using
        subgradient_point_finite (extendedIndicator V) hf x g hg
    refine ⟨hxV, ?_⟩
    intro y hy
    have h := hg y
    simpa [extendedIndicator, hxV, hy] using h
  · intro hg y
    by_cases hy : y ∈ V
    · have h := EReal.coe_le_coe_iff.mpr (hg.2 y hy)
      simpa [extendedIndicator, hg.1, hy] using h
    · simp [extendedIndicator, hg.1, hy]


theorem normalCone_interior_eq_zero [FiniteDimensional ℝ E]
    (V : Set E) (hVn : V.Nonempty) (hVc : Convex ℝ V)
    (x : E) (hx : x ∈ interior V) : SourceNormalCone V x = {(0 : E)} := by
  classical
  ext g
  change g ∈ SourceNormalCone V x ↔ g = 0
  constructor
  · intro hg
    by_contra hg0
    have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg0
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    let a : ℝ := r / (2 * ‖g‖)
    have ha : 0 < a := div_pos hr (by positivity)
    have hnorm : ‖a • g‖ = r / 2 := by
      rw [norm_smul_of_nonneg ha.le]
      dsimp [a]
      field_simp [ne_of_gt hgn]
    have hy : x + a • g ∈ V := hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, hnorm]
      linarith)
    have h := hg.2 (x + a • g) hy
    simp only [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
    have hp : 0 < a * ‖g‖ ^ 2 := mul_pos ha (sq_pos_of_pos hgn)
    linarith
  · intro hg
    subst g
    refine ⟨interior_subset hx, ?_⟩
    intro y hy
    simp


theorem normalCone_unitBall_boundary [FiniteDimensional ℝ E]
    (x : E) (hx : ‖x‖ = 1) :
    SourceNormalCone {y : E | ‖y‖ ≤ 1} x =
      {g | ∃ α : ℝ, 0 ≤ α ∧ g = α • x} := by
  classical
  ext g
  constructor
  · intro hg
    by_cases hg0 : g = 0
    · subst g
      exact ⟨0, le_rfl, by simp⟩
    have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg0
    have hy : ‖(‖g‖⁻¹ : ℝ) • g‖ ≤ 1 := by
      simpa using (norm_smul_inv_norm (𝕜 := ℝ) hg0).le
    have h := hg.2 ((‖g‖⁻¹ : ℝ) • g) hy
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
    have hn : ‖g‖⁻¹ * ‖g‖ ^ 2 = ‖g‖ := by
      field_simp [ne_of_gt hgn]
    rw [hn] at h
    have hcs := real_inner_le_norm g x
    rw [hx, mul_one] at hcs
    have he : inner ℝ g x = ‖g‖ := by linarith
    refine ⟨‖g‖, norm_nonneg g, ?_⟩
    have hsq : ‖g - ‖g‖ • x‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, norm_smul_of_nonneg (norm_nonneg g),
        real_inner_smul_right, he, hx]
      ring
    have hn0 : ‖g - ‖g‖ • x‖ = 0 := by
      nlinarith [norm_nonneg (g - ‖g‖ • x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn0)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨hx.le, ?_⟩
    intro y hy
    change ‖y‖ ≤ 1 at hy
    rw [real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq, hx]
    have hcs := real_inner_le_norm x y
    rw [hx, one_mul] at hcs
    exact mul_nonpos_of_nonneg_of_nonpos ha (by nlinarith)

end BanditRL.OnlineConvex
