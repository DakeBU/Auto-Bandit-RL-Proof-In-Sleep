import StrongConvexAttainmentCandidate

noncomputable section
open Set
namespace BanditRL.Tests.OnlineStrongConvexAttainmentCanary
open BanditRL.OnlineConvex

abbrev E := EuclideanSpace ℝ (Fin 1)
def coordinates : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1) := LinearEquiv.refl ℝ E
def point (t : ℝ) : E := EuclideanSpace.single 0 t

def quadratic (x : E) : EReal :=
  if 0 ≤ x 0 then (((x 0 - 2) ^ 2 / 2 : ℝ) : EReal) else ⊤
def affine (x : E) : EReal := (x 0 : EReal)

theorem halfline_quadratic_unique_attainment :
    (∃! p : E, p ∈ effectiveDomain quadratic ∧ ∀ q : E, quadratic p ≤ quadratic q) ∧
    (∀ p : E, (p ∈ effectiveDomain quadratic ∧ ∀ q : E, quadratic p ≤ quadratic q) ↔
      p = point 2) ∧
    point (-2) ∈ SourceSubdifferential quadratic (point 0) ∧
    ¬ IsMinOn quadratic Set.univ (point 0) ∧
    (∀ R : ℝ, ∃ x : E, x ∈ effectiveDomain quadratic ∧ R < ‖x‖) ∧
    effectiveDomain quadratic = {x : E | 0 ≤ x 0} ∧
    quadratic (point 2) = (0 : EReal) ∧
    quadratic (point (-1)) = ⊤ := by
  have hpoint (t : ℝ) : (point t) 0 = t := by
    simp [point, EuclideanSpace.single_apply]
  have hcoord : Continuous (fun x : E => x 0) := PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0
  have hnorm (x : E) : ‖x‖ ^ 2 = (x 0) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_one]
  have hdomain : effectiveDomain quadratic = {x : E | 0 ≤ x 0} := by
    ext x
    by_cases hx : 0 ≤ x 0 <;> simp [effectiveDomain, quadratic, hx]
  have hfin (x : E) (hx : 0 ≤ x 0) :
      quadratic x = (((x 0 - 2) ^ 2 / 2 : ℝ) : EReal) := by
    simp [quadratic, hx]
  have hproper : SourceProper quadratic := by
    constructor
    · intro x
      by_cases hx : 0 ≤ x 0 <;> simp [quadratic, hx]
    · exact ⟨point 0, 2, by norm_num [quadratic, hpoint]⟩
  have hclosed : SourceClosed quadratic := by
    intro r
    have hcut : {x : E | quadratic x ≤ (r : EReal)} =
        {x : E | 0 ≤ x 0} ∩ {x : E | (x 0 - 2) ^ 2 / 2 ≤ r} := by
      ext x
      by_cases hx : 0 ≤ x 0 <;> simp [quadratic, hx, EReal.coe_le_coe_iff]
    rw [hcut]
    exact (isClosed_le continuous_const hcoord).inter
      (isClosed_le (((hcoord.sub continuous_const).pow 2).div_const 2) continuous_const)
  have hstrong : ∀ x ∈ effectiveDomain quadratic, ∀ y ∈ effectiveDomain quadratic,
      ∀ a : ℝ, 0 < a → a < 1 →
      quadratic (a • x + (1 - a) • y) ≤
        (a : EReal) * quadratic x + ((1 - a : ℝ) : EReal) * quadratic y -
          ((((1 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    rw [hdomain] at hx hy
    have hm : 0 ≤ (a • x + (1 - a) • y) 0 := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha.le hx) (mul_nonneg (by linarith) hy)
    rw [hfin x hx, hfin y hy, hfin _ hm]
    simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    rw [hnorm (x - y)]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    exact le_of_eq (by ring)
  have hpair (y : E) : inner ℝ (point (-2)) (y - point 0) = -2 * y 0 := by
    simp [point, PiLp.inner_apply, Fin.sum_univ_one, RCLike.inner_apply,
      PiLp.sub_apply, EuclideanSpace.single_apply]
    change (y 0) * (2 : ℝ) = 2 * y 0
    ring
  have hsupport : point (-2) ∈ SourceSubdifferential quadratic (point 0) := by
    intro y
    have hf0 : quadratic (point 0) = ((2 : ℝ) : EReal) := by
      norm_num [quadratic, hpoint]
    rw [hf0, hpair]
    by_cases hy : 0 ≤ y 0
    · rw [hfin y hy]
      have hr : 2 + (-2 * y 0) ≤ (y 0 - 2) ^ 2 / 2 := by
        nlinarith [sq_nonneg (y 0)]
      simpa only [EReal.coe_add] using (EReal.coe_le_coe_iff.mpr hr)
    · simp [quadratic, hy]
  have hsub : {p : E |
      (SourceSubdifferential (fun u => quadratic (coordinates.symm u))
        (coordinates p)).Nonempty}.Nonempty := by
    refine ⟨point 0, point (-2), ?_⟩
    simpa only [coordinates, LinearEquiv.refl_symm, LinearEquiv.refl_apply] using hsupport
  have hattainment := stronglyConvex_existsUnique_minimizer 1 coordinates quadratic 1
    hproper hclosed (by norm_num) hstrong hsub
  have hf2 : quadratic (point 2) = (0 : EReal) := by
    norm_num [quadratic, hpoint]
  have hmin2 : point 2 ∈ effectiveDomain quadratic ∧
      ∀ q : E, quadratic (point 2) ≤ quadratic q := by
    constructor
    · rw [hdomain]
      simp only [mem_setOf_eq, hpoint]
      norm_num
    · intro q
      rw [hf2]
      by_cases hq : 0 ≤ q 0
      · rw [hfin q hq]
        exact EReal.coe_le_coe_iff.mpr (div_nonneg (sq_nonneg (q 0 - 2)) (by norm_num : (0 : ℝ) ≤ 2))
      · simp [quadratic, hq]
  have hcharacterization : ∀ p : E,
      (p ∈ effectiveDomain quadratic ∧ ∀ q : E, quadratic p ≤ quadratic q) ↔
        p = point 2 := by
    intro p
    constructor
    · rintro ⟨hp, hmin⟩
      have hp0 : 0 ≤ p 0 := by simpa only [hdomain, mem_setOf_eq] using hp
      have hle := hmin (point 2)
      rw [hfin p hp0, hf2] at hle
      have hr : (p 0 - 2) ^ 2 / 2 ≤ 0 := EReal.coe_le_coe_iff.mp hle
      have hp2 : p 0 = 2 := by nlinarith [sq_nonneg (p 0 - 2)]
      ext i
      fin_cases i
      simpa only [hpoint] using hp2
    · rintro rfl
      exact hmin2
  have hnonmin : ¬ IsMinOn quadratic Set.univ (point 0) := by
    intro hm
    have hbad := hm (show point 2 ∈ Set.univ from Set.mem_univ _)
    norm_num [quadratic, hpoint] at hbad
  have hunbounded : ∀ R : ℝ, ∃ x : E,
      x ∈ effectiveDomain quadratic ∧ R < ‖x‖ := by
    intro R
    refine ⟨point (|R| + 3), ?_, ?_⟩
    · rw [hdomain]
      simp only [mem_setOf_eq, hpoint]
      positivity
    · have hp : 0 ≤ |R| + 3 := by positivity
      have hn : ‖point (|R| + 3)‖ = |R| + 3 := by
        simpa only [point, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_nonneg hp]
      rw [hn]
      linarith [le_abs_self R]
  exact ⟨hattainment, hcharacterization, hsupport, hnonmin, hunbounded, hdomain,
    hf2, by norm_num [quadratic, hpoint]⟩

theorem zero_curvature_affine_has_no_minimum :
    SourceProper affine ∧ SourceClosed affine ∧
    (∀ x ∈ effectiveDomain affine, ∀ y ∈ effectiveDomain affine,
      ∀ a : ℝ, 0 < a → a < 1 →
      affine (a • x + (1 - a) • y) ≤
        (a : EReal) * affine x + ((1 - a : ℝ) : EReal) * affine y -
          ((((0 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ∧
    point 1 ∈ SourceSubdifferential affine (point 0) ∧
    ¬ (∃ p : E, ∀ q : E, affine p ≤ affine q) := by
  have hpoint (t : ℝ) : (point t) 0 = t := by
    simp [point, EuclideanSpace.single_apply]
  have hcoord : Continuous (fun x : E => x 0) := PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0
  have hproper : SourceProper affine := by
    refine ⟨?_, point 0, 0, ?_⟩
    · intro x
      simp [affine]
    · simp [affine, hpoint]
  have hclosed : SourceClosed affine := by
    intro r
    have hcut : {x : E | affine x ≤ (r : EReal)} = {x : E | x 0 ≤ r} := by
      ext x
      simp [affine, EReal.coe_le_coe_iff]
    rw [hcut]
    exact isClosed_le hcoord continuous_const
  have hstrong : ∀ x ∈ effectiveDomain affine, ∀ y ∈ effectiveDomain affine,
      ∀ a : ℝ, 0 < a → a < 1 →
      affine (a • x + (1 - a) • y) ≤
        (a : EReal) * affine x + ((1 - a : ℝ) : EReal) * affine y -
          ((((0 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    simp only [affine, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    norm_num only [zero_div, zero_mul, EReal.coe_zero, sub_zero]
    simp only [← EReal.coe_mul, ← EReal.coe_add, le_refl]
  have hsupport : point 1 ∈ SourceSubdifferential affine (point 0) := by
    intro y
    have hpair : inner ℝ (point 1) (y - point 0) = y 0 := by
      simp [point, PiLp.inner_apply, Fin.sum_univ_one, RCLike.inner_apply,
        PiLp.sub_apply, EuclideanSpace.single_apply]
      change (y 0) * (1 : ℝ) = y 0
      exact mul_one _
    simp [affine, hpoint, hpair]
  have hno_min : ¬ (∃ p : E, ∀ q : E, affine p ≤ affine q) := by
    rintro ⟨p, hp⟩
    have hbad := hp (point (p 0 - 1))
    have hr : p 0 ≤ p 0 - 1 := by
      simpa only [affine, hpoint, EReal.coe_le_coe_iff] using hbad
    linarith
  exact ⟨hproper, hclosed, hstrong, hsupport, hno_min⟩

end BanditRL.Tests.OnlineStrongConvexAttainmentCanary
