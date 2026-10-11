import VectorAdapterCandidate

noncomputable section
open Set
namespace BanditRL.Tests.OnlineStrongConvexSourceSubgradientCanary
open BanditRL.OnlineConvex

abbrev E := Fin 2 → ℝ
abbrev U := EuclideanSpace ℝ (Fin 2)

def feasible : Set E := {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}
def objective (x : E) : EReal :=
  (((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0 : ℝ) : EReal) + extendedIndicator feasible x
def base : E := 0
def query : E := fun _ => 1
def outside : E := fun _ => 2

def coordinates : E ≃ₗ[ℝ] U := (WithLp.linearEquiv 2 ℝ E).symm
def supportVector : U := coordinates (fun i => if i = 0 then 1 else 0)
def scaledCoordinates : E ≃ₗ[ℝ] U :=
  coordinates.trans (LinearEquiv.smulOfNeZero ℝ U 2 two_ne_zero)
def scaledSupportVector : U := (1 / 2 : ℝ) • supportVector

theorem supNorm_nonzero_support :
    ((objective base).toReal + inner ℝ supportVector (coordinates (query - base)) +
      (1 / 2 : ℝ) * ‖query - base‖ ^ 2 ≤ (objective query).toReal) ∧
    ‖query - base‖ ^ 2 = (1 : ℝ) ∧
    ‖coordinates (query - base)‖ ^ 2 = (2 : ℝ) ∧
    inner ℝ supportVector (coordinates (query - base)) = (1 : ℝ) ∧
    supportVector ≠ 0 ∧
    base ∈ feasible ∧ query ∈ feasible ∧ outside ∉ feasible ∧
    objective base = (0 : EReal) ∧ objective query = (2 : EReal) ∧
    objective outside = ⊤ := by
  classical
  have hp : base ∈ feasible := by norm_num [base, feasible]
  have hq : query ∈ feasible := by norm_num [query, feasible]
  have hout : outside ∉ feasible := by
    intro h
    have h0 := h 0
    norm_num [outside] at h0
  have hfin (x : E) (hx : x ∈ feasible) :
      objective x = (((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0 : ℝ) : EReal) := by
    simp [objective, extendedIndicator, hx]
  have hf0 : objective base = (0 : EReal) := by
    rw [hfin base hp]
    norm_num [base]
  have hfq : objective query = (2 : EReal) := by
    rw [hfin query hq]
    norm_num [query]
    rfl
  have hfo : objective outside = ⊤ := by
    simp [objective, extendedIndicator, hout]
  have hproper : SourceProper objective := by
    constructor
    · intro x
      by_cases hx : x ∈ feasible
      · rw [hfin x hx]
        exact EReal.coe_ne_bot _
      · simp [objective, extendedIndicator, hx]
    · exact ⟨base, 0, hf0⟩
  have hconv : Convex ℝ feasible := by
    intro x hx y hy a b ha hb hab i
    exact convex_Icc (-1 : ℝ) 1 (hx i) (hy i) ha hb hab
  have hdom : feasible ⊆ effectiveDomain objective := by
    intro x hx
    change objective x < ⊤
    rw [hfin x hx]
    exact EReal.coe_lt_top _
  have hnorm_sq (v : E) : ‖v‖ ^ 2 ≤ (v 0) ^ 2 + (v 1) ^ 2 := by
    have hm : ‖v‖ ≤ max |v 0| |v 1| := by
      apply (pi_norm_le_iff_of_nonneg (le_trans (abs_nonneg _) (le_max_left _ _))).2
      intro i
      fin_cases i
      · simpa only [Real.norm_eq_abs] using le_max_left |v 0| |v 1|
      · simpa only [Real.norm_eq_abs] using le_max_right |v 0| |v 1|
    rcases le_total |v 0| |v 1| with h | h
    · rw [max_eq_right h] at hm
      nlinarith [norm_nonneg v, abs_nonneg (v 1), sq_abs (v 1), sq_nonneg (v 0)]
    · rw [max_eq_left h] at hm
      nlinarith [norm_nonneg v, abs_nonneg (v 0), sq_abs (v 0), sq_nonneg (v 1)]
  have hstrong : ∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      objective (a • x + (1 - a) • y) ≤
        (a : EReal) * objective x + ((1 - a : ℝ) : EReal) * objective y -
          (((1 / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz : a • x + (1 - a) • y ∈ feasible :=
      hconv hx hy ha.le (by linarith) (by ring)
    rw [hfin _ hz, hfin x hx, hfin y hy]
    have hn := hnorm_sq (x - y)
    have hw : 0 ≤ (1 / 2 : ℝ) * a * (1 - a) :=
      mul_nonneg (mul_nonneg (by norm_num) ha.le) (sub_nonneg.mpr ha1.le)
    have hb := mul_le_mul_of_nonneg_left hn hw
    simp only [Pi.sub_apply] at hb
    have hid :
        a * ((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0) +
        (1 - a) * ((y 0 ^ 2 + y 1 ^ 2) / 2 + y 0) -
        (((a * x 0 + (1 - a) * y 0) ^ 2 +
          (a * x 1 + (1 - a) * y 1) ^ 2) / 2 +
          (a * x 0 + (1 - a) * y 0)) =
        (1 / 2 : ℝ) * a * (1 - a) * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by ring
    have hr :
        (((a * x 0 + (1 - a) * y 0) ^ 2 +
          (a * x 1 + (1 - a) * y 1) ^ 2) / 2 +
          (a * x 0 + (1 - a) * y 0)) ≤
        a * ((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0) +
          (1 - a) * ((y 0 ^ 2 + y 1 ^ 2) / 2 + y 0) -
          (1 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 := by linarith
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast hr
  have hpair0 (z : E) : inner ℝ supportVector (coordinates z) = z 0 := by
    norm_num [supportVector, coordinates, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  have hn : ‖query - base‖ ^ 2 = (1 : ℝ) := by
    have heq : query - base = (fun _ : Fin 2 => (1 : ℝ)) := by
      ext i
      simp [query, base]
    rw [heq]
    norm_num
  have hpair := hpair0
  have hsupport : supportVector ∈ SourceSubdifferential
      (fun u => objective (coordinates.symm u)) (coordinates base) := by
    intro u
    obtain ⟨z, rfl⟩ := coordinates.surjective u
    simp only [LinearEquiv.symm_apply_apply, ← map_sub, hpair]
    rw [hf0]
    by_cases hz : z ∈ feasible
    · rw [hfin z hz]
      have hr : z 0 ≤ (z 0 ^ 2 + z 1 ^ 2) / 2 + z 0 := by
        nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      simpa only [base, Pi.zero_apply, Pi.sub_apply, sub_zero, zero_add] using
        (show (z 0 : EReal) ≤ (((z 0 ^ 2 + z 1 ^ 2) / 2 + z 0 : ℝ) : EReal) from
          EReal.coe_le_coe_iff.mpr hr)
    · simp [objective, extendedIndicator, hz]
  have hbound := stronglyConvex_sourceSubgradient_growth 2 coordinates objective feasible 1
    hproper hconv hdom (by norm_num) hstrong base hp supportVector hsupport query hq
  have hpq : inner ℝ supportVector (coordinates (query - base)) = (1 : ℝ) := by
    rw [hpair]
    norm_num [query, base]
  have hnonzero : supportVector ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at hpq
    norm_num at hpq
  have hnc : ‖coordinates (query - base)‖ ^ 2 = (2 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [coordinates, query, base, Fin.sum_univ_two]
  exact ⟨hbound, hn, hnc, hpq, hnonzero, hp, hq, hout, hf0, hfq, hfo⟩

theorem scaledCoordinates_discriminate_wrong_norm :
    ((objective base).toReal +
      inner ℝ scaledSupportVector (scaledCoordinates (query - base)) +
      (1 / 2 : ℝ) * ‖query - base‖ ^ 2 ≤ (objective query).toReal) ∧
    ‖query - base‖ ^ 2 = (1 : ℝ) ∧
    ‖scaledCoordinates (query - base)‖ ^ 2 = (8 : ℝ) ∧
    inner ℝ scaledSupportVector (scaledCoordinates (query - base)) = (1 : ℝ) ∧
    scaledSupportVector ≠ 0 ∧
    (∀ x : E, scaledCoordinates x = (2 : ℝ) • coordinates x) ∧
    base ∈ feasible ∧ query ∈ feasible ∧ outside ∉ feasible ∧
    objective base = (0 : EReal) ∧ objective query = (2 : EReal) ∧
    objective outside = ⊤ ∧
    ¬ ((objective base).toReal +
      inner ℝ scaledSupportVector (scaledCoordinates (query - base)) +
      (1 / 2 : ℝ) * ‖scaledCoordinates (query - base)‖ ^ 2 ≤
        (objective query).toReal) := by
  classical
  have hp : base ∈ feasible := by norm_num [base, feasible]
  have hq : query ∈ feasible := by norm_num [query, feasible]
  have hout : outside ∉ feasible := by
    intro h
    have h0 := h 0
    norm_num [outside] at h0
  have hfin (x : E) (hx : x ∈ feasible) :
      objective x = (((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0 : ℝ) : EReal) := by
    simp [objective, extendedIndicator, hx]
  have hf0 : objective base = (0 : EReal) := by
    rw [hfin base hp]
    norm_num [base]
  have hfq : objective query = (2 : EReal) := by
    rw [hfin query hq]
    norm_num [query]
    rfl
  have hfo : objective outside = ⊤ := by
    simp [objective, extendedIndicator, hout]
  have hproper : SourceProper objective := by
    constructor
    · intro x
      by_cases hx : x ∈ feasible
      · rw [hfin x hx]
        exact EReal.coe_ne_bot _
      · simp [objective, extendedIndicator, hx]
    · exact ⟨base, 0, hf0⟩
  have hconv : Convex ℝ feasible := by
    intro x hx y hy a b ha hb hab i
    exact convex_Icc (-1 : ℝ) 1 (hx i) (hy i) ha hb hab
  have hdom : feasible ⊆ effectiveDomain objective := by
    intro x hx
    change objective x < ⊤
    rw [hfin x hx]
    exact EReal.coe_lt_top _
  have hnorm_sq (v : E) : ‖v‖ ^ 2 ≤ (v 0) ^ 2 + (v 1) ^ 2 := by
    have hm : ‖v‖ ≤ max |v 0| |v 1| := by
      apply (pi_norm_le_iff_of_nonneg (le_trans (abs_nonneg _) (le_max_left _ _))).2
      intro i
      fin_cases i
      · simpa only [Real.norm_eq_abs] using le_max_left |v 0| |v 1|
      · simpa only [Real.norm_eq_abs] using le_max_right |v 0| |v 1|
    rcases le_total |v 0| |v 1| with h | h
    · rw [max_eq_right h] at hm
      nlinarith [norm_nonneg v, abs_nonneg (v 1), sq_abs (v 1), sq_nonneg (v 0)]
    · rw [max_eq_left h] at hm
      nlinarith [norm_nonneg v, abs_nonneg (v 0), sq_abs (v 0), sq_nonneg (v 1)]
  have hstrong : ∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      objective (a • x + (1 - a) • y) ≤
        (a : EReal) * objective x + ((1 - a : ℝ) : EReal) * objective y -
          (((1 / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz : a • x + (1 - a) • y ∈ feasible :=
      hconv hx hy ha.le (by linarith) (by ring)
    rw [hfin _ hz, hfin x hx, hfin y hy]
    have hn := hnorm_sq (x - y)
    have hw : 0 ≤ (1 / 2 : ℝ) * a * (1 - a) :=
      mul_nonneg (mul_nonneg (by norm_num) ha.le) (sub_nonneg.mpr ha1.le)
    have hb := mul_le_mul_of_nonneg_left hn hw
    simp only [Pi.sub_apply] at hb
    have hid :
        a * ((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0) +
        (1 - a) * ((y 0 ^ 2 + y 1 ^ 2) / 2 + y 0) -
        (((a * x 0 + (1 - a) * y 0) ^ 2 +
          (a * x 1 + (1 - a) * y 1) ^ 2) / 2 +
          (a * x 0 + (1 - a) * y 0)) =
        (1 / 2 : ℝ) * a * (1 - a) * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by ring
    have hr :
        (((a * x 0 + (1 - a) * y 0) ^ 2 +
          (a * x 1 + (1 - a) * y 1) ^ 2) / 2 +
          (a * x 0 + (1 - a) * y 0)) ≤
        a * ((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0) +
          (1 - a) * ((y 0 ^ 2 + y 1 ^ 2) / 2 + y 0) -
          (1 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 := by linarith
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast hr
  have hpair0 (z : E) : inner ℝ supportVector (coordinates z) = z 0 := by
    norm_num [supportVector, coordinates, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  have hn : ‖query - base‖ ^ 2 = (1 : ℝ) := by
    have heq : query - base = (fun _ : Fin 2 => (1 : ℝ)) := by
      ext i
      simp [query, base]
    rw [heq]
    norm_num
  have hscaled (x : E) : scaledCoordinates x = (2 : ℝ) • coordinates x := by
    rfl
  have hpair (z : E) : inner ℝ scaledSupportVector (scaledCoordinates z) = z 0 := by
    rw [scaledSupportVector, hscaled, real_inner_smul_left, real_inner_smul_right, hpair0]
    ring
  have hsupport : scaledSupportVector ∈ SourceSubdifferential
      (fun u => objective (scaledCoordinates.symm u)) (scaledCoordinates base) := by
    intro u
    obtain ⟨z, rfl⟩ := scaledCoordinates.surjective u
    simp only [LinearEquiv.symm_apply_apply, ← map_sub, hpair]
    rw [hf0]
    by_cases hz : z ∈ feasible
    · rw [hfin z hz]
      have hr : z 0 ≤ (z 0 ^ 2 + z 1 ^ 2) / 2 + z 0 := by
        nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      simpa only [base, Pi.zero_apply, Pi.sub_apply, sub_zero, zero_add] using
        (show (z 0 : EReal) ≤ (((z 0 ^ 2 + z 1 ^ 2) / 2 + z 0 : ℝ) : EReal) from
          EReal.coe_le_coe_iff.mpr hr)
    · simp [objective, extendedIndicator, hz]
  have hbound := stronglyConvex_sourceSubgradient_growth 2 scaledCoordinates objective feasible 1
    hproper hconv hdom (by norm_num) hstrong base hp scaledSupportVector hsupport query hq
  have hpq : inner ℝ scaledSupportVector (scaledCoordinates (query - base)) = (1 : ℝ) := by
    rw [hpair]
    norm_num [query, base]
  have hnonzero : scaledSupportVector ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at hpq
    norm_num at hpq
  have hnc0 : ‖coordinates (query - base)‖ ^ 2 = (2 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [coordinates, query, base, Fin.sum_univ_two]
  have hnc : ‖scaledCoordinates (query - base)‖ ^ 2 = (8 : ℝ) := by
    rw [hscaled, norm_smul, mul_pow, hnc0]
    norm_num
  have hwrong : ¬ ((objective base).toReal +
      inner ℝ scaledSupportVector (scaledCoordinates (query - base)) +
      (1 / 2 : ℝ) * ‖scaledCoordinates (query - base)‖ ^ 2 ≤
        (objective query).toReal) := by
    rw [hf0, hfq, hpq, hnc]
    change ¬ ((0 : ℝ) + 1 + (1 / 2) * 8 ≤ 2)
    norm_num
  exact ⟨hbound, hn, hnc, hpq, hnonzero, hscaled, hp, hq, hout, hf0, hfq, hfo, hwrong⟩

end BanditRL.Tests.OnlineStrongConvexSourceSubgradientCanary
