import FullIffCandidate

noncomputable section
open Set
namespace BanditRL.Tests.OnlineStrongConvexSubgradientIffCanary
open BanditRL.OnlineConvex

abbrev E := Fin 2 → ℝ
abbrev U := EuclideanSpace ℝ (Fin 2)
def feasible : Set E := {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}
def objective (x : E) : EReal :=
  (((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0 : ℝ) : EReal)
def coordinates : E ≃ₗ[ℝ] U := (WithLp.linearEquiv 2 ℝ E).symm
def scaledCoordinates : E ≃ₗ[ℝ] U :=
  coordinates.trans (LinearEquiv.smulOfNeZero ℝ U 2 two_ne_zero)
def covector (p : E) : U :=
  (1 / 2 : ℝ) • coordinates (fun i => p i + if i = 0 then 1 else 0)
def query : E := fun _ => 1
def negativeSquare (x : ℝ) : EReal := ((-x ^ 2 : ℝ) : EReal)

theorem box_converse_originalNorm :
    (∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      objective (a • x + (1 - a) • y) ≤
        (a : EReal) * objective x + ((1 - a : ℝ) : EReal) * objective y -
          ((((1 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ∧
    SourceProper objective ∧
    (∀ p ∈ feasible,
      covector p ∈ SourceSubdifferential
        (fun u => objective (scaledCoordinates.symm u)) (scaledCoordinates p)) ∧
    (∀ p ∈ feasible, ∀ q ∈ feasible, ∀ g : U,
      g ∈ SourceSubdifferential
        (fun u => objective (scaledCoordinates.symm u)) (scaledCoordinates p) →
        (objective p).toReal + inner ℝ g (scaledCoordinates (q - p)) +
          (1 / 2 : ℝ) * ‖q - p‖ ^ 2 ≤ (objective q).toReal) ∧
    ‖query‖ ^ 2 = (1 : ℝ) ∧
    ‖scaledCoordinates query‖ ^ 2 = (8 : ℝ) ∧
    inner ℝ (covector 0) (scaledCoordinates query) = (1 : ℝ) ∧
    covector 0 ≠ 0 ∧
    objective 0 = (0 : EReal) ∧ objective query = (2 : EReal) ∧
    ¬ ((objective 0).toReal + inner ℝ (covector 0) (scaledCoordinates query) +
      (1 / 2 : ℝ) * ‖scaledCoordinates query‖ ^ 2 ≤ (objective query).toReal) ∧
    (1 / 2 : ℝ) * (objective query).toReal +
      (1 / 2 : ℝ) * (objective (-query)).toReal - (objective 0).toReal -
      (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / 2 : ℝ) * ‖query - (-query)‖ ^ 2 =
        (1 / 2 : ℝ) := by
  classical
  have hscaled (v : E) : scaledCoordinates v = (2 : ℝ) • coordinates v := rfl
  have hpair (w v : E) : inner ℝ (coordinates w) (scaledCoordinates v) =
      2 * (w 0 * v 0 + w 1 * v 1) := by
    rw [hscaled, real_inner_smul_right]
    norm_num [coordinates, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    ring
  have hcov (p v : E) : inner ℝ (covector p) (scaledCoordinates v) =
      (p 0 + 1) * v 0 + p 1 * v 1 := by
    rw [covector, real_inner_smul_left, hpair]
    norm_num
    ring
  have hproper : SourceProper objective := by
    exact ⟨fun x => EReal.coe_ne_bot _, 0, 0, by norm_num [objective]⟩
  have hconv : Convex ℝ feasible := by
    intro x hx y hy a b ha hb hab i
    exact convex_Icc (-1 : ℝ) 1 (hx i) (hy i) ha hb hab
  have hsub (p : E) : covector p ∈ SourceSubdifferential
      (fun u => objective (scaledCoordinates.symm u)) (scaledCoordinates p) := by
    intro u
    obtain ⟨v, rfl⟩ := scaledCoordinates.surjective u
    simp only [LinearEquiv.symm_apply_apply, ← map_sub, hcov, Pi.sub_apply]
    change (((p 0 ^ 2 + p 1 ^ 2) / 2 + p 0 : ℝ) : EReal) +
      (((p 0 + 1) * (v 0 - p 0) + p 1 * (v 1 - p 1) : ℝ) : EReal) ≤
      (((v 0 ^ 2 + v 1 ^ 2) / 2 + v 0 : ℝ) : EReal)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith [sq_nonneg (v 0 - p 0), sq_nonneg (v 1 - p 1)]
  have hnorm (v : E) : ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
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
  have hgrowth : ∀ p ∈ feasible, ∀ q ∈ feasible, ∀ g : U,
      g ∈ SourceSubdifferential (fun u => objective (scaledCoordinates.symm u))
        (scaledCoordinates p) →
      (objective p).toReal + inner ℝ g (scaledCoordinates (q - p)) +
        (1 / 2 : ℝ) * ‖q - p‖ ^ 2 ≤ (objective q).toReal := by
    intro p hp q hq g hg
    obtain ⟨w, rfl⟩ := coordinates.surjective g
    have hs (v : E) := hg (scaledCoordinates v)
    simp only [LinearEquiv.symm_apply_apply, ← map_sub, hpair, Pi.sub_apply] at hs
    have h0 := hs (fun i => if i = 0 then 2 * w 0 - 1 else p 1)
    have h1 := hs (fun i => if i = 0 then p 0 else 2 * w 1)
    change objective p + _ ≤ objective _ at h0 h1
    simp only [objective, ← EReal.coe_add, EReal.coe_le_coe_iff] at h0 h1
    norm_num at h0 h1
    have he0 : (2 * w 0 - p 0 - 1) ^ 2 = 0 := by
      apply le_antisymm
      · nlinarith [h0]
      · exact sq_nonneg _
    have he1 : (2 * w 1 - p 1) ^ 2 = 0 := by
      apply le_antisymm
      · nlinarith [h1]
      · exact sq_nonneg _
    have hw0 : 2 * w 0 = p 0 + 1 := by have := sq_eq_zero_iff.mp he0; linarith
    have hw1 : 2 * w 1 = p 1 := by have := sq_eq_zero_iff.mp he1; linarith
    rw [hpair]
    simp only [objective, EReal.toReal_coe, Pi.sub_apply]
    have hn := hnorm (q - p)
    simp only [Pi.sub_apply] at hn
    have hpq : 2 * (w 0 * (q 0 - p 0) + w 1 * (q 1 - p 1)) =
        (p 0 + 1) * (q 0 - p 0) + p 1 * (q 1 - p 1) := by
      calc
        _ = (2 * w 0) * (q 0 - p 0) + (2 * w 1) * (q 1 - p 1) := by ring
        _ = _ := by rw [hw0, hw1]
    rw [hpq]
    nlinarith [hn]
  have hbound := (stronglyConvex_iff_sourceSubgradient_growth 2 scaledCoordinates
    objective feasible 1 hproper hconv (by norm_num)
    (fun p hp => ⟨covector p, hsub p⟩)).mpr hgrowth
  have hn : ‖query‖ ^ 2 = (1 : ℝ) := by norm_num [query]
  have hc : ‖scaledCoordinates query‖ ^ 2 = (8 : ℝ) := by
    rw [hscaled, norm_smul, mul_pow, EuclideanSpace.real_norm_sq_eq]
    norm_num [coordinates, query, Fin.sum_univ_two]
  have hp : inner ℝ (covector 0) (scaledCoordinates query) = (1 : ℝ) := by
    rw [hcov]
    norm_num [query]
  have hg0 : covector 0 ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hp
    norm_num at hp
  have hf0 : objective 0 = (0 : EReal) := by norm_num [objective]
  have hfq : objective query = (2 : EReal) := by norm_num [objective, query]
  have hfn : objective (-query) = (0 : EReal) := by norm_num [objective, query]
  have hdiff : ‖query - (-query)‖ ^ 2 = (4 : ℝ) := by
    have hh : query - (-query) = (fun _ : Fin 2 => (2 : ℝ)) := by ext i; norm_num [query]
    rw [hh]
    norm_num
  have hwrong : ¬ ((objective 0).toReal + inner ℝ (covector 0) (scaledCoordinates query) +
      (1 / 2 : ℝ) * ‖scaledCoordinates query‖ ^ 2 ≤ (objective query).toReal) := by
    rw [hf0, hfq, hp, hc]
    norm_num
  refine ⟨hbound, hproper, fun p hp => hsub p, hgrowth, hn, hc, hp, hg0, hf0, hfq, hwrong, ?_⟩
  rw [hfq, hfn, hf0, hdiff]
  norm_num

theorem absent_support_vacuity :
    SourceProper negativeSquare ∧
    (∀ p : ℝ, SourceSubdifferential negativeSquare p = ∅) ∧
    (∀ p q : ℝ, ∀ g ∈ SourceSubdifferential negativeSquare p,
      (negativeSquare p).toReal + inner ℝ g (q - p) +
        ((0 : ℝ) / 2) * ‖q - p‖ ^ 2 ≤ (negativeSquare q).toReal) ∧
    ¬ (∀ x y : ℝ, ∀ a : ℝ, 0 < a → a < 1 →
      negativeSquare (a • x + (1 - a) • y) ≤
        (a : EReal) * negativeSquare x + ((1 - a : ℝ) : EReal) * negativeSquare y -
          ((((0 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ∧
    negativeSquare 0 = (0 : EReal) ∧
    (1 / 2 : EReal) * negativeSquare (-1) +
      (1 / 2 : EReal) * negativeSquare 1 = (-1 : EReal) := by
  have hproper : SourceProper negativeSquare :=
    ⟨fun x => EReal.coe_ne_bot _, 0, 0, by norm_num [negativeSquare]⟩
  have hempty (p : ℝ) : SourceSubdifferential negativeSquare p = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro g hg
    have hp := hg (p + 1)
    have hm := hg (p - 1)
    simp only [negativeSquare, real_inner_comm, RCLike.inner_apply,
      conj_trivial, ← EReal.coe_add, EReal.coe_le_coe_iff] at hp hm
    norm_num at hp hm
    nlinarith
  refine ⟨hproper, hempty, ?_, ?_, ?_, ?_⟩
  · intro p q g hg
    rw [hempty p] at hg
    exact False.elim hg
  · intro h
    have hh := h (-1) 1 (1 / 2) (by norm_num) (by norm_num)
    norm_num [negativeSquare] at hh
  · norm_num [negativeSquare]
  · norm_num [negativeSquare]

end BanditRL.Tests.OnlineStrongConvexSubgradientIffCanary
