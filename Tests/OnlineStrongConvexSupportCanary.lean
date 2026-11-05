import BanditRLProof.OnlineStrongConvexSupport

noncomputable section
open Set
namespace BanditRL.Tests.OnlineStrongConvexSupportCanary
open BanditRL.OnlineConvex

abbrev squareLoss (x : ℝ) : EReal := ((x ^ 2 : ℝ) : EReal)
abbrev fourSupport : ℝ →L[ℝ] ℝ := (4 : ℝ) • ContinuousLinearMap.id ℝ ℝ
abbrev negativeSupport : ℝ →L[ℝ] ℝ := (-1 : ℝ) • ContinuousLinearMap.id ℝ ℝ
noncomputable def restrictedSquare (x : ℝ) : EReal := by
  classical
  exact if x ∈ Set.Icc (0 : ℝ) 1 then ((x ^ 2 : ℝ) : EReal) else ⊤

theorem nonzero_point_nonzero_support_sharp :
    (∀ q : ℝ, (squareLoss 2).toReal + fourSupport (q - 2) +
      (2 / 2 : ℝ) * ‖q - 2‖ ^ 2 ≤ (squareLoss q).toReal) ∧
    (∀ q : ℝ, (squareLoss 2).toReal + fourSupport (q - 2) +
      (2 / 2 : ℝ) * ‖q - 2‖ ^ 2 = (squareLoss q).toReal) ∧
    fourSupport 1 = 4 ∧
    (∀ z : ℝ, squareLoss 2 + (fourSupport (z - 2) : EReal) ≤ squareLoss z) ∧
    ¬ IsMinOn squareLoss Set.univ 2 := by
  have hp : SourceProper squareLoss := by
    constructor
    · intro x; exact EReal.coe_ne_bot _
    · exact ⟨0, 0, by norm_num [squareLoss]⟩
  have hd : (Set.univ : Set ℝ) ⊆ effectiveDomain squareLoss := by
    intro x hx
    exact EReal.coe_lt_top _
  have hs : ∀ x ∈ (Set.univ : Set ℝ), ∀ y ∈ (Set.univ : Set ℝ),
      ∀ a : ℝ, 0 < a → a < 1 →
      squareLoss (a • x + (1 - a) • y) ≤
        (a : EReal) * squareLoss x + ((1 - a : ℝ) : EReal) * squareLoss y -
          (((2 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    simp only [squareLoss, smul_eq_mul, ← EReal.coe_mul, ← EReal.coe_add,
      ← EReal.coe_sub, EReal.coe_le_coe_iff]
    norm_num only [show (2 / 2 : ℝ) = 1 by norm_num, one_mul,
      Real.norm_eq_abs, sq_abs]
    apply le_of_eq
    ring
  have hsupport (z : ℝ) :
      squareLoss 2 + (fourSupport (z - 2) : EReal) ≤ squareLoss z := by
    simp only [squareLoss, fourSupport, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    nlinarith [sq_nonneg (z - 2)]
  have hg (q : ℝ) := stronglyConvex_support_growth squareLoss Set.univ 2
    hp convex_univ hd (by norm_num) hs 2 (Set.mem_univ _) fourSupport
    (fun z hz => hsupport z) q (Set.mem_univ _)
  refine ⟨hg, ?_, ?_, hsupport, ?_⟩
  · intro q
    simp only [squareLoss, EReal.toReal_coe, fourSupport,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      Real.norm_eq_abs, sq_abs]
    norm_num
    ring
  · norm_num [fourSupport]
  · intro hm
    have hbad := (isMinOn_iff.mp hm) 0 (Set.mem_univ _)
    norm_num [squareLoss] at hbad

theorem boundary_nonzero_support_extended_domain :
    (∀ q ∈ Set.Icc (0 : ℝ) 1,
      (restrictedSquare 0).toReal + negativeSupport (q - 0) +
        (2 / 2 : ℝ) * ‖q - 0‖ ^ 2 ≤ (restrictedSquare q).toReal) ∧
    negativeSupport 1 = -1 ∧
    (∀ z ∈ Set.Icc (0 : ℝ) 1,
      restrictedSquare 0 + (negativeSupport (z - 0) : EReal) ≤ restrictedSquare z) ∧
    restrictedSquare 2 = ⊤ ∧
    effectiveDomain restrictedSquare = Set.Icc (0 : ℝ) 1 ∧
    (restrictedSquare 0).toReal + negativeSupport ((1 : ℝ) - 0) +
      (2 / 2 : ℝ) * ‖(1 : ℝ) - 0‖ ^ 2 = 0 ∧
    (restrictedSquare 1).toReal = 1 ∧
    (restrictedSquare 0).toReal + negativeSupport ((1 : ℝ) - 0) +
      (2 / 2 : ℝ) * ‖(1 : ℝ) - 0‖ ^ 2 < (restrictedSquare 1).toReal := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hdomain : effectiveDomain restrictedSquare = Set.Icc (0 : ℝ) 1 := by
    ext x
    change (if x ∈ Set.Icc (0 : ℝ) 1 then ((x ^ 2 : ℝ) : EReal) else ⊤) < ⊤ ↔
      x ∈ Set.Icc (0 : ℝ) 1
    split_ifs with hx
    · exact iff_of_true (EReal.coe_lt_top _) hx
    · exact iff_of_false (lt_irrefl _) hx
  have hp : SourceProper restrictedSquare := by
    constructor
    · intro x
      unfold restrictedSquare
      split_ifs
      · exact EReal.coe_ne_bot _
      · exact top_ne_bot
    · exact ⟨0, 0, by norm_num [restrictedSquare]⟩
  have hV : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hd : Set.Icc (0 : ℝ) 1 ⊆ effectiveDomain restrictedSquare := by
    rw [hdomain]
  have hs : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ∀ a : ℝ, 0 < a → a < 1 →
      restrictedSquare (a • x + (1 - a) • y) ≤
        (a : EReal) * restrictedSquare x + ((1 - a : ℝ) : EReal) * restrictedSquare y -
          (((2 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hm := hV hx hy (le_of_lt ha) (le_of_lt (sub_pos.mpr ha1))
      (show a + (1 - a) = 1 by ring)
    simp only [smul_eq_mul] at hm
    simp only [restrictedSquare, if_pos hx, if_pos hy, if_pos hm,
      smul_eq_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
      EReal.coe_le_coe_iff]
    norm_num only [show (2 / 2 : ℝ) = 1 by norm_num, one_mul,
      Real.norm_eq_abs, sq_abs]
    apply le_of_eq
    ring
  have hsupport (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      restrictedSquare 0 + (negativeSupport (z - 0) : EReal) ≤ restrictedSquare z := by
    simp only [restrictedSquare, if_pos h0, if_pos hz, negativeSupport,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith [sq_nonneg z, hz.1]
  have hg (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :=
    stronglyConvex_support_growth restrictedSquare (Set.Icc (0 : ℝ) 1) 2
      hp hV hd (by norm_num) hs 0 h0 negativeSupport hsupport q hq
  refine ⟨hg, ?_, hsupport, ?_, hdomain, ?_, ?_, ?_⟩
  · norm_num [negativeSupport]
  · norm_num [restrictedSquare]
  · norm_num [restrictedSquare, negativeSupport, Real.norm_eq_abs]
  · norm_num [restrictedSquare]
  · norm_num [restrictedSquare, negativeSupport, Real.norm_eq_abs]

end BanditRL.Tests.OnlineStrongConvexSupportCanary
