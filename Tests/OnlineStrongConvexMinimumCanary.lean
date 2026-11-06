import BanditRLProof.OnlineStrongConvexMinimum
import Mathlib.Tactic

noncomputable section
open Set
namespace BanditRL.Tests.OnlineStrongConvexMinimumCanary
open BanditRL.OnlineConvex

abbrev squareLoss (x : ℝ) : EReal := ((x ^ 2 : ℝ) : EReal)
abbrev intervalLoss : ℝ → EReal := extendedIndicator (Set.Icc (0 : ℝ) 1)

theorem square_two_exact_growth :
    (∀ q : ℝ, (squareLoss 0).toReal + (2 / 2 : ℝ) * ‖q - 0‖ ^ 2 ≤
      (squareLoss q).toReal) ∧
    (∀ q : ℝ, (squareLoss 0).toReal + (2 / 2 : ℝ) * ‖q - 0‖ ^ 2 =
      (squareLoss q).toReal) ∧ (9 : ℝ) ≤ 9 := by
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
  have hm : IsMinOn squareLoss Set.univ 0 := by
    intro x hx
    simpa only [squareLoss, zero_pow (by decide : 2 ≠ 0), EReal.coe_le_coe_iff]
      using (sq_nonneg x)
  have hg (q : ℝ) := stronglyConvex_minimum_growth squareLoss Set.univ 2
    hp convex_univ hd (by norm_num) hs 0 (Set.mem_univ _) hm q (Set.mem_univ _)
  refine ⟨hg, ?_, ?_⟩
  · intro q
    simp only [squareLoss, EReal.toReal_coe]
    simp [Real.norm_eq_abs, sq_abs]
  · simpa [squareLoss, Real.norm_eq_abs] using hg 3

theorem interval_zero_extended_domain :
    (intervalLoss 0).toReal + (0 / 2 : ℝ) * ‖(1 : ℝ) - 0‖ ^ 2 ≤
      (intervalLoss 1).toReal ∧
    intervalLoss 2 = ⊤ ∧
    effectiveDomain intervalLoss = Set.Icc (0 : ℝ) 1 ∧
    IsMinOn intervalLoss (Set.Icc (0 : ℝ) 1) 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hp : SourceProper intervalLoss :=
    (sourceProper_indicator_iff _).mpr ⟨0, h0⟩
  have hV : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hd : Set.Icc (0 : ℝ) 1 ⊆ effectiveDomain intervalLoss := by
    rw [effectiveDomain_indicator]
  have hs : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ∀ a : ℝ, 0 < a → a < 1 →
      intervalLoss (a • x + (1 - a) • y) ≤
        (a : EReal) * intervalLoss x + ((1 - a : ℝ) : EReal) * intervalLoss y -
          (((0 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hm := hV hx hy (le_of_lt ha) (le_of_lt (sub_pos.mpr ha1))
      (show a + (1 - a) = 1 by ring)
    simp only [intervalLoss, extendedIndicator, if_pos hx, if_pos hy, if_pos hm]
    norm_num
  have hm : IsMinOn intervalLoss (Set.Icc (0 : ℝ) 1) 0 := by
    intro x hx
    change intervalLoss 0 ≤ intervalLoss x
    simp only [intervalLoss, extendedIndicator, if_pos hx, if_pos h0, le_refl]
  have hg := stronglyConvex_minimum_growth intervalLoss (Set.Icc (0 : ℝ) 1) 0
    hp hV hd (by norm_num) hs 0 h0 hm 1 h1
  refine ⟨hg, ?_, ?_, hm⟩
  · norm_num [intervalLoss, extendedIndicator]
  · exact effectiveDomain_indicator _

end BanditRL.Tests.OnlineStrongConvexMinimumCanary
