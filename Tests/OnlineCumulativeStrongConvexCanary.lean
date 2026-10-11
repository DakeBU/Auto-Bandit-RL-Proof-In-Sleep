import BanditRLProof.OnlineCumulativeStrongConvex
import BanditRLProof.OnlineStrongConvexSupport

noncomputable section
open Set Finset
namespace BanditRL.Tests.OnlineCumulativeStrongConvexCanary
open BanditRL.OnlineConvex

abbrev feasible : Set ℝ := Set.Icc (-1 : ℝ) 1
abbrev quadraticRegularizer (x : ℝ) : ℝ := x ^ 2 / 2
noncomputable def twoLoss (i : ℕ) (x : ℝ) : EReal :=
  ((if i = 0 then -x else 3 * x : ℝ) : EReal) + extendedIndicator feasible x
noncomputable def twoObjective (x : ℝ) : EReal :=
  (quadraticRegularizer x : EReal) + ∑ i ∈ range 2, twoLoss i x +
    extendedIndicator feasible x
abbrev doubleSupport : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
abbrev linearRegularizer (x : ℝ) : ℝ := x
abbrev emptyLoss (_ : ℕ) (_ : ℝ) : EReal := ⊥
noncomputable def emptyObjective (x : ℝ) : EReal :=
  (linearRegularizer x : EReal) + ∑ i ∈ range 0, emptyLoss i x +
    extendedIndicator feasible x
abbrev unitSupport : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

theorem twoLoss_actual_producer_tight_support :
    (twoObjective 0).toReal + doubleSupport ((1 : ℝ) - 0) +
      (1 / 2 : ℝ) * ‖(1 : ℝ) - 0‖ ^ 2 ≤ (twoObjective 1).toReal ∧
    (SourceProper twoObjective ∧ effectiveDomain twoObjective = feasible ∧
      (∀ x ∈ feasible, twoObjective x =
        ((quadraticRegularizer x + ∑ i ∈ range 2, (twoLoss i x).toReal : ℝ) : EReal)) ∧
      (∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
        twoObjective (a • x + (1 - a) • y) ≤
          (a : EReal) * twoObjective x + ((1 - a : ℝ) : EReal) * twoObjective y -
            (((1 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))) ∧
    (∀ z ∈ feasible,
      twoObjective 0 + (doubleSupport (z - 0) : EReal) ≤ twoObjective z) ∧
    (twoObjective 0).toReal + doubleSupport ((1 : ℝ) - 0) +
      (1 / 2 : ℝ) * ‖(1 : ℝ) - 0‖ ^ 2 = (5 / 2 : ℝ) ∧
    (twoObjective 1).toReal = (5 / 2 : ℝ) ∧
    twoLoss 0 1 = ((-1 : ℝ) : EReal) ∧ twoLoss 1 1 = ((3 : ℝ) : EReal) ∧
    twoLoss 0 2 = ⊤ ∧ twoLoss 1 2 = ⊤ ∧ twoObjective 2 = ⊤ ∧
    ¬ IsMinOn twoObjective feasible 0 := by
  have h0 : (0 : ℝ) ∈ feasible := by norm_num [feasible]
  have h1 : (1 : ℝ) ∈ feasible := by norm_num [feasible]
  have hm1 : (-1 : ℝ) ∈ feasible := by norm_num [feasible]
  have hv (i : ℕ) (z : ℝ) (hz : z ∈ feasible) :
      twoLoss i z = ((if i = 0 then -z else 3 * z : ℝ) : EReal) := by
    simp only [twoLoss, extendedIndicator, if_pos hz, add_zero]
  have hpsi : StrongConvexOn feasible 1 quadraticRegularizer := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst b
    simp only [quadraticRegularizer, smul_eq_mul, Real.norm_eq_abs, sq_abs]
    apply le_of_eq
    ring
  have hbot : ∀ i < 2, ∀ z, twoLoss i z ≠ ⊥ := by
    intro i hi z
    by_cases hz : z ∈ feasible
    · rw [hv i z hz]
      exact EReal.coe_ne_bot _
    · simp [twoLoss, extendedIndicator, hz]
  have hdom : ∀ i < 2, feasible ⊆ effectiveDomain (twoLoss i) := by
    intro i hi z hz
    change twoLoss i z < ⊤
    rw [hv i z hz]
    exact EReal.coe_lt_top _
  have hloss : ∀ i < 2, ConvexOn ℝ feasible (fun z => (twoLoss i z).toReal) := by
    intro i hi
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hz := (convex_Icc (-1 : ℝ) 1) hx hy ha hb hab
    change (twoLoss i (a • x + b • y)).toReal ≤
      a * (twoLoss i x).toReal + b * (twoLoss i y).toReal
    rw [hv i _ hz, hv i x hx, hv i y hy]
    simp only [EReal.toReal_coe, smul_eq_mul]
    by_cases hi0 : i = 0
    · simp only [if_pos hi0]
      linarith
    · simp only [if_neg hi0]
      nlinarith
  have package := cumulative_regularizer_source_strongConvex feasible ⟨0, h0⟩
    quadraticRegularizer twoLoss 2 1 (by norm_num) hpsi hbot hdom hloss
  have hvalue (z : ℝ) (hz : z ∈ feasible) :
      twoObjective z = ((z ^ 2 / 2 + 2 * z : ℝ) : EReal) := by
    calc
      twoObjective z = ((quadraticRegularizer z + ∑ i ∈ range 2, (twoLoss i z).toReal : ℝ) : EReal) := package.2.2.1 z hz
      _ = _ := by
        simp only [sum_range_succ, sum_range_zero, zero_add]
        rw [hv 0 z hz, hv 1 z hz]
        norm_num only [if_pos, Nat.one_ne_zero, if_false, EReal.toReal_coe]
        congr 1
        dsimp [quadraticRegularizer]
        ring
  have hs : ∀ z ∈ feasible,
      twoObjective 0 + (doubleSupport (z - 0) : EReal) ≤ twoObjective z := by
    intro z hz
    rw [hvalue 0 h0, hvalue z hz]
    simp only [doubleSupport, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, sub_zero, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith [sq_nonneg z]
  have hg := stronglyConvex_support_growth twoObjective feasible 1 package.1
    (convex_Icc _ _) (by have hd : effectiveDomain twoObjective = feasible := package.2.1; rw [hd]) (by norm_num) package.2.2.2
    0 h0 doubleSupport hs 1 h1
  refine ⟨hg, package, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvalue 0 h0]
    norm_num [doubleSupport]
  · rw [hvalue 1 h1]
    norm_num
  · rw [hv 0 1 h1]
    norm_num
  · rw [hv 1 1 h1]
    norm_num
  · norm_num [twoLoss, extendedIndicator, feasible]
  · norm_num [twoLoss, extendedIndicator, feasible]
  · have ho0 : twoLoss 0 2 = ⊤ := by norm_num [twoLoss, extendedIndicator, feasible]
    have ho1 : twoLoss 1 2 = ⊤ := by norm_num [twoLoss, extendedIndicator, feasible]
    dsimp only [twoObjective]
    rw [sum_range_succ, sum_range_succ, sum_range_zero, zero_add, ho0, ho1]
    simp [extendedIndicator, feasible]
  · intro hm
    have h := hm hm1
    change twoObjective 0 ≤ twoObjective (-1) at h
    rw [hvalue 0 h0, hvalue (-1) hm1, EReal.coe_le_coe_iff] at h
    norm_num at h


theorem emptyPrefix_zeroCurvature_actual_producer :
    (emptyObjective 0).toReal + unitSupport ((1 : ℝ) - 0) +
      (0 / 2 : ℝ) * ‖(1 : ℝ) - 0‖ ^ 2 ≤ (emptyObjective 1).toReal ∧
    (SourceProper emptyObjective ∧ effectiveDomain emptyObjective = feasible ∧
      (∀ x ∈ feasible, emptyObjective x =
        ((linearRegularizer x + ∑ i ∈ range 0, (emptyLoss i x).toReal : ℝ) : EReal)) ∧
      (∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
        emptyObjective (a • x + (1 - a) • y) ≤
          (a : EReal) * emptyObjective x + ((1 - a : ℝ) : EReal) * emptyObjective y -
            (((0 / 2 : ℝ) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))) ∧
    (∀ z ∈ feasible,
      emptyObjective 0 + (unitSupport (z - 0) : EReal) ≤ emptyObjective z) ∧
    (emptyObjective 0).toReal + unitSupport ((1 : ℝ) - 0) +
      (0 / 2 : ℝ) * ‖(1 : ℝ) - 0‖ ^ 2 = 1 ∧
    (emptyObjective 1).toReal = 1 ∧ emptyObjective 2 = ⊤ ∧ emptyLoss 0 0 = ⊥ ∧
    ¬ SourceProper (fun x : ℝ =>
      (linearRegularizer x : EReal) + ∑ i ∈ range 1, emptyLoss i x +
        extendedIndicator feasible x) ∧
    ¬ IsMinOn emptyObjective feasible 0 := by
  have h0 : (0 : ℝ) ∈ feasible := by norm_num [feasible]
  have h1 : (1 : ℝ) ∈ feasible := by norm_num [feasible]
  have hm1 : (-1 : ℝ) ∈ feasible := by norm_num [feasible]
  have hpsi : StrongConvexOn feasible 0 linearRegularizer := by
    rw [strongConvexOn_zero]
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    simp [linearRegularizer]
  have hbot : ∀ i < 0, ∀ z, emptyLoss i z ≠ ⊥ := by
    intro i hi
    omega
  have hdom : ∀ i < 0, feasible ⊆ effectiveDomain (emptyLoss i) := by
    intro i hi
    omega
  have hloss : ∀ i < 0, ConvexOn ℝ feasible (fun z => (emptyLoss i z).toReal) := by
    intro i hi
    omega
  have package := cumulative_regularizer_source_strongConvex feasible ⟨0, h0⟩
    linearRegularizer emptyLoss 0 0 (by norm_num) hpsi hbot hdom hloss
  have hvalue (z : ℝ) (hz : z ∈ feasible) : emptyObjective z = (z : EReal) := by
    change (linearRegularizer z : EReal) + ∑ i ∈ range 0, emptyLoss i z +
      extendedIndicator feasible z = (z : EReal)
    simpa only [linearRegularizer, sum_range_zero, add_zero] using package.2.2.1 z hz
  have hs : ∀ z ∈ feasible,
      emptyObjective 0 + (unitSupport (z - 0) : EReal) ≤ emptyObjective z := by
    intro z hz
    rw [hvalue 0 h0, hvalue z hz]
    simp [unitSupport]
  have hg := stronglyConvex_support_growth emptyObjective feasible 0 package.1
    (convex_Icc _ _) (by have hd : effectiveDomain emptyObjective = feasible := package.2.1; rw [hd]) (by norm_num) package.2.2.2
    0 h0 unitSupport hs 1 h1
  refine ⟨hg, package, hs, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · rw [hvalue 0 h0]
    norm_num [unitSupport]
  · rw [hvalue 1 h1]
    norm_num
  · norm_num [emptyObjective, linearRegularizer, extendedIndicator, feasible]
  · intro hp
    have h := hp.1 0
    norm_num [linearRegularizer, emptyLoss, extendedIndicator, feasible, sum_range_succ] at h
  · intro hm
    have h := hm hm1
    change emptyObjective 0 ≤ emptyObjective (-1) at h
    rw [hvalue 0 h0, hvalue (-1) hm1, EReal.coe_le_coe_iff] at h
    norm_num at h


end BanditRL.Tests.OnlineCumulativeStrongConvexCanary
