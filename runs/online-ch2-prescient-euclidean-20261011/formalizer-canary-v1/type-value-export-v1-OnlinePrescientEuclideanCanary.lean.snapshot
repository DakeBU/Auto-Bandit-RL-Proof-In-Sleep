import BanditRLProof.OnlinePrescientEuclidean
import Tests.OnlineSubgradientBasicCanary
import Mathlib.Tactic

noncomputable section
open Set Finset
open BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
set_option autoImplicit false
namespace PrescientEuclideanProbe

theorem variable_quadratic_actual_run :
    let V : Set ℝ := Icc 0 2
    let loss : ℕ → ℝ → EReal := fun _ z =>
      if z ∈ V then ((z ^ 2 / 2 : ℝ) : EReal) else ⊤
    let η : ℕ → ℝ := fun t => if t = 0 then 1 else 1 / 2
    let x : ℕ → ℝ := fun t => if t = 0 then 2 else if t = 1 then 1 else 2 / 3
    Convex ℝ V ∧ V.Nonempty ∧ IsClosed V ∧
    (∀ t, SourceProper (loss t) ∧ IsConvexExtended (loss t) ∧
      effectiveDomain (loss t) = V) ∧
    (∀ t, ∀ z ∈ V, z ∈ SourceSubdifferential (loss t) z) ∧
    loss 0 3 = ⊤ ∧
    (loss 0 0).toReal + (loss 0 2).toReal ≠ 2 * (loss 0 1).toReal ∧
    (∀ t, 0 < η t) ∧ (∀ t, η (t + 1) ≤ η t) ∧
    η 0 = 1 ∧ η 1 = 1 / 2 ∧
    x 0 = 2 ∧ x 1 = 1 ∧ x 2 = 2 / 3 ∧
    (∀ t < 2, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((‖z - x t‖ ^ 2 / (2 * η t) : ℝ) : EReal))
        V (x (t + 1))) ∧
    (∀ t ≤ 2, iterate V (fun z : ℝ => ‖z‖ ^ 2 / 2) η loss 2 t = some (x t)) ∧
    (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t 0).toReal)) = 13 / 18 ∧
    (∑ t ∈ range 2, ((loss t (x t)).toReal - (loss t 0).toReal)) = 5 / 2 ∧
    ‖x 1 - x 0‖ ^ 2 / (2 * η 0) = 1 / 2 ∧
    ‖x 2 - x 1‖ ^ 2 / (2 * η 1) = 1 / 9 ∧
    (∑ t ∈ range 2, ‖x (t + 1) - x t‖ ^ 2 / (2 * η t)) = 11 / 18 ∧
    (∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      ((range 2).sup' (nonempty_range_iff.mpr (by decide : (2 : ℕ) ≠ 0))
        (fun t => ‖u - x t‖ ^ 2 / 2)) / η 1 -
      ∑ t ∈ range 2, ‖x (t + 1) - x t‖ ^ 2 / (2 * η t)) ∧
    (13 / 18 : ℝ) ≤ 61 / 18 := by
  classical
  dsimp only
  let V : Set ℝ := Icc 0 2
  let loss : ℕ → ℝ → EReal := fun _ z =>
    if z ∈ V then ((z ^ 2 / 2 : ℝ) : EReal) else ⊤
  let η : ℕ → ℝ := fun t => if t = 0 then 1 else 1 / 2
  let x : ℕ → ℝ := fun t => if t = 0 then 2 else if t = 1 then 1 else 2 / 3
  have hV : Convex ℝ V := convex_Icc 0 2
  have hVn : V.Nonempty := ⟨0, by norm_num [V]⟩
  have hVc : IsClosed V := isClosed_Icc
  have hzero : (0 : ℝ) ∈ V := by norm_num [V]
  have hbot (t : ℕ) (z : ℝ) : loss t z ≠ ⊥ := by
    by_cases hz : z ∈ V <;> simp [loss, hz]
  have hdom (t : ℕ) : effectiveDomain (loss t) = V := by
    ext z
    by_cases hz : z ∈ V <;> simp [effectiveDomain, loss, hz]
  have hp (t : ℕ) : SourceProper (loss t) :=
    sourceProper_of_domain (loss t) V hVn (hbot t) (by rw [hdom t])
  have hs (t : ℕ) (z : ℝ) (hz : z ∈ V) :
      z ∈ SourceSubdifferential (loss t) z := by
    intro y
    by_cases hy : y ∈ V
    · have hold := SubgradientProbe.square_support z y
      simp only [← EReal.coe_add, EReal.coe_le_coe_iff] at hold
      change z ^ 2 + (y - z) * (2 * z) ≤ y ^ 2 at hold
      simp only [loss, if_pos hz, if_pos hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      change z ^ 2 / 2 + (y - z) * z ≤ y ^ 2 / 2
      nlinarith only [hold]
    · simp only [loss, if_neg hy]
      exact le_top
  have hregular (t : ℕ) : SourceProper (loss t) ∧ IsConvexExtended (loss t) ∧
      effectiveDomain (loss t) = V := by
    refine ⟨hp t, ?_, hdom t⟩
    apply (convexExtended_iff_toReal (loss t) (hbot t)).mpr
    rw [hdom t]
    exact finitePart_convex_of_subdifferentiable (loss t) V hV (hp t)
      (fun z hz => ⟨z, hs t z hz⟩)
  have hη (t : ℕ) : 0 < η t := by
    by_cases ht : t = 0 <;> norm_num [η, ht]
  have hmono (t : ℕ) : η (t + 1) ≤ η t := by
    by_cases ht : t = 0 <;> simp [η, ht] <;> norm_num
  have hm : ∀ t < 2, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((‖z - x t‖ ^ 2 / (2 * η t) : ℝ) : EReal))
        V (x (t + 1)) := by
    intro t ht
    have ht01 : t = 0 ∨ t = 1 := by omega
    have hxp : x (t + 1) ∈ V := by
      rcases ht01 with rfl | rfl <;> norm_num [x, V]
    refine ⟨hxp, ?_⟩
    intro z hz
    change loss t (x (t + 1)) + _ ≤ loss t z + _
    dsimp only [loss]
    rw [if_pos hxp, if_pos hz, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    rcases ht01 with rfl | rfl
    · norm_num [x, η, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (z - 1)]
    · norm_num [x, η, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (z - (2 / 3 : ℝ))]
  have hcore (u : ℝ) (hu : u ∈ V) :=
    euclidean_variable_regret V hV hVn hVc η loss 2 x 2 (by decide)
      (fun t _ => hη t) (by norm_num [x]) (fun t _ => hmono t)
      (fun t _ z => hbot t z) (fun t _ => by rw [hdom t])
      (fun t _ z hz => ⟨z, hs t z hz⟩) hm u hu
  have hbound (u : ℝ) (hu : u ∈ V) := (hcore u hu).2
  have hnum : (13 / 18 : ℝ) ≤ 61 / 18 := by
    have hb := hbound 0 hzero
    convert hb using 1 <;>
      norm_num [show range 2 = {0, 1} from by decide, Finset.sup'_insert, Finset.sup'_singleton,
        loss, V, x, η, Real.norm_eq_abs]
  refine ⟨hV, hVn, hVc, hregular, hs, ?_, ?_, hη, hmono, ?_, ?_, ?_, ?_, ?_,
    hm, (hcore 0 hzero).1, ?_, ?_, ?_, ?_, ?_, hbound, hnum⟩ <;>
    norm_num [sum_range_succ, loss, V, x, η, Real.norm_eq_abs]

theorem fixed_quadratic_actual_run :
    let V : Set ℝ := Icc 0 2
    let loss : ℕ → ℝ → EReal := fun _ z =>
      if z ∈ V then ((z ^ 2 / 2 : ℝ) : EReal) else ⊤
    let η : ℕ → ℝ := fun _ => 1
    let x : ℕ → ℝ := fun t => if t = 0 then 2 else if t = 1 then 1 else 1 / 2
    Convex ℝ V ∧ V.Nonempty ∧ IsClosed V ∧
    (∀ t, SourceProper (loss t) ∧ IsConvexExtended (loss t) ∧
      effectiveDomain (loss t) = V) ∧
    (∀ t, ∀ z ∈ V, z ∈ SourceSubdifferential (loss t) z) ∧
    loss 0 3 = ⊤ ∧
    (loss 0 0).toReal + (loss 0 2).toReal ≠ 2 * (loss 0 1).toReal ∧
    (∀ t, 0 < η t) ∧ (∀ t, η (t + 1) ≤ η t) ∧
    η 0 = 1 ∧ η 1 = 1 ∧
    x 0 = 2 ∧ x 1 = 1 ∧ x 2 = 1 / 2 ∧
    (∀ t < 2, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((‖z - x t‖ ^ 2 / (2 * η t) : ℝ) : EReal))
        V (x (t + 1))) ∧
    (∀ t ≤ 2, iterate V (fun z : ℝ => ‖z‖ ^ 2 / 2) η loss 2 t = some (x t)) ∧
    (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t 0).toReal)) = 5 / 8 ∧
    (∑ t ∈ range 2, ((loss t (x t)).toReal - (loss t 0).toReal)) = 5 / 2 ∧
    ‖x 1 - x 0‖ ^ 2 / (2 * η 0) = 1 / 2 ∧
    ‖x 2 - x 1‖ ^ 2 / (2 * η 1) = 1 / 8 ∧
    (∑ t ∈ range 2, ‖x (t + 1) - x t‖ ^ 2 / (2 * η t)) = 5 / 8 ∧
    (∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      ‖u - (2 : ℝ)‖ ^ 2 / (2 * 1) -
      (∑ t ∈ range 2, ‖x (t + 1) - x t‖ ^ 2) / (2 * 1)) ∧
    (5 / 8 : ℝ) ≤ 11 / 8 := by
  classical
  dsimp only
  let V : Set ℝ := Icc 0 2
  let loss : ℕ → ℝ → EReal := fun _ z =>
    if z ∈ V then ((z ^ 2 / 2 : ℝ) : EReal) else ⊤
  let η : ℕ → ℝ := fun _ => 1
  let x : ℕ → ℝ := fun t => if t = 0 then 2 else if t = 1 then 1 else 1 / 2
  have hV : Convex ℝ V := convex_Icc 0 2
  have hVn : V.Nonempty := ⟨0, by norm_num [V]⟩
  have hVc : IsClosed V := isClosed_Icc
  have hzero : (0 : ℝ) ∈ V := by norm_num [V]
  have hbot (t : ℕ) (z : ℝ) : loss t z ≠ ⊥ := by
    by_cases hz : z ∈ V <;> simp [loss, hz]
  have hdom (t : ℕ) : effectiveDomain (loss t) = V := by
    ext z
    by_cases hz : z ∈ V <;> simp [effectiveDomain, loss, hz]
  have hp (t : ℕ) : SourceProper (loss t) :=
    sourceProper_of_domain (loss t) V hVn (hbot t) (by rw [hdom t])
  have hs (t : ℕ) (z : ℝ) (hz : z ∈ V) :
      z ∈ SourceSubdifferential (loss t) z := by
    intro y
    by_cases hy : y ∈ V
    · have hold := SubgradientProbe.square_support z y
      simp only [← EReal.coe_add, EReal.coe_le_coe_iff] at hold
      change z ^ 2 + (y - z) * (2 * z) ≤ y ^ 2 at hold
      simp only [loss, if_pos hz, if_pos hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      change z ^ 2 / 2 + (y - z) * z ≤ y ^ 2 / 2
      nlinarith only [hold]
    · simp only [loss, if_neg hy]
      exact le_top
  have hregular (t : ℕ) : SourceProper (loss t) ∧ IsConvexExtended (loss t) ∧
      effectiveDomain (loss t) = V := by
    refine ⟨hp t, ?_, hdom t⟩
    apply (convexExtended_iff_toReal (loss t) (hbot t)).mpr
    rw [hdom t]
    exact finitePart_convex_of_subdifferentiable (loss t) V hV (hp t)
      (fun z hz => ⟨z, hs t z hz⟩)
  have hη (t : ℕ) : 0 < η t := by
    norm_num [η]
  have hmono (t : ℕ) : η (t + 1) ≤ η t := by
    norm_num [η]
  have hm : ∀ t < 2, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((‖z - x t‖ ^ 2 / (2 * η t) : ℝ) : EReal))
        V (x (t + 1)) := by
    intro t ht
    have ht01 : t = 0 ∨ t = 1 := by omega
    have hxp : x (t + 1) ∈ V := by
      rcases ht01 with rfl | rfl <;> norm_num [x, V]
    refine ⟨hxp, ?_⟩
    intro z hz
    change loss t (x (t + 1)) + _ ≤ loss t z + _
    dsimp only [loss]
    rw [if_pos hxp, if_pos hz, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    rcases ht01 with rfl | rfl
    · norm_num [x, η, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (z - 1)]
    · norm_num [x, η, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (z - (1 / 2 : ℝ))]
  have hcore (u : ℝ) (hu : u ∈ V) :=
    euclidean_fixed_regret V hV hVn hVc 1 (by norm_num) loss 2 x 2
      (by norm_num [x]) (fun t _ z => hbot t z) (fun t _ => by rw [hdom t])
      (fun t _ z hz => ⟨z, hs t z hz⟩) hm u hu
  have hbound (u : ℝ) (hu : u ∈ V) := (hcore u hu).2
  have hnum : (5 / 8 : ℝ) ≤ 11 / 8 := by
    have hb := hbound 0 hzero
    convert hb using 1 <;> norm_num [sum_range_succ, loss, V, x, η, Real.norm_eq_abs]
  refine ⟨hV, hVn, hVc, hregular, hs, ?_, ?_, hη, hmono, ?_, ?_, ?_, ?_, ?_,
    hm, (hcore 0 hzero).1, ?_, ?_, ?_, ?_, ?_, hbound, hnum⟩ <;>
    norm_num [sum_range_succ, loss, V, x, η, Real.norm_eq_abs]

end PrescientEuclideanProbe
