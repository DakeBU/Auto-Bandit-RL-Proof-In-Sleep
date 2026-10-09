import BanditRLProof.OnlinePrescientBregman
import Tests.OnlineBregmanExtendedCanary
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Set BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregmanCanary

theorem closed_strict_regularizer_missing_minimum :
    let V : Set ℝ := Iic 0
    let f : ℝ → EReal := fun z => (z : EReal)
    let ψ : ℝ → ℝ := Real.exp
    V.Nonempty ∧ IsClosed V ∧ Convex ℝ V ∧ (0 : ℝ) ∈ V ∧
      SourceProper f ∧
      (∀ z : ℝ, (SourceSubdifferential f z).Nonempty) ∧
      SourceClosed (fun z => ((ψ z : ℝ) : EReal)) ∧
      StrictConvexOn ℝ univ ψ ∧
      (∀ z : ℝ, DifferentiableAt ℝ ψ z) ∧
      (0 : ℝ) ∈ interior (univ : Set ℝ) ∧
      (∀ z : ℝ, f z + ((divergence ψ z 0 : ℝ) : EReal) = ((Real.exp z - 1 : ℝ) : EReal)) ∧
      (¬ ∃ p, p ∈ V ∧ IsMinOn (fun z => f z + ((divergence ψ z 0 : ℝ) : EReal)) V p) ∧
      advance V ψ 1 f 0 = none ∧
      (∀ k : ℕ, iterate V ψ (fun _ => 1) (fun _ => f) 0 (k + 1) = none) := by
  dsimp only
  let V : Set ℝ := Iic 0
  let f : ℝ → EReal := fun z => (z : EReal)
  let ψ : ℝ → ℝ := Real.exp
  have hf : SourceProper f := ⟨fun z => EReal.coe_ne_bot z, 0, 0, rfl⟩
  have hs : ∀ z : ℝ, (SourceSubdifferential f z).Nonempty := by
    intro z
    refine ⟨1, ?_⟩
    intro y
    change (z : EReal) + (inner ℝ (1 : ℝ) (y - z) : EReal) ≤ (y : EReal)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    change z + (y - z) * 1 ≤ y
    linarith
  have hc : SourceClosed (fun z => ((ψ z : ℝ) : EReal)) := by
    intro r
    change IsClosed {z : ℝ | (Real.exp z : EReal) ≤ (r : EReal)}
    simpa only [EReal.coe_le_coe_iff] using
      (isClosed_le Real.continuous_exp (continuous_const : Continuous (fun _ : ℝ => r)))
  have hD (z : ℝ) : divergence ψ z 0 = Real.exp z - 1 - z := by
    rw [divergence, fderiv_eq_deriv_mul]
    simp only [ψ, Real.deriv_exp, Real.exp_zero, sub_zero, one_mul]
  have hO (z : ℝ) : f z + ((divergence ψ z 0 : ℝ) : EReal) =
      ((Real.exp z - 1 : ℝ) : EReal) := by
    change (z : EReal) + ((divergence ψ z 0 : ℝ) : EReal) = _
    rw [← EReal.coe_add, hD]
    congr 1
    ring
  have hn : ¬ ∃ p, p ∈ V ∧
      IsMinOn (fun z => f z + ((divergence ψ z 0 : ℝ) : EReal)) V p := by
    rintro ⟨p, hp, hm⟩
    have hpm : p - 1 ∈ V := by
      change p - 1 ≤ 0
      change p ≤ 0 at hp
      linarith
    have hh := hm hpm
    change f p + ((divergence ψ p 0 : ℝ) : EReal) ≤
      f (p - 1) + ((divergence ψ (p - 1) 0 : ℝ) : EReal) at hh
    rw [hO, hO, EReal.coe_le_coe_iff] at hh
    have he : Real.exp (p - 1) < Real.exp p := Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hnone : advance V ψ 1 f 0 = none := by
    apply (advance_none_iff V ψ 1 f 0).mpr
    simpa only [inv_one, one_mul] using hn
  have h1 : iterate V ψ (fun _ => 1) (fun _ => f) 0 1 = none := by
    change advance V ψ 1 f 0 = none
    exact hnone
  refine ⟨⟨0, by norm_num [V]⟩, isClosed_Iic, convex_Iic 0, by norm_num [V], hf, hs, hc,
    strictConvexOn_exp, Real.differentiable_exp, by simp, hO, hn, hnone, ?_⟩
  intro k
  simpa only [Nat.add_comm] using
    iterate_no_recovery V ψ (fun _ => 1) (fun _ => f) 0 1 k h1

theorem interior_extension_boundary_difference :
    let X : Set ℝ := Ici 0
    let ψ : ℝ → ℝ := fun z => z ^ 2 + z
    let φ : ℝ → ℝ := fun z => z ^ 2 + |z|
    EqOn ψ φ X ∧ ψ (-1) ≠ φ (-1) ∧ (1 : ℝ) ∈ interior X ∧ (2 : ℝ) ∈ X ∧
      divergence ψ 2 1 = divergence φ 2 1 ∧ divergence ψ 2 1 = 1 ∧
      divergence ψ 2 0 = 4 ∧ divergence φ 2 0 = 6 ∧ ¬ DifferentiableAt ℝ φ 0 := by
  dsimp only
  let X : Set ℝ := Ici 0
  let ψ : ℝ → ℝ := fun z => z ^ 2 + z
  let φ : ℝ → ℝ := fun z => z ^ 2 + |z|
  have he : EqOn ψ φ X := by
    intro z hz
    change 0 ≤ z at hz
    simp only [ψ, φ, abs_of_nonneg hz]
  have hi : (1 : ℝ) ∈ interior X := by norm_num [X, interior_Ici]
  have ht : (2 : ℝ) ∈ X := by norm_num [X]
  have hd (z : ℝ) : HasDerivAt ψ (2 * z + 1) z := by
    convert ((hasDerivAt_id z).pow 2).add (hasDerivAt_id z) using 1
    dsimp [ψ, id]
    ring
  have hD (a b : ℝ) : divergence ψ a b = (a - b) ^ 2 := by
    rw [divergence, fderiv_eq_deriv_mul, (hd b).deriv]
    dsimp [ψ]
    ring
  have hn : ¬ DifferentiableAt ℝ φ 0 := by
    intro h
    apply not_differentiableAt_abs_zero
    have hh := h.sub (((hasDerivAt_id (0 : ℝ)).pow 2).differentiableAt)
    convert hh using 1
    ext z
    simp [φ]
  have hb : divergence φ 2 0 = 6 := by
    rw [divergence, fderiv_zero_of_not_differentiableAt hn]
    norm_num [φ]
  refine ⟨he, by norm_num [ψ, φ], hi, ht,
    divergence_extension_eq X ψ φ he 2 1 ht hi, ?_, ?_, hb, hn⟩
  · rw [hD]
    norm_num
  · rw [hD]
    norm_num

end BanditRL.OnlinePrescientBregmanCanary
