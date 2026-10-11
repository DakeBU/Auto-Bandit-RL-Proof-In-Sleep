import BanditRLProof.OnlinePrescientBregmanSource
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic

noncomputable section
open Set Finset
open BanditRL.OnlineBregman
set_option autoImplicit false

namespace BanditRL.OnlineBregman

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem quadratic_geometry (x y : E) :
    HasGradientAt (fun z : E => ‖z‖ ^ 2 / 2) y y ∧
    divergence (fun z : E => ‖z‖ ^ 2 / 2) x y = ‖x - y‖ ^ 2 / 2 := by
  have hg : HasGradientAt (fun z : E => ‖z‖ ^ 2 / 2) y y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_smul (1 / 2 : ℝ)) using 1
    · ext z
      change ‖z‖ ^ 2 / 2 = (1 / 2 : ℝ) * ‖z‖ ^ 2
      ring
    · ext z
      simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply,
        InnerProductSpace.toDual_apply_apply, smul_eq_mul]
      ring
  refine ⟨hg, ?_⟩
  rw [divergence, hg.fderiv_apply]
  rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real]
  rw [real_inner_comm y x]
  ring

end BanditRL.OnlineBregman

namespace BanditRL.OnlinePrescientBregman

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem euclidean_variable_regret (V : Set E) (hV : Convex ℝ V)
    (hVn : V.Nonempty) (hVc : IsClosed V)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x0 : E) (x : ℕ → E) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hinit : x 0 = x0)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hbot : ∀ t < T, ∀ z, loss t z ≠ ⊥)
    (hdom : ∀ t < T, V ⊆ BanditRL.OnlineConvex.effectiveDomain (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((‖z - x t‖ ^ 2 / (2 * η t) : ℝ) : EReal))
        V (x (t + 1))) (u : E) (hu : u ∈ V) :
    (∀ t ≤ T, iterate V (fun z : E => ‖z‖ ^ 2 / 2) η loss x0 t = some (x t)) ∧
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      ((range T).sup' (nonempty_range_iff.mpr (Nat.ne_of_gt hT))
        (fun t => ‖u - x t‖ ^ 2 / 2)) / η (T - 1) -
      ∑ t ∈ range T, ‖x (t + 1) - x t‖ ^ 2 / (2 * η t) := by
  classical
  let ψ : E → ℝ := fun z => ‖z‖ ^ 2 / 2
  have hgeometry (a b : E) : divergence ψ a b = ‖a - b‖ ^ 2 / 2 :=
    (quadratic_geometry a b).2
  have hψ : StrictConvexOn ℝ (univ : Set E) ψ := by
    have hstrong : StrongConvexOn (univ : Set E) 1 ψ := by
      rw [strongConvexOn_iff_convex]
      have he : (fun z : E => ψ z - (1 : ℝ) / 2 * ‖z‖ ^ 2) = fun _ => (0 : ℝ) := by
        funext z
        dsimp [ψ]
        ring
      rw [he]
      exact convexOn_const 0 convex_univ
    exact hstrong.strictConvexOn (by norm_num)
  have hd : DifferentiableOn ℝ ψ (interior (univ : Set E)) := by
    intro z _
    exact (quadratic_geometry z z).1.hasFDerivAt.differentiableAt.differentiableWithinAt
  have hc : Continuous ψ :=
    (show Differentiable ℝ ψ from fun z =>
      (quadratic_geometry z z).1.hasFDerivAt.differentiableAt).continuous
  have hclosed : BanditRL.OnlineConvex.SourceClosed (fun z =>
      (ψ z : EReal) + BanditRL.OnlineConvex.extendedIndicator univ z) := by
    intro a
    simpa only [BanditRL.OnlineConvex.extendedIndicator, mem_univ, if_true,
      EReal.coe_zero, add_zero, EReal.coe_le_coe_iff] using
      (isClosed_le hc (continuous_const : Continuous (fun _ : E => a)))
  have hf (t : ℕ) (ht : t < T) : BanditRL.OnlineConvex.SourceProper (loss t) :=
    BanditRL.OnlineConvex.sourceProper_of_domain (loss t) V hVn (hbot t ht) (hdom t ht)

  have hm : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1)) := by
    intro t ht
    simpa only [hgeometry, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
      mul_assoc] using hmin t ht
  have hrun := iterate_eq_of_source_updates V univ hV (fun _ _ => mem_univ _)
    ψ hψ η loss x0 x T hinit hη hf hs hm
  refine ⟨hrun, ?_⟩
  have hb := source_variable_regret V univ hV hVn hVc (fun _ _ => mem_univ _)
    ψ hψ hclosed hd η loss x0 x T hT hη hinit (by simp) hmono hbot hdom hs hm u hu
  simpa only [hgeometry, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
    mul_assoc] using hb

theorem euclidean_fixed_regret (V : Set E) (hV : Convex ℝ V)
    (hVn : V.Nonempty) (hVc : IsClosed V)
    (η : ℝ) (hη : 0 < η) (loss : ℕ → E → EReal)
    (x0 : E) (x : ℕ → E) (T : ℕ) (hinit : x 0 = x0)
    (hbot : ∀ t < T, ∀ z, loss t z ≠ ⊥)
    (hdom : ∀ t < T, V ⊆ BanditRL.OnlineConvex.effectiveDomain (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((‖z - x t‖ ^ 2 / (2 * η) : ℝ) : EReal))
        V (x (t + 1))) (u : E) (hu : u ∈ V) :
    (∀ t ≤ T, iterate V (fun z : E => ‖z‖ ^ 2 / 2) (fun _ => η) loss x0 t = some (x t)) ∧
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      ‖u - x0‖ ^ 2 / (2 * η) -
      (∑ t ∈ range T, ‖x (t + 1) - x t‖ ^ 2) / (2 * η) := by
  classical
  let ψ : E → ℝ := fun z => ‖z‖ ^ 2 / 2
  have hgeometry (a b : E) : divergence ψ a b = ‖a - b‖ ^ 2 / 2 :=
    (quadratic_geometry a b).2
  have hψ : StrictConvexOn ℝ (univ : Set E) ψ := by
    have hstrong : StrongConvexOn (univ : Set E) 1 ψ := by
      rw [strongConvexOn_iff_convex]
      have he : (fun z : E => ψ z - (1 : ℝ) / 2 * ‖z‖ ^ 2) = fun _ => (0 : ℝ) := by
        funext z
        dsimp [ψ]
        ring
      rw [he]
      exact convexOn_const 0 convex_univ
    exact hstrong.strictConvexOn (by norm_num)
  have hd : DifferentiableOn ℝ ψ (interior (univ : Set E)) := by
    intro z _
    exact (quadratic_geometry z z).1.hasFDerivAt.differentiableAt.differentiableWithinAt
  have hc : Continuous ψ :=
    (show Differentiable ℝ ψ from fun z =>
      (quadratic_geometry z z).1.hasFDerivAt.differentiableAt).continuous
  have hclosed : BanditRL.OnlineConvex.SourceClosed (fun z =>
      (ψ z : EReal) + BanditRL.OnlineConvex.extendedIndicator univ z) := by
    intro a
    simpa only [BanditRL.OnlineConvex.extendedIndicator, mem_univ, if_true,
      EReal.coe_zero, add_zero, EReal.coe_le_coe_iff] using
      (isClosed_le hc (continuous_const : Continuous (fun _ : E => a)))
  have hf (t : ℕ) (ht : t < T) : BanditRL.OnlineConvex.SourceProper (loss t) :=
    BanditRL.OnlineConvex.sourceProper_of_domain (loss t) V hVn (hbot t ht) (hdom t ht)

  have hm : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((η⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1)) := by
    intro t ht
    simpa only [hgeometry, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
      mul_assoc] using hmin t ht
  have hrun := iterate_eq_of_source_updates V univ hV (fun _ _ => mem_univ _)
    ψ hψ (fun _ => η) loss x0 x T hinit (fun _ _ => hη) hf hs hm
  refine ⟨hrun, ?_⟩
  have hb := source_fixed_regret V univ hV hVn hVc (fun _ _ => mem_univ _)
    ψ hψ hclosed hd η hη loss x0 x T hinit (by simp) hbot hdom hs hm u hu
  simp only [hgeometry] at hb
  have hsum : (∑ t ∈ range T, ‖x (t + 1) - x t‖ ^ 2 / 2) =
      (∑ t ∈ range T, ‖x (t + 1) - x t‖ ^ 2) / 2 := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [hsum] at hb
  simpa only [div_div, mul_comm] using hb

end BanditRL.OnlinePrescientBregman
