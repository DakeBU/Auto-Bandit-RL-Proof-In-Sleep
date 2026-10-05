import BanditRLProof.OnlineGradientDescentVariable
import BanditRLProof.OnlineConvexFirstOrder
import Mathlib.Tactic

/-!
# Projected OGD with source regularity

Orabona, arXiv:1912.13213v10, Algorithm 2.1, Lemma 2.12, both branches of
Theorem 2.13, and Eq. (2.1). The loss is convex on the feasible set and has
a specified differentiable ambient extension on an arbitrary open neighborhood.
That neighborhood need not be convex. The existing projected algorithms are
reused, with Lean time zero corresponding to source round one.
-/

noncomputable section
open Set Finset
open scoped InnerProductSpace
namespace BanditRL.OnlineGradientDescentSource
open BanditRL.OnlineGradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Convexity on the feasible set and ambient derivatives at every feasible point. -/
def FeasibleRegularLoss (V : Domain E) (f : E → ℝ) : Prop :=
  ConvexOn ℝ V.carrier f ∧ ∀ x ∈ V.carrier, DifferentiableAt ℝ f x

/-- Source regularity for the supplied ambient extension. No convexity of `U` is required. -/
def SourceRegularLoss (V : Domain E) (f : E → ℝ) : Prop :=
  ∃ U : Set E, IsOpen U ∧ V.carrier ⊆ U ∧
    ConvexOn ℝ V.carrier f ∧ DifferentiableOn ℝ f U

/-- The arbitrary open differentiability neighborhood supplies each ambient derivative. -/
theorem source_to_feasible (V : Domain E) (f : E → ℝ) (hf : SourceRegularLoss V f) :
    FeasibleRegularLoss V f := by
  rcases hf with ⟨U, hU, hVU, hconv, hdiff⟩
  exact ⟨hconv, fun x hx => hdiff.differentiableAt (hU.mem_nhds (hVU hx))⟩

/-- Compatibility with the historical stronger convex-neighborhood interface; forward only. -/
theorem regular_to_feasible (V : Domain E) (f : E → ℝ) (hf : RegularLoss V f) :
    FeasibleRegularLoss V f := by
  rcases hf with ⟨U, hU, hVU, hconv, hdiff⟩
  exact ⟨hconv.subset hVU V.convex,
    fun x hx => hdiff.differentiableAt (hU.mem_nhds (hVU hx))⟩

/-- The genuine affine specialization satisfies the historical stronger interface. -/
theorem linear_regular (V : Domain E) (g : E) : RegularLoss V (fun z => inner ℝ g z) := by
  refine ⟨univ, isOpen_univ, subset_univ _, ?_, ?_⟩
  · simpa only [InnerProductSpace.toDual_apply_apply] using
      (InnerProductSpace.toDual ℝ E g).toLinearMap.convexOn convex_univ
  · simpa only [InnerProductSpace.toDual_apply_apply] using
      (InnerProductSpace.toDual ℝ E g).differentiable.differentiableOn

/-- The affine loss uses the specified vector as its actual gradient. -/
theorem gradient_linear (g x : E) : gradient (fun z => inner ℝ g z) x = g := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [InnerProductSpace.toDual_apply_apply] using
    (InnerProductSpace.toDual ℝ E g).hasFDerivAt (x := x)

/-- Convexity on the feasible set produces the first-order loss comparison. -/
theorem first_order (V : Domain E) (f : E → ℝ) (hf : FeasibleRegularLoss V f)
    (x u : E) (hx : x ∈ V.carrier) (hu : u ∈ V.carrier) :
    f x - f u ≤ inner ℝ (gradient f x) (x - u) := by
  have hb := BanditRL.OnlineConvex.convex_gradient_lower_bound V.carrier f hf.1
    x u hx hu (hf.2 x hx)
  rw [show u - x = -(x - u) by abel, inner_neg_right] at hb
  linarith

/-- Both one-step inequalities hold for the same original projected update. -/
theorem lemma_2_12 (V : Domain E) (f : E → ℝ) (hf : FeasibleRegularLoss V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hx : x ∈ V.carrier) (hu : u ∈ V.carrier) :
    η * (f x - f u) ≤ η * inner ℝ (gradient f x) (x - u) ∧
    η * inner ℝ (gradient f x) (x - u) ≤
      ‖x - u‖ ^ 2 / 2 - ‖step V η f x - u‖ ^ 2 / 2 +
        η ^ 2 / 2 * ‖gradient f x‖ ^ 2 := by
  refine ⟨mul_le_mul_of_nonneg_left (first_order V f hf x u hx hu) hη.le, ?_⟩
  have hs := (BanditRL.OnlineGradientDescent.lemma_2_12 V
    (fun z => inner ℝ (gradient f x) z) (linear_regular V (gradient f x)) η hη
    x u hx hu).2
  simpa only [step, gradient_linear] using hs

/-- Fixed-step telescope on the actual recurrence; no bounded-domain premise. -/
theorem theorem_2_13_fixed (V : Domain E) (η : ℝ) (hη : 0 < η) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) : regret V η loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) + η / 2 * (∑ t ∈ range T, ‖gradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) - ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η) := by
  have hscaled : η * regret V η loss x₁ u T ≤
      ‖x₁ - u‖ ^ 2 / 2 - ‖iterate V η loss x₁ T - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * (∑ t ∈ range T, ‖gradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) := by
    induction T with
    | zero => simp [regret, iterate]
    | succ T ih =>
      have hi := ih (fun t ht => hloss t (Nat.lt_succ_of_lt ht))
      have hs := lemma_2_12 V (loss T) (hloss T (Nat.lt_succ_self T)) η hη
        (iterate V η loss x₁ T) u (iterate_mem V η loss x₁ hx₁ T) hu
      simp only [regret, sum_range_succ, mul_add] at hi ⊢
      change _ ≤ _ - ‖step V η (loss T) (iterate V η loss x₁ T) - u‖ ^ 2 / 2 + _
      nlinarith [hs.1.trans hs.2]
  apply le_of_mul_le_mul_left (a := η) _ hη
  calc
    η * regret V η loss x₁ u T ≤ _ := hscaled
    _ = η * (‖x₁ - u‖ ^ 2 / (2 * η) +
        η / 2 * (∑ t ∈ range T, ‖gradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
        ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η)) := by field_simp; ring

/-- The current actual scheduled update supplies the divided one-step inequality. -/
theorem variable_one_step (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (hη : 0 < η t) (hloss : FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) : loss t (iterateVariable V η loss x₁ t) - loss t u ≤ (‖iterateVariable V η loss x₁ t - u‖ ^ 2 - ‖iterateVariable V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) + η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2 := by
  have hs := lemma_2_12 V (loss t) hloss (η t) hη
    (iterateVariable V η loss x₁ t) u (iterateVariable_mem V η loss x₁ hx₁ t) hu
  apply le_of_mul_le_mul_left (a := η t) _ hη
  calc
    η t * (loss t (iterateVariable V η loss x₁ t) - loss t u) ≤
        ‖iterateVariable V η loss x₁ t - u‖ ^ 2 / 2 -
        ‖iterateVariable V η loss x₁ (t + 1) - u‖ ^ 2 / 2 +
        (η t) ^ 2 / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2 :=
      hs.1.trans hs.2
    _ = η t * ((‖iterateVariable V η loss x₁ t - u‖ ^ 2 -
        ‖iterateVariable V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) +
        η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) := by
      field_simp

/-- The weighted potential telescope retains the negative terminal at the last played step. -/
theorem theorem_2_13_variable_bound (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (D : ℝ) (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) : regretVariable V η loss x₁ u T ≤ D ^ 2 / (2 * η (T - 1)) + (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) - ‖iterateVariable V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1)) := by
  have hp := weighted_potential_sum
    (fun t => ‖iterateVariable V η loss x₁ t - u‖ ^ 2) η (D ^ 2) T hT hη hmono
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _)
      (hdiam _ (iterateVariable_mem V η loss x₁ hx₁ t) u hu) 2)
  have hs := Finset.sum_le_sum (s := range T) (fun t ht =>
    variable_one_step V η loss x₁ hx₁ t (hη t (mem_range.mp ht))
      (hloss t (mem_range.mp ht)) u hu)
  rw [sum_add_distrib] at hs
  change regretVariable V η loss x₁ u T ≤ _ at hs
  linarith

/-- The bounded-set diameter supplies the source finite-diameter bound. -/
theorem theorem_2_13_variable (V : Domain E) (hV : Bornology.IsBounded V.carrier) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) : regretVariable V η loss x₁ u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) + (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) - ‖iterateVariable V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1)) := by
  apply theorem_2_13_variable_bound V η loss x₁ hx₁ T hT hη hmono hloss
    (Metric.diam V.carrier) ?_ u hu
  intro x hx y hy
  simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hV hx hy

/-- Positive horizon tuning uses gradients of this same tuned trajectory. -/
theorem equation_2_1_distance (V : Domain E) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) (hdist : ‖x₁ - u‖ ≤ D) (hgrad : ∀ t < T, ‖gradient (loss t) (iterate V (D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G) : regret V (D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T := by
  have hTreal : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hTreal
  have hη : 0 < D / (G * Real.sqrt T) := div_pos hD (mul_pos hG hsqrt)
  have hb := theorem_2_13_fixed V (D / (G * Real.sqrt T)) hη loss x₁ hx₁ T hloss u hu
  have hdist2 : ‖x₁ - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hsum : (∑ t ∈ range T,
      ‖gradient (loss t) (iterate V (D / (G * Real.sqrt T)) loss x₁ t)‖ ^ 2) ≤
      (T : ℝ) * G ^ 2 := by
    calc
      _ ≤ ∑ _t ∈ range T, G ^ 2 := sum_le_sum fun t ht =>
        pow_le_pow_left₀ (norm_nonneg _) (hgrad t (mem_range.mp ht)) 2
      _ = _ := by simp
  have hinit := div_le_div_of_nonneg_right hdist2 (by positivity :
    0 ≤ 2 * (D / (G * Real.sqrt T)))
  have henergy := mul_le_mul_of_nonneg_left hsum (by positivity :
    0 ≤ (D / (G * Real.sqrt T)) / 2)
  have hterminal : 0 ≤ ‖iterate V (D / (G * Real.sqrt T)) loss x₁ T - u‖ ^ 2 /
      (2 * (D / (G * Real.sqrt T))) := by positivity
  have htune : D ^ 2 / (2 * (D / (G * Real.sqrt T))) +
      (D / (G * Real.sqrt T)) / 2 * ((T : ℝ) * G ^ 2) = D * G * Real.sqrt T := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg T)
    field_simp
    nlinarith
  linarith

/-- One horizon-tuned learner satisfies the bound for every feasible comparator. -/
theorem equation_2_1 (V : Domain E) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G) (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (hgrad : ∀ t < T, ‖gradient (loss t) (iterate V (D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G) : ∀ u ∈ V.carrier, regret V (D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T := by
  intro u hu
  exact equation_2_1_distance V loss x₁ hx₁ T hT D G hD hG hloss u hu (hdiam x₁ hx₁ u hu) hgrad

end BanditRL.OnlineGradientDescentSource
