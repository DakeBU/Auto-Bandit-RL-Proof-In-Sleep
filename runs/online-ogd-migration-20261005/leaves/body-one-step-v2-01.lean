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

end BanditRL.OnlineGradientDescentSource
