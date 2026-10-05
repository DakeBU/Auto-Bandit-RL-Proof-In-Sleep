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

end BanditRL.OnlineGradientDescentSource
