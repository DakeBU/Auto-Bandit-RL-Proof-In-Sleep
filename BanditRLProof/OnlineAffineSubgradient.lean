import BanditRLProof.OnlineSubgradientBasic
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!
# Affine transport of global subgradients
Orabona arXiv:1912.13213v10, Theorem 2.28, printed 18 / PDF 30.
For an arbitrary proper extended-real function, transport a global support
through the actual affine map and its adjoint. Only inclusion is claimed;
convexity and properness of the composite are not additional assumptions.
The shared all-point support definition is used literally even if the
composite is identically top; that case has an empty source image.
-/
noncomputable section
open Set
namespace BanditRL.OnlineConvex
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem theorem_2_28 [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : F → EReal) (hp : SourceProper f) (A : E →L[ℝ] F) (b : F) (x : E) :
    A.adjoint '' (SourceSubdifferential f (A x + b)) ⊆
      SourceSubdifferential (fun y => f (A y + b)) x := by
  intro q hq
  rcases hq with ⟨g, hg, rfl⟩
  intro y
  have hi := hg (A y + b)
  have hm : (A y + b) - (A x + b) = A (y - x) := by
    rw [A.map_sub]
    abel
  rw [hm, ← ContinuousLinearMap.adjoint_inner_left A (y - x) g] at hi
  exact hi

end BanditRL.OnlineConvex
