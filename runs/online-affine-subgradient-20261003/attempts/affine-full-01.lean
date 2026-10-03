import BanditRLProof.OnlineSubgradientBasic
import Mathlib.Analysis.InnerProductSpace.Adjoint
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

#print axioms BanditRL.OnlineConvex.theorem_2_28
end BanditRL.OnlineConvex
