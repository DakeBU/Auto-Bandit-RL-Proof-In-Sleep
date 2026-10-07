import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Normed.Module.Convex

namespace BanditRL.OnlineConvex
def coordinateAbsolute (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|
#check (ConvexOn ℝ Set.univ coordinateAbsolute)
#check (∀ x : EuclideanSpace ℝ (Fin 2), x 0 = 0 → ¬ DifferentiableAt ℝ coordinateAbsolute x)
#check (ConvexOn ℝ Set.univ coordinateAbsolute ∧ ∀ x ∈ segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1), ¬ DifferentiableAt ℝ coordinateAbsolute x)
#print coordinateAbsolute
end BanditRL.OnlineConvex
