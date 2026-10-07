import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Normed.Module.Convex

namespace BanditRL.OnlineConvex
def coordinateAbsolute (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|
end BanditRL.OnlineConvex
