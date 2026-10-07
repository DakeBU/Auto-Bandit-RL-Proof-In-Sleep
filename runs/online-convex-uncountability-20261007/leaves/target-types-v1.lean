import BanditRLProof.OnlineConvexNondifferentiability
import Mathlib.Analysis.Real.Cardinality

namespace BanditRL.OnlineConvex
#check (¬ (segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1)).Countable)
#check (ConvexOn ℝ Set.univ coordinateAbsolute ∧ ¬ ({x : EuclideanSpace ℝ (Fin 2) | ¬ DifferentiableAt ℝ coordinateAbsolute x}).Countable)
#print coordinateAbsolute
end BanditRL.OnlineConvex
