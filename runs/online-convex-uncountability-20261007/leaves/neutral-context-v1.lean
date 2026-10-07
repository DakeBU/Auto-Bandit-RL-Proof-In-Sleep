import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality

def Q (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|
#check (¬ (segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1)).Countable)
#check (ConvexOn ℝ Set.univ Q ∧
  ¬ ({x : EuclideanSpace ℝ (Fin 2) | ¬ DifferentiableAt ℝ Q x}).Countable)
