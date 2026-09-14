import BanditRLProof.OnlineLearningHistory
import Mathlib.Probability.ProbabilityMassFunction.Constructions
open MeasureTheory ProbabilityTheory BanditRL.OnlineLearning

namespace OnlineLearningProbabilityCanary
noncomputable def coin : PMF Bool := PMF.bernoulli (1/2) (by norm_num)
noncomputable def coinMeasure : Measure Bool := coin.toMeasure
instance : IsProbabilityMeasure coinMeasure := by unfold coinMeasure; infer_instance
def observation (b : Bool) : ℝ := if b then 1 else 0

example : coin true = 1/2 ∧ coin false = 1/2 := by
  norm_num [coin, PMF.bernoulli_apply]

example : (∫ b, observation b ∂coinMeasure) ∈ Set.Icc (0:ℝ) 1 ∧
    (∫ b, ((∫ b, observation b ∂coinMeasure) - observation b)^2 ∂coinMeasure) =
      variance observation coinMeasure ∧
    ∀ u : ℝ, variance observation coinMeasure ≤ ∫ b, (u - observation b)^2 ∂coinMeasure := by
  apply source_mean_optimal
  · exact measurable_of_countable observation
  · intro b
    cases b <;> norm_num [observation]

#print axioms BanditRL.OnlineLearning.history_policy_independent
end OnlineLearningProbabilityCanary
