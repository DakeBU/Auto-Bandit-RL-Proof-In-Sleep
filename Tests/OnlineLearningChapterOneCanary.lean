import BanditRLProof
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace ChapterOneCase0

open BanditRL.OnlineLearning

def demoLoss (t : ℕ) (b : Bool) : ℝ := if b then if t = 0 then -2 else 3 else 0
def demoLeader (n : ℕ) : Bool := n = 1

example : (∑ t ∈ Finset.range 2, demoLoss t (demoLeader (t + 1))) ≤
    ∑ t ∈ Finset.range 2, demoLoss t (demoLeader 2) := by
  apply lemma_1_2 Set.univ demoLoss demoLeader 2
  · simp
  · intro n hn hnt u hu
    interval_cases n <;> cases u <;> norm_num [demoLoss, demoLeader, Finset.sum_range_succ]

example : (∑ t ∈ Finset.range 2, demoLoss t (demoLeader (t + 1))) = -2 ∧
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader 2)) = 0 := by
  norm_num [demoLoss, demoLeader, Finset.sum_range_succ]

#print axioms BanditRL.OnlineLearning.lemma_1_2
end ChapterOneCase0

namespace ChapterOneCase1

open BanditRL.OnlineLearning

example : empiricalMean (fun t => if t = 0 then 0 else 1) 2 = (1:ℝ)/2 := by
  norm_num [empiricalMean, Finset.sum_range_succ]

example (u : ℝ) :
    (∑ t ∈ Finset.range 2, ((1:ℝ)/2 - (if t = 0 then 0 else 1))^2) ≤
    ∑ t ∈ Finset.range 2, (u - (if t = 0 then 0 else 1))^2 := by
  have h := empiricalMean_minimizes (fun t => if t = 0 then 0 else 1) 2 (by omega) u
  norm_num [empiricalMean, Finset.sum_range_succ] at h ⊢
  exact h

example : empiricalMean (fun t => if t = 0 then 0 else 1) 2 ∈ Set.Icc (0:ℝ) 1 := by
  apply empiricalMean_mem _ _ (by omega)
  intro t ht
  split_ifs <;> norm_num

#print axioms BanditRL.OnlineLearning.empiricalMean_decomposition
#print axioms BanditRL.OnlineLearning.empiricalMean_minimizes
#print axioms BanditRL.OnlineLearning.empiricalMean_mem
end ChapterOneCase1

namespace ChapterOneCase2
open BanditRL.OnlineLearning

def samples (t : ℕ) : ℝ := if t = 0 then 0 else 1

example : meanPredict samples 0 = 1/2 ∧ meanPredict samples 1 = 0 ∧
    empiricalMean samples 2 = 1/2 := by
  norm_num [meanPredict, empiricalMean, samples, Finset.sum_range_succ]

example : (∑ t ∈ Finset.range 2, (meanPredict samples t - samples t)^2) -
    (∑ t ∈ Finset.range 2, (empiricalMean samples 2 - samples t)^2) = 3/4 := by
  norm_num [meanPredict, empiricalMean, samples, Finset.sum_range_succ]

example : (∑ t ∈ Finset.range 2, (meanPredict samples t - samples t)^2) -
    (∑ t ∈ Finset.range 2, (empiricalMean samples 2 - samples t)^2) ≤
      4 + 4 * Real.log 2 := by
  apply theorem_1_3 samples 2 (by omega)
  intro t ht
  unfold samples
  split_ifs <;> norm_num

#print axioms BanditRL.OnlineLearning.meanPredict_prefix
#print axioms BanditRL.OnlineLearning.meanPredict_stability
#print axioms BanditRL.OnlineLearning.theorem_1_3
end ChapterOneCase2

namespace ChapterOneCase3
open BanditRL.OnlineLearning
example : NoRegret (Set.Icc (0:ℝ) 1)
    (fun t x => (x - (if t = 0 then 0 else 1))^2)
    (meanPredict (fun t => if t = 0 then 0 else 1)) := by
  apply meanPredict_noRegret
  intro t
  split_ifs <;> norm_num
#print axioms BanditRL.OnlineLearning.meanPredict_noRegret
#print axioms BanditRL.OnlineLearning.meanPredict_independent
end ChapterOneCase3

namespace ChapterOneCase4
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
end ChapterOneCase4

namespace ChapterOneUnique
open BanditRL.OnlineLearning
example (u : ℝ)
    (hu : (∑ t ∈ Finset.range 2, (u - (if t = 0 then 0 else 1))^2) ≤
      ∑ t ∈ Finset.range 2, (empiricalMean (fun t => if t = 0 then 0 else 1) 2 -
        (if t = 0 then 0 else 1))^2) : u = (1:ℝ)/2 := by
  have h := empiricalMean_unique (fun t => if t = 0 then 0 else 1) 2 (by omega) u hu
  norm_num [empiricalMean, Finset.sum_range_succ] at h
  exact h
#print axioms BanditRL.OnlineLearning.empiricalMean_unique
end ChapterOneUnique
