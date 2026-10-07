import BanditRLProof.OnlineLearningFTL
import Mathlib.Tactic

open BanditRL.OnlineLearning
namespace FTLSharpProbe

/-- Validation sequence: first target zero, subsequent targets one. -/
def probeTargets (t : ℕ) : ℝ := if t = 0 then 0 else 1

theorem endpoint_values :
    (meanPredict (fun _ => 0) 0 - 0)^2 - (empiricalMean (fun _ => 0) 1 - 0)^2 = (1 : ℝ) / 4 ∧
    (meanPredict (fun _ => 1) 0 - 1)^2 - (empiricalMean (fun _ => 1) 1 - 1)^2 = (1 : ℝ) / 4 ∧
    (meanPredict (fun _ => 0) 0 - 0)^2 - (empiricalMean (fun _ => 0) 1 - 0)^2 ≤ (1 : ℝ) / 4 ∧
    (meanPredict (fun _ => 1) 0 - 1)^2 - (empiricalMean (fun _ => 1) 1 - 1)^2 ≤ (1 : ℝ) / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
  · norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
  · exact meanPredict_initial_stability _ (by norm_num)
  · exact meanPredict_initial_stability _ (by norm_num)

theorem interior_value :
    (meanPredict (fun _ => (1 : ℝ) / 2) 0 - 1 / 2)^2 -
      (empiricalMean (fun _ => (1 : ℝ) / 2) 1 - 1 / 2)^2 = 0 ∧
    (meanPredict (fun _ => (1 : ℝ) / 2) 0 - 1 / 2)^2 -
      (empiricalMean (fun _ => (1 : ℝ) / 2) 1 - 1 / 2)^2 < (1 : ℝ) / 4 := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]

theorem outside_interval :
    (meanPredict (fun _ => 2) 0 - 2)^2 - (empiricalMean (fun _ => 2) 1 - 2)^2 = (9 : ℝ) / 4 ∧
    (meanPredict (fun _ => 2) 0 - 2)^2 - (empiricalMean (fun _ => 2) 1 - 2)^2 > (1 : ℝ) / 4 := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]

theorem one_round_refined :
    ((∑ t ∈ Finset.range 1, (meanPredict (fun _ => 0) t - 0)^2) -
      (∑ t ∈ Finset.range 1, (empiricalMean (fun _ => 0) 1 - 0)^2) = (1 : ℝ) / 4) ∧
    ((∑ t ∈ Finset.range 1, (meanPredict (fun _ => 0) t - 0)^2) -
      (∑ t ∈ Finset.range 1, (empiricalMean (fun _ => 0) 1 - 0)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (1 - 1), 4 / ((t : ℝ) + 2)) := by
  constructor
  · norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
  · exact meanPredict_regret_refined _ 1 (by omega) (by intro t ht; norm_num)

theorem two_round_refined :
    ((∑ t ∈ Finset.range 2, (meanPredict probeTargets t - probeTargets t)^2) -
      (∑ t ∈ Finset.range 2, (empiricalMean probeTargets 2 - probeTargets t)^2) = (3 : ℝ) / 4) ∧
    ((∑ t ∈ Finset.range 2, (meanPredict probeTargets t - probeTargets t)^2) -
      (∑ t ∈ Finset.range 2, (empiricalMean probeTargets 2 - probeTargets t)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)) ∧
    ((1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)) = 9 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [meanPredict, empiricalMean, probeTargets, Finset.sum_range_succ]
  · exact meanPredict_regret_refined _ 2 (by omega) (by
      intro t ht
      simp only [probeTargets]
      split_ifs <;> norm_num)
  · norm_num [Finset.sum_range_succ]

theorem future_independence :
    meanPredict (fun _ => 0) 1 = meanPredict probeTargets 1 ∧
    (0 : ℝ) ≠ probeTargets 1 := by
  constructor
  · apply meanPredict_prefix
    intro i hi
    have : i = 0 := by omega
    subst i
    norm_num [probeTargets]
  · norm_num [probeTargets]

end FTLSharpProbe
