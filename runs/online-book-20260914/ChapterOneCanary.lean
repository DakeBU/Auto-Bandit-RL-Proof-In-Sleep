import BanditRLProof.OnlineLearningFoundations
import Mathlib.Tactic

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
