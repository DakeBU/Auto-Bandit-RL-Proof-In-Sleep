import BanditRLProof

open MeasureTheory ProbabilityTheory BanditRLProof.HOO
open scoped ENNReal

namespace HOOCausalCanary

-- The initial search is a genuine binary-tree search, with deterministic ties.
example : action 1 (1/2) (fun _ => 0) 0 = [false] := by
  norm_num [action, history, next, select, expanded, depthBound, walk, bValue,
    backward, preferred, child]

private theorem leaf_value (S : Finset Node) (U : Node → WithTop ℝ) (v : Node)
    (hv : v ∈ S) (hl : child v false ∉ S) (hr : child v true ∉ S) : bValue S U v = U v := by
  rw [bValue_eq S U v hv, bValue_not_mem S U _ hl, bValue_not_mem S U _ hr]
  simp

private theorem select_two (U : Node → WithTop ℝ) :
    select {[], [false], [true]} U =
      if U [true] ≤ U [false] then [false, false] else [true, false] := by
  have h0 := leaf_value {[], [false], [true]} U [false] (by decide) (by decide) (by decide)
  have h1 := leaf_value {[], [false], [true]} U [true] (by decide) (by decide) (by decide)
  have h00 := bValue_not_mem {[], [false], [true]} U [false, false] (by decide)
  have h01 := bValue_not_mem {[], [false], [true]} U [false, true] (by decide)
  have h10 := bValue_not_mem {[], [false], [true]} U [true, false] (by decide)
  have h11 := bValue_not_mem {[], [false], [true]} U [true, true] (by decide)
  by_cases h : U [true] ≤ U [false] <;>
    simp [select, depthBound, walk, preferred, child, h0, h1, h00, h01, h10, h11, h]

theorem left_reward_select : next 1 (1/2) [([false], 1), ([true], 0)] = [false, false] := by
  unfold next
  have he : expanded [([false], (1 : ℝ)), ([true], 0)] = {[], [false], [true]} := by
    ext v; simp [expanded]
  rw [he, select_two]
  have hc : upper 1 (1/2) [([false], 1), ([true], 0)] [true] ≤
      upper 1 (1/2) [([false], 1), ([true], 0)] [false] := by
    simp only [upper, visits, rewardSum]
    norm_num [List.IsPrefix, ← WithTop.coe_add, ← WithTop.coe_mul]
  rw [if_pos hc]

example : next 1 (1/2) [([false], 0), ([true], 1)] = [true, false] := by
  unfold next
  have he : expanded [([false], (0 : ℝ)), ([true], 1)] = {[], [false], [true]} := by
    ext v; simp [expanded]
  rw [he, select_two]
  have hc : ¬ upper 1 (1/2) [([false], 0), ([true], 1)] [true] ≤
      upper 1 (1/2) [([false], 0), ([true], 1)] [false] := by
    simp only [upper, visits, rewardSum]
    norm_num [List.IsPrefix, ← WithTop.coe_add, ← WithTop.coe_mul]
  rw [if_neg hc]

private theorem next_one (y : ℝ) : next 1 (1/2) [([false], y)] = [true] := by
  let U := upper 1 (1/2) [([false], y)]
  have h0 := leaf_value {[], [false]} U [false] (by decide) (by decide) (by decide)
  have h1 := bValue_not_mem {[], [false]} U [true] (by decide)
  have hU : U [false] ≠ ⊤ := by
    norm_num [U, upper, visits, rewardSum, List.IsPrefix, ← WithTop.coe_mul]
  have he : expanded [([false], y)] = {[], [false]} := by ext v; simp [expanded]
  unfold next
  rw [he]
  change select {[], [false]} U = _
  simp [select, depthBound, walk, preferred, child, h0, h1, hU]

-- End-to-end generated third action, rather than only a supplied history.
example : action 1 (1/2) (fun i => if i = 0 then 1 else 0) 2 = [false, false] := by
  have hh : history 1 (1/2) (fun i => if i = 0 then 1 else 0) 2 =
      [([false], 1), ([true], 0)] := by
    have hn0 : next 1 (1/2) [] = [false] := by
      norm_num [next, select, expanded, depthBound, walk, bValue, backward, preferred, child]
    simp only [history, step, hn0, List.nil_append, next_one, List.cons_append]
    norm_num
  unfold action
  rw [hh]
  exact left_reward_select

-- A genuinely noisy, nonconstant law on the countably infinite node set.
-- This is a process canary; a complete A1/A2 infinite-arm witness is still required.
noncomputable def rewardLaw (v : Node) : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac 0 +
    (1/2 : ℝ≥0∞) • Measure.dirac (if v.head? = some false then 1 else 1/2)

instance rewardLaw_probability (v : Node) : IsProbabilityMeasure (rewardLaw v) := by
  constructor
  norm_num [rewardLaw, ENNReal.inv_two_add_inv_two]

noncomputable def law : Kernel Node ℝ := Kernel.ofFunOfCountable rewardLaw

instance law_markov : IsMarkovKernel law := by
  constructor
  intro v
  exact rewardLaw_probability v

example : IsProbabilityMeasure (trajectory 1 (1/2) law) := inferInstance

theorem law_bounded (v : Node) : ∀ᵐ y ∂law v, y ∈ Set.Icc (0 : ℝ) 1 := by
  change ∀ᵐ y ∂rewardLaw v, y ∈ Set.Icc (0 : ℝ) 1
  simp only [rewardLaw, ae_add_measure_iff]
  constructor
  · simp
  · split_ifs <;> norm_num

-- Both tails use the actual eight-round adaptive process and random visit count.
example (lower : Bool) :
    (trajectory 1 (1/2) law) {Y | 0 < visits (history 1 (1/2) Y 8) [false] ∧
      Real.sqrt (2 * (visits (history 1 (1/2) Y 8) [false] : ℝ) * 1) ≤
        regionDeviation 1 (1/2) law [false] 8 lower Y} ≤
      (8 : ENNReal) * ENNReal.ofReal (Real.exp (-4*1)) :=
  region_deviation_confidence 1 (1/2) law law_bounded [false] 8 lower 1 (by norm_num)

example (n : ℕ) :
    condDistrib (fun Y : ℕ → ℝ => Y (n+1)) (Preorder.frestrictLe n) (trajectory 1 (1/2) law)
      =ᵐ[(trajectory 1 (1/2) law).map (Preorder.frestrictLe n)] stepKernel 1 (1/2) law n :=
  trajectory_condDistrib 1 (1/2) law n

example (Y : ℕ → ℝ) : Function.Injective (action 1 (1/2) Y) := action_injective _ _ _

#print axioms BanditRLProof.HOO.measurable_action
#print axioms BanditRLProof.HOO.trajectory_condDistrib
#print axioms BanditRLProof.HOO.bValue_eq
#print axioms BanditRLProof.HOO.near_optimal_region
#print axioms BanditRLProof.HOO.region_deviation_confidence
#print axioms BanditRLProof.HOO.trajectory_initial_law

end HOOCausalCanary
