from leaf_tools_v1 import *
description='Actual jointly measurable private-seed strict-history policy success equivalences; convergence is characterized, not asserted for every policy.'
body='''  dsimp only
  let prediction := fun t ω => policy t (S ω, fun i => Y i ω)
  have he (T : ℕ) := randomized_history_policy_expectedFixed_excess
    μ Y hY hlaw hb hind S hS hseed policy hp hpb T
  have hmin (T : ℕ) := expectedFixedMinimum_eq_variance μ Y hY hlaw hb T
  refine ⟨fun T => (he T).2, ?_, ?_⟩
  · have hi := centered_total_sublinear_iff_average
      (fun T => ∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ)
      (variance (Y 0) μ)
    simpa only [expectedFixedRegret, hmin] using hi
  · apply tendsto_congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    rw [normalized_excess _ _ T hT]
    have hx := (he T).1
    unfold expectedFixedRegret at hx
    rw [hmin T] at hx
    exact congrArg (fun x => x / (T : ℝ)) hx
'''
row=start_leaf(1,body,description)
gate('S002-focused-build-v1','lake','build','BanditRLProof.OnlineGuessingIIDSuccess')
finish_leaf(1,'v1',description)
