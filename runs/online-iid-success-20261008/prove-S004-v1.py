from leaf_tools_v2 import *
assert load(RUN/'S003-focused-build-v3-exit.json')['exit_code']==0
description='Actual unknown-law strictpast meanPredict stochastic success: IID nonnegative excess and integrated4log upper produce ordinary zero normalized limit and little-o.'
body='''  let prediction := fun t ω => meanPredict (fun i => Y i ω) t
  have hlo : ∀ᶠ T : ℕ in atTop, 0 ≤ expectedFixedRegret μ Y prediction T / (T : ℝ) :=
    Eventually.of_forall (fun T => div_nonneg
      (meanPredict_expectedFixed_excess μ Y hY hlaw hb hind T).2 (Nat.cast_nonneg T))
  have hup : ∀ᶠ T : ℕ in atTop,
      expectedFixedRegret μ Y prediction T / (T : ℝ) ≤
        (4 + 4 * Real.log (T : ℝ)) / (T : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    exact div_le_div_of_nonneg_right
      (meanPredict_expectedFixed_upper μ Y hY hlaw hb T hT) (Nat.cast_nonneg T)
  have h0 : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hc : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun T : ℕ => (4 + 4 * Real.log (T : ℝ)) / (T : ℝ))
      atTop (nhds 0) := by
    have hh := ((h0.comp hc).const_mul 4).add ((h1.comp hc).const_mul 4)
    simp only [mul_zero, add_zero] at hh
    convert hh using 1
    ext T
    dsimp [Function.comp_def]
    ring
  have he := squeeze_zero' hlo hup hbound
  refine ⟨he, ?_⟩
  have hs := (centered_total_sublinear_iff_average
    (fun T => expectedFixedRegret μ Y prediction T) 0).mpr (by simpa only [sub_zero] using he)
  simpa only [mul_zero, sub_zero] using hs
'''
row=start_leaf(3,body,description)
gate('S004-focused-build-v1','lake','build','BanditRLProof.OnlineGuessingIIDSuccess')
finish_leaf(3,'v1',description)
write(RUN/'actual-DAG-proving-v1.json',dict(
    planned_DAG_sha256=sha(CONTRACT/'initial-DAG-v1.json'),
    actual_chosen_route_delta='S004 reuses new centered-total adapter S001 with c0 rather than directly repeat Mathlib little-oiffdivision; second actual consumer, terminal unchanged',
    headers_unchanged=True,actual_compiler_VALUE_edges='pending compiled graph audit, current route below architectural until audited',
    intended_local_edges=[['S001','S002'],['S001','S004'],['S003','S004']],
    package_accepted=False,chapter_complete=False,goal_complete=False))
