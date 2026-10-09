from leaf_driver import *
assert load(RUN/'affine-run-local-milestone-v1.json')['source_regret_lower_bound_closed'] is False
lower('phi_limit','''  have hd : HasDerivAt (fun z : ℝ => (1 / 2 : ℝ) ^ (1 - z))
      (-Real.log (1 / 2 : ℝ)) 1 := by
    simpa only [zero_sub, sub_self, Real.rpow_zero, mul_one, mul_neg_one] using
      (((hasDerivAt_const (1 : ℝ) 1).sub (hasDerivAt_id 1)).const_rpow
        (by norm_num : (0 : ℝ) < 1 / 2))
  have hs := hd.tendsto_slope.mono_left nhdsLT_le_nhdsNE
  have heq : (fun z : ℝ => ((1 / 2 : ℝ) ^ (1 - z) - 1) / (1 - z)) =
      (fun z => -slope (fun y : ℝ => (1 / 2 : ℝ) ^ (1 - y)) 1 z) := by
    funext z
    simp only [slope_def_field, sub_self, Real.rpow_zero]
    rw [show 1 - z = -(z - 1) by ring, div_neg]
  have hsecond : Tendsto (fun z : ℝ => ((1 / 2 : ℝ) ^ (1 - z) - 1) / (1 - z))
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log (1 / 2 : ℝ))) := by
    rw [heq]
    simpa only [neg_neg] using hs.neg
  have hc : ContinuousAt (fun z : ℝ => 1 / (2 - z)) 1 :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hfirst : Tendsto (fun z : ℝ => 1 / (2 - z)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
  constructor
  · have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    simpa only [phi, hlog, sub_eq_add_neg] using hfirst.add hsecond
  · linarith [Real.log_two_lt_d9]
''',['HasDerivAt.tendsto_slope actual primary derivative API','Real.hasStrictDerivAt_const_rpow/HasDerivAt.const_rpow actual primary API','Real.log_two_lt_d9 compiled primary bound'])
write(RUN/'phi-limit-local-milestone-v1.json',dict(leaf=targets['phi_limit']['name'],status='focused compiled/frozen only',source_supplementary_assertion='left limit1-log2>=0.3',not_endpoint_continuity=True,phi_range_open=True,source_algorithm_lower_bound_open=True,package_BODY_accepted=False,whole_Goal='ACTIVE'))
print('Printed coefficient left-limit/assertion locally compiled; phi range and algorithmic lower bound remain required/open.')
