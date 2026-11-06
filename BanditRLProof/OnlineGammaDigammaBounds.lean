import BanditRLProof.OnlineGammaReciprocalBounds

namespace BanditRL.OnlineGamma
open Filter
open scoped Topology

private theorem logGammaSlopeApprox_bounds (x : ℝ) (hx : 0 < x) (N : ℕ) :
    Real.log (N : ℝ) - Real.log (x + (N : ℝ)) + Real.log x - 1 / x ≤
      logGammaSlopeApprox N x ∧
    logGammaSlopeApprox N x ≤
      Real.log (N : ℝ) - Real.log (x + (N : ℝ)) + Real.log x - (1 / x) / 2 -
        (1 / (x + (N : ℝ))) / 2 := by
  have h := reciprocal_prefix_log_bounds x N hx
  simp only [logGammaSlopeApprox, Finset.sum_range_succ]
  constructor <;> linarith [h.1, h.2]

theorem logGammaSlope_bounds :
  ∀ (x : ℝ), 0 < x →
    Real.log x - 1 / x ≤ logGammaSlope x ∧
    logGammaSlope x ≤ Real.log x - 1 / (2 * x) := by
  intro x hx
  have ha : 0 < x / 2 := by linarith
  have hab : x / 2 < 2 * x := by linarith
  have hxin : x ∈ Set.Ioo (x / 2) (2 * x) := by constructor <;> linarith
  have heuler : Tendsto (fun N : ℕ => logGammaSlopeApprox N x) atTop (𝓝 (logGammaSlope x)) :=
    (tendstoUniformlyOn_logGammaSlopeApprox_and_curvatureApprox (x / 2) (2 * x) ha hab).1.tendsto_at hxin
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) - Real.log (x + (N : ℝ))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_log_comp_add_sub_log x).comp hcast).neg
    simpa only [Function.comp_def, neg_sub, neg_zero, add_comm] using h
  have hshift : Tendsto (fun N : ℕ => x + (N : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop hcast
  have hinv : Tendsto (fun N : ℕ => 1 / (x + (N : ℝ))) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hlow : Tendsto
      (fun N : ℕ => Real.log (N : ℝ) - Real.log (x + (N : ℝ)) + Real.log x - 1 / x)
      atTop (𝓝 (Real.log x - 1 / x)) := by
    simpa only [zero_add] using (hlog.add_const (Real.log x)).sub_const (1 / x)
  have hupp : Tendsto
      (fun N : ℕ => Real.log (N : ℝ) - Real.log (x + (N : ℝ)) + Real.log x - (1 / x) / 2 -
        (1 / (x + (N : ℝ))) / 2)
      atTop (𝓝 (Real.log x - (1 / x) / 2)) := by
    simpa only [zero_add, zero_div, sub_zero] using
      ((hlog.add_const (Real.log x)).sub_const ((1 / x) / 2)).sub (hinv.div_const 2)
  have hhalf : (1 / x) / 2 = 1 / (2 * x) := by
    field_simp [hx.ne']
    <;> ring
  constructor
  · exact le_of_tendsto_of_tendsto' hlow heuler (fun N => (logGammaSlopeApprox_bounds x hx N).1)
  · have h := le_of_tendsto_of_tendsto' heuler hupp (fun N => (logGammaSlopeApprox_bounds x hx N).2)
    simpa only [hhalf] using h

end BanditRL.OnlineGamma
