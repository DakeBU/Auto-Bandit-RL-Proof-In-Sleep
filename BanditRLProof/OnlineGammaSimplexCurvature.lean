import BanditRLProof.OnlineGammaDerivatives
import BanditRLProof.OnlineGammaIntegralEstimates
import BanditRLProof.OnlineGammaSimplexBasic

namespace BanditRL.OnlineGamma

open Filter Set

private theorem simplexLogFactor_first (x : ℝ) (hx : 0 < x) :
    HasDerivAt simplexLogFactor (Real.log x + 1 - logGammaSlope (x + 1/2)) x := by
  have hd := (logGamma_derivatives (x + 1/2) (by positivity)).1
  have hs := hd.comp x ((hasDerivAt_id x).add_const (1/2 : ℝ))
  change HasDerivAt (fun z : ℝ => z * Real.log z - Real.log (Real.Gamma (z + 1/2))) _ x
  simpa [Function.comp_def, Pi.sub_def] using
    (Real.hasDerivAt_mul_log hx.ne').sub hs

theorem simplexLogFactor_derivatives (x : ℝ) (hx : 0 < x) :
    HasDerivAt simplexLogFactor (Real.log x + 1 - logGammaSlope (x + 1/2)) x ∧
    HasDerivAt (deriv simplexLogFactor) (1/x - logGammaCurvature (x + 1/2)) x ∧
    0 ≤ deriv (deriv simplexLogFactor) x := by
  have hy : 0 < x + 1/2 := by positivity
  obtain ⟨_, hg, hsum⟩ := logGamma_derivatives (x + 1/2) hy
  have hslope : HasDerivAt logGammaSlope (logGammaCurvature (x + 1/2)) (x + 1/2) := by
    apply hg.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hy] with z hz
    exact (logGamma_derivatives z hz).1.deriv.symm
  have hshift := hslope.comp x ((hasDerivAt_id x).add_const (1/2 : ℝ))
  have hsecond : HasDerivAt (deriv simplexLogFactor) (1/x - logGammaCurvature (x + 1/2)) x := by
    have hv : HasDerivAt (fun z : ℝ => Real.log z + 1 - logGammaSlope (z + 1/2))
        (1/x - logGammaCurvature (x + 1/2)) x := by
      simpa [Function.comp_def, Pi.sub_apply, one_div] using
        ((Real.hasDerivAt_log hx.ne').add_const 1).sub hshift
    apply hv.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with z hz
    exact (simplexLogFactor_first z hz).deriv
  refine ⟨simplexLogFactor_first x hx, hsecond, ?_⟩
  rw [hsecond.deriv, sub_nonneg, ← hsum.tsum_eq]
  obtain ⟨_, heq, hbound⟩ := midpointInvSq_ray_integral x hx
  rw [heq] at hbound
  convert hbound using 1
  congr 1
  funext k
  rw [add_right_comm x (1/2 : ℝ)]

theorem simplexLogFactor_convexOn : ConvexOn ℝ (Set.Ici 0) simplexLogFactor := by
  apply convexOn_of_deriv2_nonneg (convex_Ici (0 : ℝ)) continuousOn_simplexLogFactor_and_zero.1
  · rw [interior_Ici]
    exact fun x hx => (simplexLogFactor_derivatives x hx).1.differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    exact fun x hx => (simplexLogFactor_derivatives x hx).2.1.differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    exact fun x hx => (simplexLogFactor_derivatives x hx).2.2

end BanditRL.OnlineGamma
