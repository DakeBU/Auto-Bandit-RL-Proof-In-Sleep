import BanditRLProof.OnlineGammaDerivatives
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace BanditRL.OnlineGamma

private theorem logGammaCurvature_pos (x : ℝ) (hx : 0 < x) :
    0 < logGammaCurvature x := by
  have hs := (logGamma_derivatives x hx).2.2
  have hterm (k : ℕ) : 0 < 1 / (x + (k : ℝ)) ^ 2 :=
    one_div_pos.mpr (sq_pos_of_pos (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k)))
  have h := Summable.tsum_lt_tsum_of_nonneg
    (f := fun _ : ℕ => (0 : ℝ)) (g := fun k : ℕ => 1 / (x + (k : ℝ)) ^ 2)
    (i := 0) (fun _ => le_rfl) (fun k => (hterm k).le) (hterm 0) hs.summable
  simpa only [tsum_zero, hs.tsum_eq] using h

private theorem logGammaCurvature_strictAntiOn :
    StrictAntiOn logGammaCurvature (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hsx := (logGamma_derivatives x hx).2.2
  have hsy := (logGamma_derivatives y hy).2.2
  have hterm (k : ℕ) :
      1 / (y + (k : ℝ)) ^ 2 < 1 / (x + (k : ℝ)) ^ 2 := by
    have hxk : 0 < x + (k : ℝ) := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k)
    have hyk : 0 < y + (k : ℝ) := add_pos_of_pos_of_nonneg hy (Nat.cast_nonneg k)
    exact one_div_lt_one_div_of_lt (sq_pos_of_pos hxk)
      ((sq_lt_sq₀ hxk.le hyk.le).2 (by linarith))
  have h := Summable.tsum_lt_tsum_of_nonneg
    (f := fun k : ℕ => 1 / (y + (k : ℝ)) ^ 2)
    (g := fun k : ℕ => 1 / (x + (k : ℝ)) ^ 2)
    (i := 0) (fun k => (one_div_pos.mpr
      (sq_pos_of_pos (add_pos_of_pos_of_nonneg hy (Nat.cast_nonneg k)))).le)
    (fun k => (hterm k).le) (hterm 0) hsx.summable
  simpa only [hsy.tsum_eq, hsx.tsum_eq] using h

theorem logGamma_deriv_strictMonoOn_and_strictConcaveOn :
  StrictMonoOn (deriv (fun y : ℝ => Real.log (Real.Gamma y))) (Set.Ioi (0 : ℝ)) ∧
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (deriv (fun y : ℝ => Real.log (Real.Gamma y))) := by
  have hc : ContinuousOn (deriv (fun y : ℝ => Real.log (Real.Gamma y)))
      (Set.Ioi (0 : ℝ)) := fun x hx =>
    (logGamma_derivatives x hx).2.1.continuousAt.continuousWithinAt
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) hc
    intro x hx
    have hx0 : 0 < x := interior_subset hx
    rw [(logGamma_derivatives x hx0).2.1.deriv]
    exact logGammaCurvature_pos x hx0
  · apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi (0 : ℝ)) hc
    intro x hx y hy hxy
    have hx0 : 0 < x := interior_subset hx
    have hy0 : 0 < y := interior_subset hy
    rw [(logGamma_derivatives x hx0).2.1.deriv,
      (logGamma_derivatives y hy0).2.1.deriv]
    exact logGammaCurvature_strictAntiOn hx0 hy0 hxy

end BanditRL.OnlineGamma
