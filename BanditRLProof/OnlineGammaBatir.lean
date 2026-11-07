import BanditRLProof.OnlineGammaDigammaBounds
import BanditRLProof.OnlineGammaSimplexCurvature

namespace BanditRL.OnlineGamma
open Filter Set
open scoped Topology

private noncomputable def batirG (x : ℝ) : ℝ :=
  logGammaSlope x - Real.log (x - 1 / 2)

private noncomputable def batirF (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - (x - 1 / 2) * (Real.log (x - 1 / 2) - 1) -
    (1 / 2) * Real.log (2 * Real.exp 1)

private theorem batirG_hasDerivAt (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt batirG (logGammaCurvature x - 1 / (x - 1 / 2)) x := by
  have hx0 : 0 < x := by linarith
  have hu : 0 < x - 1 / 2 := by linarith
  have hs : HasDerivAt logGammaSlope (logGammaCurvature x) x := by
    apply (logGamma_derivatives x hx0).2.1.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx0] with y hy
    exact (logGamma_derivatives y hy).1.deriv.symm
  have hl := ((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).log hu.ne'
  change HasDerivAt (fun y : ℝ => logGammaSlope y - Real.log (y - 1 / 2))
    (logGammaCurvature x - 1 / (x - 1 / 2)) x
  simpa only [Pi.sub_apply, id_eq] using hs.sub hl

private theorem batirG_tendsto : Tendsto batirG atTop (𝓝 0) := by
  have hneg : Tendsto (fun x : ℝ => -(1 / x)) atTop (𝓝 0) := by
    simpa only [one_div, neg_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).neg
  have hdiff : Tendsto (fun x : ℝ => logGammaSlope x - Real.log x) atTop (𝓝 0) := by
    apply hneg.squeeze' tendsto_const_nhds
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h := (logGammaSlope_bounds x hx).1
      linarith
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h := (logGammaSlope_bounds x hx).2
      have hi : 0 ≤ 1 / (2 * x) := by positivity
      linarith
  have hshift := Real.tendsto_log_comp_add_sub_log (-(1 / 2 : ℝ))
  have heq : (fun x : ℝ => (logGammaSlope x - Real.log x) -
      (Real.log (x + -(1 / 2)) - Real.log x)) = batirG := by
    funext x
    dsimp [batirG]
    rw [show x + -(1 / 2 : ℝ) = x - 1 / 2 by ring]
    ring
  simpa only [heq, sub_self] using hdiff.sub hshift

private theorem batirG_nonneg (x : ℝ) (hx : 1 ≤ x) : 0 ≤ batirG x := by
  have hsign (y : ℝ) (hy : 1 ≤ y) : logGammaCurvature y - 1 / (y - 1 / 2) ≤ 0 := by
    have hu : 0 < y - 1 / 2 := by linarith
    have hs := simplexLogFactor_derivatives (y - 1 / 2) hu
    have hn := hs.2.2
    rw [hs.2.1.deriv] at hn
    rw [show y - 1 / 2 + 1 / 2 = y by ring] at hn
    linarith
  have hanti : AntitoneOn batirG (Ici (1 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (1 : ℝ))
    · exact fun y hy => (batirG_hasDerivAt y hy).continuousAt.continuousWithinAt
    · exact fun y hy => (batirG_hasDerivAt y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(batirG_hasDerivAt y (interior_subset hy)).deriv]
      exact hsign y (interior_subset hy)
  apply le_of_tendsto batirG_tendsto
  filter_upwards [eventually_ge_atTop x] with y hxy
  exact hanti hx (hx.trans hxy) hxy

private theorem batirF_hasDerivAt (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt batirF (batirG x) x := by
  have hx0 : 0 < x := by linarith
  have hu : 0 < x - 1 / 2 := by linarith
  have hid := (hasDerivAt_id x).sub_const (1 / 2 : ℝ)
  have hlog := hid.log hu.ne'
  have hd := ((logGamma_derivatives x hx0).1.sub
    (hid.mul (hlog.sub_const 1))).sub_const ((1 / 2 : ℝ) * Real.log (2 * Real.exp 1))
  change HasDerivAt (fun y : ℝ => Real.log (Real.Gamma y) -
    (y - 1 / 2) * (Real.log (y - 1 / 2) - 1) - (1 / 2) * Real.log (2 * Real.exp 1)) (batirG x) x
  have hcancel : (x - 1 / 2) * (1 / (x - 1 / 2)) = 1 := by
    simpa only [one_div] using mul_inv_cancel₀ hu.ne'
  have hcoef : logGammaSlope x -
      (1 * (Real.log (x - 1 / 2) - 1) + (x - 1 / 2) * (1 / (x - 1 / 2))) =
      batirG x := by
    rw [one_mul, hcancel]
    dsimp [batirG]
    ring
  simpa only [id_eq, Pi.sub_apply, Pi.mul_apply, hcoef] using hd

private theorem batirF_nonneg (x : ℝ) (hx : 1 ≤ x) : 0 ≤ batirF x := by
  have hmono : MonotoneOn batirF (Ici (1 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (1 : ℝ))
    · exact fun y hy => (batirF_hasDerivAt y hy).continuousAt.continuousWithinAt
    · exact fun y hy => (batirF_hasDerivAt y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(batirF_hasDerivAt y (interior_subset hy)).deriv]
      exact batirG_nonneg y (interior_subset hy)
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have h1 : batirF 1 = 0 := by
    unfold batirF
    rw [Real.Gamma_one, Real.log_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      hhalf, Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
    ring
  have h := hmono (show (1 : ℝ) ∈ Ici (1 : ℝ) from Set.mem_Ici.mpr le_rfl) hx hx
  simpa only [h1] using h

theorem gamma_lower_bound_batir :
  ∀ (x : ℝ), 1 ≤ x →
    ((x - 1 / 2) / Real.exp 1) ^ (x - 1 / 2) *
      Real.sqrt (2 * Real.exp 1) ≤ Real.Gamma x := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hu : 0 < x - 1 / 2 := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase : 0 < (x - 1 / 2) / Real.exp 1 := div_pos hu he
  have htwo : 0 < 2 * Real.exp 1 := by positivity
  have hp := Real.rpow_pos_of_pos hbase (x - 1 / 2)
  have hs := Real.sqrt_pos.2 htwo
  apply (Real.log_le_log_iff (mul_pos hp hs) (Real.Gamma_pos_of_pos hx0)).mp
  rw [Real.log_mul hp.ne' hs.ne', Real.log_rpow hbase,
    Real.log_div hu.ne' he.ne', Real.log_exp, Real.log_sqrt htwo.le]
  have h := batirF_nonneg x hx
  dsimp [batirF] at h
  linarith

end BanditRL.OnlineGamma
