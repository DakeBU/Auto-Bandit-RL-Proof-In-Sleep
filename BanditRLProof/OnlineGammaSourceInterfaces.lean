import BanditRLProof.OnlineGammaDerivatives
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

open MeasureTheory
namespace BanditRL.OnlineGamma

theorem complexGamma_integral_and_integrable :
  ∀ (z : ℂ), 0 < z.re →
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (z - 1)) (Set.Ioi 0) ∧
    Complex.Gamma z = ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-t) : ℂ) * (t : ℂ) ^ (z - 1) := by
  intro z hz
  exact ⟨Complex.GammaIntegral_convergent hz, Complex.Gamma_eq_integral hz⟩

theorem logGammaSlope_eq_deriv_and_gamma_quotient :
  ∀ (x : ℝ), 0 < x →
    logGammaSlope x = deriv (fun y : ℝ => Real.log (Real.Gamma y)) x ∧
    logGammaSlope x = deriv Real.Gamma x / Real.Gamma x := by
  intro x hx
  have hd : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma (fun m =>
    ne_of_gt (lt_of_le_of_lt (neg_nonpos.mpr (Nat.cast_nonneg m)) hx))
  have hlog := (logGamma_derivatives x hx).1.deriv
  exact ⟨hlog.symm, hlog.symm.trans (deriv.log hd (Real.Gamma_pos_of_pos hx).ne')⟩

theorem convexOn_logGamma_positive :
  ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (Real.Gamma x)) := by
  simpa only [Function.comp_def] using Real.convexOn_log_Gamma

end BanditRL.OnlineGamma
