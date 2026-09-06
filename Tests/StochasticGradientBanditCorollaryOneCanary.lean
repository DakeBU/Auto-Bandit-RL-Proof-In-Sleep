import BanditRLProof.Algorithms.StochasticGradientBanditCorollaryOne

/-!
# SGB Corollary-1 companion canary

This canary pins the actual generated sampled-pseudo-regret route, the exact
finite two-branch consumer of Theorem 1, and the explicit
`sqrt (T * log T)` endpoint.  It does not promote the separate Theorem-2
polynomial lower-bound route.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

#check twoArmSampledPseudoRegret_le_gap_mul_horizon
#check measurable_twoArmSampledPseudoRegret
#check integrable_twoArmSampledPseudoRegret
#check integral_twoArmSampledPseudoRegret_le_gap_mul_horizon
#check corollaryOneEta
#check sourceTheoremOne_margin_of_two_mul_eta_sourceC_le
#check sourceTheoremOne_constant_le_inv_eta
#check corollaryOneEta_pos
#check corollaryOneEta_sq
#check corollaryOneEta_le_one
#check corollaryOneRate
#check corollaryOneEta_mul_horizon_eq_rate
#check corollaryOneEta_mul_rate_eq_log
#check corollaryOne_inv_eta_le_inv_log_two_mul_rate
#check corollaryOne_log_argument_le_horizon_pow_four
#check corollaryOne_log_term_le_two_mul_rate
#check corollaryOne_gap_mul_horizon_le_exp_constant_mul_rate
#check corollaryOneAbsoluteConstant
#check corollaryOne_piecewise_bound
#check twoArmFixedIIDDirac_corollaryOne_piecewise
#check twoArmFixedIIDDirac_corollaryOne

example
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (mean : Fin 2 -> Real)
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm, |reward| <= 1)
    (hmean : forall arm, integral (armLaw arm) id = mean arm)
    (Delta : Real) (hDelta : 0 < Delta) (hDelta_lt_one : Delta < 1)
    (hgap : mean 0 - mean 1 = Delta)
    (tailHorizon : Nat) (horizon_ge_two : 1 <= tailHorizon) :
    let eta := corollaryOneEta (tailHorizon + 1)
    integral
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmSampledPseudoRegret (Env := Unit) Delta
          (tailHorizon + 1)) <=
      corollaryOneAbsoluteConstant *
        corollaryOneRate (tailHorizon + 1) :=
  twoArmFixedIIDDirac_corollaryOne armLaw hprob mean hbound hmean Delta
    hDelta hDelta_lt_one hgap tailHorizon horizon_ge_two

#print axioms twoArmSampledPseudoRegret_le_gap_mul_horizon
#print axioms integral_twoArmSampledPseudoRegret_le_gap_mul_horizon
#print axioms sourceTheoremOne_constant_le_inv_eta
#print axioms twoArmFixedIIDDirac_corollaryOne_piecewise
#print axioms twoArmFixedIIDDirac_corollaryOne

end StochasticGradientBandit
end BanditRLProof
