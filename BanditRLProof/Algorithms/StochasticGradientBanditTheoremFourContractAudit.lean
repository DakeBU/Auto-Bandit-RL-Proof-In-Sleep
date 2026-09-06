import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmTheoremOne
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Stochastic-gradient bandit Theorem 4: source-contract audit

This module isolates finite scalar obligations from Appendix E, Steps 1, 3,
and 4, of Baudry, Johnson, Vary, Pike-Burke, and Rebeschini,
*Does Stochastic Gradient really succeed for Bandits?* (NeurIPS 2025).

The camera-ready proof uses a transient-phase argument to claim a positive
probability of never returning below best-arm probability `1 / 2`.  Its Step 4
switches between the conditions `q >= c` and `q < c`; as printed, the displayed
total-probability direction does not provide the lower bound later consumed by
Step 3.  The declarations below therefore record the conservative finite
contract that would suffice, while leaving the source-contract mismatch open:

* the printed learning-rate condition gives a positive drift margin;
* a buffered event of mass at least `pPrime`, together with conditional
  survival mass at least `1 - 2*c`, gives unconditional survival mass at
  least `pPrime * (1 - 2*c)`; and
* for `0 < rho <= 1`, a finite phase-mass sequence already known to be
  dominated by `(1 - rho)^j` has the usual `1 / rho` geometric envelope.

These are dependency-checked source-audit leaves.  They do **not** construct
the general-`K` generated SGB process, a stopped supermartingale, a Doob
maximal bound, the uniform buffered-event producer, or Theorem 4.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open scoped BigOperators
noncomputable section

/-- The positive scalar margin used in Appendix E after Equation (22). -/
def theoremFourStepOneMargin (K : Nat) (eta Delta : Real) : Real :=
  2 * Delta - eta * sourceC eta * ((K : Real) + 2)

/-- The unconditional survival mass required by the audited Step-4 event
composition. -/
def theoremFourStepFourSurvivalLowerBound (pPrime c : Real) : Real :=
  pPrime * (1 - 2 * c)

/-- The source learning-rate condition implies that the Equation-(22) drift
margin is strictly positive. -/
theorem theoremFourStepOneMargin_pos
    (K : Nat) (eta Delta : Real)
    (hmargin : eta * sourceC eta < 2 * Delta / ((K : Real) + 2)) :
    0 < theoremFourStepOneMargin K eta Delta := by
  have hden : 0 < (K : Real) + 2 := by positivity
  have hscaled := (lt_div_iff₀ hden).mp hmargin
  unfold theoremFourStepOneMargin
  linarith

/-- If `pPrime > 0` and `c < 1/2`, the audited Step-4 survival lower bound
is positive. -/
theorem theoremFourStepFourSurvivalLowerBound_pos
    (pPrime c : Real) (hpPrime : 0 < pPrime)
    (hc_half : c < 1 / 2) :
    0 < theoremFourStepFourSurvivalLowerBound pPrime c := by
  unfold theoremFourStepFourSurvivalLowerBound
  have hfactor : 0 < 1 - 2 * c := by linarith
  positivity

/-- Finite total-probability contract for Appendix E, Step 4.

`bufferedMass` represents the probability of entering the strict buffer
`q_{s+1} < c`; `jointSurvivalMass` represents the probability of both entering
that buffer and not returning before the audited finite horizon.  The two
middle hypotheses are the multiplication-free form of
`P(buffer) >= pPrime` and
`P(survival | buffer) >= 1 - 2*c`.
-/
theorem theoremFourStepFour_survivalMass_ge
    (pPrime c bufferedMass jointSurvivalMass survivalMass : Real)
    (hc_half : c < 1 / 2)
    (hbuffer : pPrime <= bufferedMass)
    (hconditional : (1 - 2 * c) * bufferedMass <= jointSurvivalMass)
    (hsubset : jointSurvivalMass <= survivalMass) :
    theoremFourStepFourSurvivalLowerBound pPrime c <= survivalMass := by
  have hfactor : 0 <= 1 - 2 * c := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hbuffer hfactor
  unfold theoremFourStepFourSurvivalLowerBound
  calc
    pPrime * (1 - 2 * c) = (1 - 2 * c) * pPrime := by ring
    _ <= (1 - 2 * c) * bufferedMass := hscaled
    _ <= jointSurvivalMass := hconditional
    _ <= survivalMass := hsubset

/-- The audited finite event contract yields a strictly positive survival
mass when its buffered event has positive mass. -/
theorem theoremFourStepFour_survivalMass_pos
    (pPrime c bufferedMass jointSurvivalMass survivalMass : Real)
    (hpPrime : 0 < pPrime) (hc_half : c < 1 / 2)
    (hbuffer : pPrime <= bufferedMass)
    (hconditional : (1 - 2 * c) * bufferedMass <= jointSurvivalMass)
    (hsubset : jointSurvivalMass <= survivalMass) :
    0 < survivalMass := by
  exact (theoremFourStepFourSurvivalLowerBound_pos pPrime c hpPrime
    hc_half).trans_le
      (theoremFourStepFour_survivalMass_ge pPrime c bufferedMass
        jointSurvivalMass survivalMass hc_half hbuffer hconditional
        hsubset)

/-- For `0 < rho <= 1`, the finite geometric phase envelope is at most
`1 / rho`.  This is the finite statement needed before any infinite
expected-phase claim. -/
theorem theoremFourFiniteGeometricPhaseMass_le_inv
    (rho : Real) (hrho_pos : 0 < rho) (hrho_le_one : rho <= 1)
    (phaseCount : Nat) :
    (Finset.range phaseCount).sum (fun phase => (1 - rho) ^ phase) <=
      1 / rho := by
  have hbase_nonneg : 0 <= 1 - rho := by linarith
  have hbase_lt_one : 1 - rho < 1 := by linarith
  have hsummable := summable_geometric_of_lt_one hbase_nonneg hbase_lt_one
  have hfinite := hsummable.sum_le_tsum (Finset.range phaseCount)
    (fun phase _ => pow_nonneg hbase_nonneg phase)
  rw [tsum_geometric_of_lt_one hbase_nonneg hbase_lt_one] at hfinite
  simpa [one_div] using hfinite

/-- Any finite transient-phase mass dominated termwise by the geometric
return envelope inherits the same `1 / rho` bound. -/
theorem theoremFourFiniteTransientMass_le_inv
    (rho : Real) (hrho_pos : 0 < rho) (hrho_le_one : rho <= 1)
    (phaseMass : Nat -> Real)
    (hphase : forall phase, phaseMass phase <= (1 - rho) ^ phase)
    (phaseCount : Nat) :
    (Finset.range phaseCount).sum phaseMass <= 1 / rho := by
  calc
    (Finset.range phaseCount).sum phaseMass <=
        (Finset.range phaseCount).sum (fun phase => (1 - rho) ^ phase) := by
      exact Finset.sum_le_sum (fun phase _ => hphase phase)
    _ <= 1 / rho :=
      theoremFourFiniteGeometricPhaseMass_le_inv rho hrho_pos hrho_le_one
        phaseCount

end
end StochasticGradientBandit
end BanditRLProof
