import BanditRLProof.LowerBounds.InformationTheory
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic.Linarith

/-!
# High-probability lower-bound interfaces

This module formalizes the source-faithful threshold surfaces and reusable
probability/algebra leaves from Lattimore--Szepesvari, *Bandit Algorithms*
(2020), Part IV, Chapter 17.

The stochastic bandit terminals (Theorem 17.1 and Corollaries 17.2--17.3)
still require the same-policy adaptive-history KL decomposition inherited from
Chapters 15--16.  The adversarial terminal (Theorem 17.4) additionally needs
the clipped-normal construction and Claims 17.6--17.7.  This file therefore
does not claim those terminals.  It does compile the exact threshold
expressions, the first-moment argument of Claim 17.5, the probability
subtraction step combining Claims 17.6--17.7, and the deterministic algebra
following Eq. (17.8).
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory Set

noncomputable section

/-- The tail event used throughout Chapter 17: the realized quantity is at
least the displayed lower-bound threshold. -/
def tailAtLeast {Omega : Type*} (quantity : Omega -> Real) (threshold : Real) :
    Set Omega :=
  {omega | threshold <= quantity omega}

/-- The exact threshold inside Theorem 17.1, with `alternativeArms = k - 1`.
The theorem's factor `1/4` multiplies the whole minimum. -/
def stochasticHighProbabilityThreshold
    (horizon alternativeArms : Nat) (B delta : Real) : Real :=
  (1 / 4 : Real) *
    min (horizon : Real)
      ((1 / B) * Real.sqrt ((alternativeArms : Real) * (horizon : Real)) *
        Real.log (1 / (4 * delta)))

/-- The exact threshold in Corollary 17.2, again with
`alternativeArms = k - 1`. -/
def stochasticMinimaxHighProbabilityThreshold
    (horizon alternativeArms : Nat) (delta : Real) : Real :=
  (1 / 4 : Real) *
    min (horizon : Real)
      (Real.sqrt
        (((horizon : Real) * (alternativeArms : Real) / 2) *
          Real.log (1 / (4 * delta))))

/-- The threshold shape in Theorem 17.4.  The universal constant `c` remains
an explicit argument, and the logarithm is `log (1 / (2 * delta))`. -/
def adversarialHighProbabilityThreshold
    (horizon arms : Nat) (c delta : Real) : Real :=
  c * Real.sqrt
    ((horizon : Real) * (arms : Real) * Real.log (1 / (2 * delta)))

/-- Claim 17.5 in its abstract first-moment form.  If the average tail mass is
at least `delta`, some deterministic instance has tail mass at least `delta`.

The textbook suppresses the regularity needed to write the expectation.  Lean
makes it explicit as `Integrable tailMass Q`; `Q` is explicitly a probability
measure. -/
theorem exists_tailMass_ge_of_integral_ge
    {Instance : Type*} [MeasurableSpace Instance]
    (Q : Measure Instance) [IsProbabilityMeasure Q]
    (tailMass : Instance -> Real) (delta : Real)
    (hIntegrable : Integrable tailMass Q)
    (hAverage : delta <= ∫ x, tailMass x ∂Q) :
    exists x, delta <= tailMass x := by
  obtain ⟨x, hx⟩ := exists_integral_le hIntegrable
  exact ⟨x, hAverage.trans hx⟩

/-- Claim 17.5 specialized to the source notation `1 - F_x(u)`. -/
theorem exists_cdfTail_ge_of_integral_ge
    {Instance : Type*} [MeasurableSpace Instance]
    (Q : Measure Instance) [IsProbabilityMeasure Q]
    (cdf : Instance -> Real -> Real) (threshold delta : Real)
    (hIntegrable : Integrable (fun x => 1 - cdf x threshold) Q)
    (hAverage :
      delta <= ∫ x, 1 - cdf x threshold ∂Q) :
    exists x, delta <= 1 - cdf x threshold := by
  exact exists_tailMass_ge_of_integral_ge Q
    (fun x => 1 - cdf x threshold) delta hIntegrable hAverage

/-- Probability subtraction used after Claims 17.6 and 17.7.  If the
pull-count event has probability at least `2 * delta` and the clipping event
has probability at most `delta`, their good difference has probability at
least `delta`.

No measurability hypothesis is hidden: `Measure.real` is defined for all sets,
and `le_measureReal_diff` is an outer-measure inequality. -/
theorem measureReal_diff_ge_delta
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P]
    (pullSmall clippingBad : Set Omega) (delta : Real)
    (hPullSmall : 2 * delta <= P.real pullSmall)
    (hClippingBad : P.real clippingBad <= delta) :
    delta <= P.real (pullSmall \ clippingBad) := by
  have hDiff :
      P.real pullSmall - P.real clippingBad <=
        P.real (pullSmall \ clippingBad) :=
    le_measureReal_diff
  linarith

/-- The deterministic lower expression on the right-hand side of Eq. (17.8),
after writing the pull and clipping counts as real numbers. -/
def adversarialRegretLowerExpression
    (horizon pullCount clippingCount : Nat) (gap : Real) : Real :=
  gap *
    ((horizon : Real) - (pullCount : Real) - (clippingCount : Real))

/-- If fewer than half of the rounds pull the distinguished arm and at most a
quarter are clipped, the Eq. (17.8) lower expression is at least one quarter
of `gap * horizon`. -/
theorem adversarialRegretLowerExpression_ge_quarter
    (horizon pullCount clippingCount : Nat) (gap : Real)
    (hGap : 0 <= gap)
    (hPull : (pullCount : Real) <= (horizon : Real) / 2)
    (hClipping : (clippingCount : Real) <= (horizon : Real) / 4) :
    gap * ((horizon : Real) / 4) <=
      adversarialRegretLowerExpression horizon pullCount clippingCount gap := by
  unfold adversarialRegretLowerExpression
  apply mul_le_mul_of_nonneg_left _ hGap
  linarith

/-- The explicit transfer from Eq. (17.8) to the quarter-horizon regret
threshold.  The premise `hSource` is exactly the construction-specific part
that Chapter 17 must still supply. -/
theorem randomRegret_ge_quarter_of_clippingDecomposition
    (horizon pullCount clippingCount : Nat) (gap randomRegret : Real)
    (hGap : 0 <= gap)
    (hPull : (pullCount : Real) <= (horizon : Real) / 2)
    (hClipping : (clippingCount : Real) <= (horizon : Real) / 4)
    (hSource :
      adversarialRegretLowerExpression horizon pullCount clippingCount gap <=
        randomRegret) :
    gap * ((horizon : Real) / 4) <= randomRegret :=
  (adversarialRegretLowerExpression_ge_quarter horizon pullCount clippingCount
    gap hGap hPull hClipping).trans hSource

end

end LowerBounds
end BanditRLProof
