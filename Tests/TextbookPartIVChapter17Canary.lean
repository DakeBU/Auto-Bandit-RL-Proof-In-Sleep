import BanditRLProof

/-!
# Typed public canary for Part IV, Chapter 17

The examples exercise only the compiled threshold, first-moment, probability,
and deterministic-algebra slice.  They do not claim Theorem 17.1,
Corollaries 17.2--17.3, Theorem 17.4, Claim 17.6, or Claim 17.7.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory Set

example {Omega : Type*} (quantity : Omega -> Real) (threshold : Real)
    (omega : Omega) :
    omega ∈ tailAtLeast quantity threshold ↔ threshold <= quantity omega := by
  rfl

example {Instance : Type*} [MeasurableSpace Instance]
    (Q : Measure Instance) [IsProbabilityMeasure Q]
    (tailMass : Instance -> Real) (delta : Real)
    (hIntegrable : Integrable tailMass Q)
    (hAverage : delta <= ∫ x, tailMass x ∂Q) :
    exists x, delta <= tailMass x := by
  exact exists_tailMass_ge_of_integral_ge Q tailMass delta hIntegrable hAverage

example {Instance : Type*} [MeasurableSpace Instance]
    (Q : Measure Instance) [IsProbabilityMeasure Q]
    (cdf : Instance -> Real -> Real) (threshold delta : Real)
    (hIntegrable : Integrable (fun x => 1 - cdf x threshold) Q)
    (hAverage : delta <= ∫ x, 1 - cdf x threshold ∂Q) :
    exists x, delta <= 1 - cdf x threshold := by
  exact exists_cdfTail_ge_of_integral_ge Q cdf threshold delta
    hIntegrable hAverage

example {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (pullSmall clippingBad : Set Omega) (delta : Real)
    (hPullSmall : 2 * delta <= P.real pullSmall)
    (hClippingBad : P.real clippingBad <= delta) :
    delta <= P.real (pullSmall \ clippingBad) := by
  exact measureReal_diff_ge_delta P pullSmall clippingBad delta
    hPullSmall hClippingBad

example (gap : Real) (hGap : 0 <= gap) :
    gap * ((8 : Real) / 4) <=
      adversarialRegretLowerExpression 8 4 2 gap := by
  exact adversarialRegretLowerExpression_ge_quarter 8 4 2 gap hGap
    (by norm_num) (by norm_num)

example (horizon alternativeArms : Nat) (B delta : Real) :
    stochasticHighProbabilityThreshold horizon alternativeArms B delta =
      (1 / 4 : Real) *
        min (horizon : Real)
          ((1 / B) *
            Real.sqrt ((alternativeArms : Real) * (horizon : Real)) *
            Real.log (1 / (4 * delta))) := by
  rfl

example (horizon alternativeArms : Nat) (delta : Real) :
    stochasticMinimaxHighProbabilityThreshold horizon alternativeArms delta =
      (1 / 4 : Real) *
        min (horizon : Real)
          (Real.sqrt
            (((horizon : Real) * (alternativeArms : Real) / 2) *
              Real.log (1 / (4 * delta)))) := by
  rfl

example (horizon arms : Nat) (c delta : Real) :
    adversarialHighProbabilityThreshold horizon arms c delta =
      c * Real.sqrt
        ((horizon : Real) * (arms : Real) * Real.log (1 / (2 * delta))) := by
  rfl

example (gap randomRegret : Real) (hGap : 0 <= gap)
    (hSource : adversarialRegretLowerExpression 8 4 2 gap <= randomRegret) :
    gap * ((8 : Real) / 4) <= randomRegret := by
  exact randomRegret_ge_quarter_of_clippingDecomposition
    8 4 2 gap randomRegret hGap (by norm_num) (by norm_num) hSource

#print axioms LowerBounds.exists_tailMass_ge_of_integral_ge
#print axioms LowerBounds.exists_cdfTail_ge_of_integral_ge
#print axioms LowerBounds.measureReal_diff_ge_delta
#print axioms LowerBounds.adversarialRegretLowerExpression_ge_quarter
#print axioms LowerBounds.randomRegret_ge_quarter_of_clippingDecomposition

end LowerBounds
end BanditRLProof
