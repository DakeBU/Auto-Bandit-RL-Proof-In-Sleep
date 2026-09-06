import BanditRLProof.TsallisSqrtScheduleSelfBoundingRefinedScalar

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- A compact sufficient window for the coefficient-aware refined optimizer.
Here `armCount` is the number of suboptimal arms, `horizonMass = T + 1`,
`reciprocalGap` is the sum of inverse gaps, and `corruption` is the self-bound
allowance. -/
def RefinedLocalCorruptionWindow
    (armCount horizonMass reciprocalGap corruption : Real) : Prop :=
  25 * reciprocalGap ^ 2 <= armCount * horizonMass ∧
    corruption * reciprocalGap <= armCount * horizonMass ∧
      25 * reciprocalGap *
          (Real.log
            ((2 * armCount * horizonMass) /
              (25 * reciprocalGap ^ 2)) + 2) <=
        corruption

/-- The compact window plus `armCount <= reciprocalGap` supplies all scalar
contracts used by the generated refined theorem. -/
theorem refinedLocalCorruptionWindow_scalar_bounds
    (armCount horizonMass reciprocalGap corruption : Real)
    (harmCount : 1 <= armCount) (hhorizonMass : 0 < horizonMass)
    (hreciprocalGap : 0 < reciprocalGap)
    (hcountGap : armCount <= reciprocalGap)
    (hwindow : RefinedLocalCorruptionWindow
      armCount horizonMass reciprocalGap corruption) :
    2 <=
        (2 * armCount * horizonMass) /
          (25 * reciprocalGap ^ 2) ∧
      (2 * armCount * horizonMass) /
          (25 * reciprocalGap ^ 2) <= 2 * horizonMass ∧
      2 * (corruption * reciprocalGap) <=
        2 * armCount * horizonMass ∧
      25 * reciprocalGap *
          (Real.log
            ((2 * armCount * horizonMass) /
              (25 * reciprocalGap ^ 2)) + 2) <=
        corruption ∧
      0 < corruption := by
  rcases hwindow with ⟨hhorizon, hcorruptionUpper, hcorruptionLower⟩
  have hdenom : 0 < 25 * reciprocalGap ^ 2 := by positivity
  have hscalarLower :
      2 <=
        (2 * armCount * horizonMass) /
          (25 * reciprocalGap ^ 2) := by
    rw [le_div_iff₀ hdenom]
    nlinarith
  have hgapOne : 1 <= reciprocalGap := harmCount.trans hcountGap
  have hcountSq : armCount <= 25 * reciprocalGap ^ 2 := by
    have hgapSq : reciprocalGap <= reciprocalGap ^ 2 := by nlinarith
    nlinarith
  have hthresholdOne :
      (2 * armCount * horizonMass) /
          (25 * reciprocalGap ^ 2) <= 2 * horizonMass := by
    rw [div_le_iff₀ hdenom]
    nlinarith
  have hcorruptionUpper' :
      2 * (corruption * reciprocalGap) <=
        2 * armCount * horizonMass := by
    nlinarith
  have hratioOne :
      1 <=
        (2 * armCount * horizonMass) /
          (25 * reciprocalGap ^ 2) := one_le_two.trans hscalarLower
  have hlogNonneg :
      0 <= Real.log
        ((2 * armCount * horizonMass) /
          (25 * reciprocalGap ^ 2)) := Real.log_nonneg hratioOne
  have hcorruptionPos : 0 < corruption := by
    have hleftPos :
        0 < 25 * reciprocalGap *
          (Real.log
            ((2 * armCount * horizonMass) /
              (25 * reciprocalGap ^ 2)) + 2) := by
      positivity
    exact hleftPos.trans_le hcorruptionLower
  exact ⟨hscalarLower, hthresholdOne, hcorruptionUpper',
    hcorruptionLower, hcorruptionPos⟩

end Tsallis
end BanditRLProof
