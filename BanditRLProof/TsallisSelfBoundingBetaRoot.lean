import BanditRLProof.TsallisSqrtScheduleSelfBoundingTuning
import Mathlib.Topology.Order.IntermediateValue

/-!
# Tsallis self-bounding beta root

This module isolates the scalar intermediate-value step used by the refined
self-bounding tuning route.  It proves existence of a root in the paper's
admissible beta interval without assuming a Lambert-W API.  Quantitative bounds
on that root remain downstream obligations.
-/

namespace BanditRLProof
namespace Tsallis

open Set

/-- The scalar equation used to tune the refined self-bounding parameter. -/
noncomputable def selfBoundingBetaEquation
    (scale reciprocalGap corruption beta : Real) : Real :=
  corruption * reciprocalGap / scale * beta - Real.log beta - 1

/-- The beta equation is continuous on every interval bounded below by one. -/
theorem continuousOn_selfBoundingBetaEquation
    (scale reciprocalGap corruption upper : Real) :
    ContinuousOn (selfBoundingBetaEquation scale reciprocalGap corruption)
      (Icc 1 upper) := by
  unfold selfBoundingBetaEquation
  apply ContinuousOn.sub
  · apply ContinuousOn.sub
    · fun_prop
    · exact Real.continuousOn_log.mono (by
        intro beta hbeta
        exact ne_of_gt (zero_lt_one.trans_le hbeta.1))
  · exact continuousOn_const

/-- Under the corruption window used by the refined Tsallis-INF analysis, the
scalar beta equation has a zero between one and `scale / reciprocalGap ^ 2`.
This is the intermediate-value certificate that precedes any quantitative
Lambert-W estimate. -/
theorem exists_selfBoundingBetaEquation_eq_zero
    (scale reciprocalGap corruption : Real)
    (hscale : 0 < scale) (hreciprocalGap : 0 < reciprocalGap)
    (hupper : 1 <= scale / reciprocalGap ^ 2)
    (hcorruptionUpper : corruption * reciprocalGap <= scale)
    (hcorruptionLower :
      reciprocalGap *
          (Real.log (scale / reciprocalGap ^ 2) + 1) <= corruption) :
    exists beta,
      beta ∈ Icc 1 (scale / reciprocalGap ^ 2) ∧
        selfBoundingBetaEquation scale reciprocalGap corruption beta = 0 := by
  let upper := scale / reciprocalGap ^ 2
  let g := selfBoundingBetaEquation scale reciprocalGap corruption
  have hgOne : g 1 <= 0 := by
    dsimp [g, selfBoundingBetaEquation]
    rw [Real.log_one]
    have hdiv : corruption * reciprocalGap / scale <= 1 :=
      (div_le_one hscale).2 hcorruptionUpper
    linarith
  have hgUpper : 0 <= g upper := by
    have hreciprocalGapNe : reciprocalGap ≠ 0 := ne_of_gt hreciprocalGap
    have hscaleNe : scale ≠ 0 := ne_of_gt hscale
    have hnormalize :
        corruption * reciprocalGap / scale * upper =
          corruption / reciprocalGap := by
      dsimp [upper]
      field_simp
    have hdiv :
        Real.log upper + 1 <= corruption / reciprocalGap := by
      apply (le_div_iff₀ hreciprocalGap).2
      simpa [mul_comm] using hcorruptionLower
    dsimp [g, selfBoundingBetaEquation]
    rw [hnormalize]
    linarith
  have hcontinuous : ContinuousOn g (Icc 1 upper) := by
    exact continuousOn_selfBoundingBetaEquation
      scale reciprocalGap corruption upper
  have hzero : (0 : Real) ∈ Icc (g 1) (g upper) := ⟨hgOne, hgUpper⟩
  rcases intermediate_value_Icc hupper hcontinuous hzero with
    ⟨beta, hbeta, hbetaZero⟩
  exact ⟨beta, hbeta, hbetaZero⟩

end Tsallis
end BanditRLProof
