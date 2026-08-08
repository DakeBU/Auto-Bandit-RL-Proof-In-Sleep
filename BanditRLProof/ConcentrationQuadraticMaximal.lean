import BanditRLProof.ConcentrationQuadraticFixedMGF
import BanditRLProof.ProbabilityUnionBound

/-!
# Finite maximal quadratic fixed-MGF tails

This module adds a finite-index maximal surface to the quadratic fixed-MGF
route.  It uses equal confidence shares and the finite outer-measure union
bound; it is not a Ville, Doob, or infinite-horizon maximal inequality.
-/

namespace BanditRLProof.Concentration

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

/-- Equal-share quadratic radius for a finite family of events. -/
noncomputable def quadraticFixedMGFMaximalRadius
    {Idx : Type*} [DecidableEq Idx] (times : Finset Idx)
    (varianceScale varianceBudget tiltCap delta : Real) : Real :=
  quadraticFixedMGFRadius varianceScale varianceBudget tiltCap
    (delta / (times.card : Real))

/-- Finite maximal delta tail obtained by optimizing every fixed-tilt event
at confidence `delta / times.card` and taking the finite union. -/
theorem measure_biUnion_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
    {Omega Idx : Type*} [MeasurableSpace Omega] [DecidableEq Idx]
    (mu : Measure Omega) (times : Finset Idx) (htimes : times.Nonempty)
    (deviation predictableVariance : Idx -> Omega -> Real)
    (varianceScale varianceBudget tiltCap delta : Real)
    (hvarianceScale : 0 < varianceScale)
    (hvarianceBudget : 0 < varianceBudget) (htiltCap : 0 < tiltCap)
    (hdelta : 0 < delta)
    (hfixed : forall i, i ∈ times -> forall tilt,
      0 <= tilt -> tilt <= tiltCap ->
        mu {omega |
            quadraticFixedMGFMaximalRadius times varianceScale varianceBudget
                tiltCap delta <= deviation i omega ∧
              predictableVariance i omega <= varianceBudget} <=
          ENNReal.ofReal (Real.exp
            (-tilt * quadraticFixedMGFMaximalRadius times varianceScale
                varianceBudget tiltCap delta +
              varianceScale * (tilt ^ 2 * varianceBudget)))) :
    mu (⋃ i ∈ times, {omega |
        quadraticFixedMGFMaximalRadius times varianceScale varianceBudget
            tiltCap delta <= deviation i omega ∧
          predictableVariance i omega <= varianceBudget}) <=
      ENNReal.ofReal delta := by
  let deltaShare := delta / (times.card : Real)
  have hcardNat : 0 < times.card := Finset.card_pos.mpr htimes
  have hcardReal : 0 < (times.card : Real) := Nat.cast_pos.mpr hcardNat
  have hdeltaShare : 0 < deltaShare := div_pos hdelta hcardReal
  have htail : ∀ i ∈ times,
      mu {omega |
          quadraticFixedMGFMaximalRadius times varianceScale varianceBudget
              tiltCap delta <= deviation i omega ∧
            predictableVariance i omega <= varianceBudget} <=
        ENNReal.ofReal deltaShare := by
    intro i hi
    have hiTail :=
      measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
        mu (deviation i) (predictableVariance i) varianceScale varianceBudget
          tiltCap deltaShare hvarianceScale hvarianceBudget htiltCap hdeltaShare
          (by
            intro tilt htilt_nonneg htilt_le
            simpa [quadraticFixedMGFMaximalRadius, deltaShare] using
              hfixed i hi tilt htilt_nonneg htilt_le)
    simpa [quadraticFixedMGFMaximalRadius, deltaShare] using hiTail
  have hcardENN_ne_zero : (times.card : ENNReal) ≠ 0 := by
    simp [Finset.card_ne_zero.mpr htimes]
  have hcardENN_ne_top : (times.card : ENNReal) ≠ ⊤ := by simp
  calc
    mu (⋃ i ∈ times, {omega |
        quadraticFixedMGFMaximalRadius times varianceScale varianceBudget
            tiltCap delta <= deviation i omega ∧
          predictableVariance i omega <= varianceBudget}) <=
        ∑ i ∈ times, mu {omega |
          quadraticFixedMGFMaximalRadius times varianceScale varianceBudget
              tiltCap delta <= deviation i omega ∧
            predictableVariance i omega <= varianceBudget} :=
      ProbabilityUnionBound.measure_biUnion_finset_le mu times fun i =>
        {omega |
          quadraticFixedMGFMaximalRadius times varianceScale varianceBudget
              tiltCap delta <= deviation i omega ∧
            predictableVariance i omega <= varianceBudget}
    _ <= ∑ _i ∈ times, ENNReal.ofReal deltaShare := by
      exact Finset.sum_le_sum fun i hi => htail i hi
    _ = (times.card : ENNReal) * ENNReal.ofReal deltaShare := by
      simp [nsmul_eq_mul]
    _ = ENNReal.ofReal delta := by
      dsimp [deltaShare]
      rw [ENNReal.ofReal_div_of_pos hcardReal]
      simp only [ENNReal.ofReal_natCast]
      exact ENNReal.mul_div_cancel hcardENN_ne_zero hcardENN_ne_top

end BanditRLProof.Concentration
