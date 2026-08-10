import BanditRLProof.ConcentrationQuadraticFixedMGF

/-!
# Countable scheduled quadratic fixed-MGF tails

This module lifts the one-event quadratic fixed-MGF delta theorem to a
countable family with time-varying parameters and confidence shares. The
result uses countable outer-measure subadditivity; it is not a Ville, Doob,
mixture, optional-stopping, or general Freedman theorem.
-/

namespace BanditRLProof.Concentration

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

/-- The optimized quadratic radius evaluated at one index of a parameter
schedule. -/
noncomputable def quadraticFixedMGFScheduledRadius
    (varianceScale varianceBudget tiltCap deltaAt : Nat -> Real)
    (n : Nat) : Real :=
  quadraticFixedMGFRadius
    (varianceScale n) (varianceBudget n) (tiltCap n) (deltaAt n)

/-- A countable family of quadratic fixed-MGF events is controlled by the
sum of its scheduled confidence shares. Event measurability is not required
because `Measure.measure_iUnion_le` is an outer-measure inequality. -/
theorem measure_iUnion_scheduled_deviation_ge_inter_variance_le_tsum_of_fixedTilt_quadratic_tail
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (deviation predictableVariance : Nat -> Omega -> Real)
    (varianceScale varianceBudget tiltCap deltaAt : Nat -> Real)
    (hvarianceScale : forall n, 0 < varianceScale n)
    (hvarianceBudget : forall n, 0 < varianceBudget n)
    (htiltCap : forall n, 0 < tiltCap n)
    (hdeltaAt : forall n, 0 < deltaAt n)
    (hfixed : forall n tilt, 0 <= tilt -> tilt <= tiltCap n ->
      mu {omega |
          quadraticFixedMGFScheduledRadius
                varianceScale varianceBudget tiltCap deltaAt n <=
              deviation n omega ∧
            predictableVariance n omega <= varianceBudget n} <=
        ENNReal.ofReal (Real.exp
          (-tilt * quadraticFixedMGFScheduledRadius
              varianceScale varianceBudget tiltCap deltaAt n +
            varianceScale n * (tilt ^ 2 * varianceBudget n)))) :
    mu (⋃ n, {omega |
        quadraticFixedMGFScheduledRadius
              varianceScale varianceBudget tiltCap deltaAt n <=
            deviation n omega ∧
          predictableVariance n omega <= varianceBudget n}) <=
      ∑' n, ENNReal.ofReal (deltaAt n) := by
  calc
    mu (⋃ n, {omega |
        quadraticFixedMGFScheduledRadius
              varianceScale varianceBudget tiltCap deltaAt n <=
            deviation n omega ∧
          predictableVariance n omega <= varianceBudget n}) <=
        ∑' n, mu {omega |
          quadraticFixedMGFScheduledRadius
                varianceScale varianceBudget tiltCap deltaAt n <=
              deviation n omega ∧
            predictableVariance n omega <= varianceBudget n} :=
      MeasureTheory.measure_iUnion_le _
    _ <= ∑' n, ENNReal.ofReal (deltaAt n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa [quadraticFixedMGFScheduledRadius] using
        (measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
          mu (deviation n) (predictableVariance n)
            (varianceScale n) (varianceBudget n) (tiltCap n) (deltaAt n)
            (hvarianceScale n) (hvarianceBudget n) (htiltCap n) (hdeltaAt n)
            (hfixed n))

/-- A caller-supplied total ENNReal budget turns the scheduled `tsum` bound
into a direct outer confidence bound. -/
theorem measure_iUnion_scheduled_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (deviation predictableVariance : Nat -> Omega -> Real)
    (varianceScale varianceBudget tiltCap deltaAt : Nat -> Real)
    (delta : Real)
    (hvarianceScale : forall n, 0 < varianceScale n)
    (hvarianceBudget : forall n, 0 < varianceBudget n)
    (htiltCap : forall n, 0 < tiltCap n)
    (hdeltaAt : forall n, 0 < deltaAt n)
    (hfixed : forall n tilt, 0 <= tilt -> tilt <= tiltCap n ->
      mu {omega |
          quadraticFixedMGFScheduledRadius
                varianceScale varianceBudget tiltCap deltaAt n <=
              deviation n omega ∧
            predictableVariance n omega <= varianceBudget n} <=
        ENNReal.ofReal (Real.exp
          (-tilt * quadraticFixedMGFScheduledRadius
              varianceScale varianceBudget tiltCap deltaAt n +
            varianceScale n * (tilt ^ 2 * varianceBudget n))))
    (hbudget : (∑' n, ENNReal.ofReal (deltaAt n)) <= ENNReal.ofReal delta) :
    mu (⋃ n, {omega |
        quadraticFixedMGFScheduledRadius
              varianceScale varianceBudget tiltCap deltaAt n <=
            deviation n omega ∧
          predictableVariance n omega <= varianceBudget n}) <=
      ENNReal.ofReal delta :=
  (measure_iUnion_scheduled_deviation_ge_inter_variance_le_tsum_of_fixedTilt_quadratic_tail
    mu deviation predictableVariance varianceScale varianceBudget tiltCap
      deltaAt hvarianceScale hvarianceBudget htiltCap hdeltaAt hfixed).trans
    hbudget

end BanditRLProof.Concentration
