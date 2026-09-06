import BanditRLProof.Exp3RealizedPredictableVariance

/-!
# Predictable-variance tail for realized EXP3 loss

This module iterates the exact selected-loss variance-compensated conditional
MGF along the generated trajectory. It yields a Bernstein-shaped upper tail
for realized-minus-predictable selected loss jointly with a pathwise budget on
the cumulative selected-loss predictable variance.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Shifted exact-variance compensated realized-loss process. -/
noncomputable def sampledPredictableRealizedCompensatedProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma tilt : Real)
    (loss : PredictableLossVector Env Action) :
    Nat → Env × ((k : Nat) → Action × Real) → Real :=
  fun i sample =>
    tilt * sampledPredictableRealizedDeviationProcess
        arms eta gamma loss i sample -
      tilt ^ 2 * sampledPredictableRealizedVarianceProcess
        arms eta gamma loss i sample

theorem sampledPredictableRealizedCompensatedProcess_stronglyAdapted
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma tilt : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) :
    StronglyAdapted (sampledPredictableDeviationFiltration Env Action)
      (sampledPredictableRealizedCompensatedProcess
        arms eta gamma tilt loss) := by
  have hdeviation :=
    sampledPredictableRealizedDeviationProcess_stronglyAdapted
      arms harms eta gamma hgamma_pos.le hgamma_le_one loss
  have hvariance :=
    (sampledPredictableRealizedVarianceProcess_isPredictable
      arms harms eta gamma hgamma_pos hgamma_le_one loss).adapted
  intro i
  exact ((hdeviation i).const_mul tilt).sub
    ((hvariance i).const_mul (tilt ^ 2))

theorem sampledPredictableRealizedCompensatedProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma tilt : Real)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) → Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledPredictableRealizedCompensatedProcess
          arms eta gamma tilt loss i sample) =
      tilt * (Finset.range horizon).sum (fun i =>
          sampledTrajectoryRealizedDeviationAt
            arms eta gamma loss i sample) -
        tilt ^ 2 * (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss i sample) := by
  simp_rw [sampledPredictableRealizedCompensatedProcess]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sampledPredictableRealizedDeviationProcess_sum_range_succ,
    sampledPredictableRealizedVarianceProcess_sum_range_succ]

/-- Fixed-tilt upper tail retaining the random cumulative selected-loss
predictable variance. -/
theorem sampledPredictableRealizedDeviation_sum_tail_predictableVariance_fixedTilt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (tilt : Real) (htilt_nonneg : 0 ≤ tilt)
    (htilt_le_one : tilt ≤ 1)
    (threshold varianceBudget : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        threshold ≤ (Finset.range horizon).sum (fun i =>
          sampledTrajectoryRealizedDeviationAt
            arms eta gamma loss i sample) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
      ENNReal.ofReal (Real.exp
        (-tilt * threshold + tilt ^ 2 * varianceBudget)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledPredictableRealizedDeviationProcess arms eta gamma loss
  let V := sampledPredictableRealizedVarianceProcess arms eta gamma loss
  let Z := sampledPredictableRealizedCompensatedProcess
    arms eta gamma tilt loss
  let psiZ : Nat → Real := fun _ => 0
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Z := by
    simpa [F, Z] using
      sampledPredictableRealizedCompensatedProcess_stronglyAdapted
        arms harms eta gamma tilt hgamma_pos hgamma_le_one loss
  have hzero : Concentration.HasMGFUpperBoundAt (Z 0) 1 (psiZ 0) mu := by
    have hzero' : Concentration.HasMGFUpperBoundAt
        (fun _ : Env × ((k : Nat) → Action × Real) => 0) 1 0 mu := by
      constructor
      · intro s
        simp
      · simp [ProbabilityTheory.mgf]
    have hZ0 : Z 0 =
        (fun _ : Env × ((k : Nat) → Action × Real) => 0) := by
      funext sample
      simp [Z, sampledPredictableRealizedCompensatedProcess,
        sampledPredictableRealizedDeviationProcess,
        sampledPredictableRealizedVarianceProcess]
    rw [hZ0]
    simpa [psiZ] using hzero'
  have hcond : ∀ i, i < (horizon + 1) - 1 →
      Concentration.HasCondMGFUpperBoundAt
        (F i) (F.le i) (Z (i + 1)) 1 (psiZ (i + 1)) mu := by
    intro i _hi
    cases i with
    | zero =>
        simpa [mu, F, Z, psiZ,
          sampledPredictableRealizedCompensatedProcess,
          sampledPredictableRealizedDeviationProcess,
          sampledPredictableRealizedVarianceProcess] using
          (sampledPredictableRealizedCompensated_zero_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss
              tilt htilt_nonneg htilt_le_one)
    | succ n =>
        simpa [mu, F, Z, psiZ,
          sampledPredictableRealizedCompensatedProcess,
          sampledPredictableRealizedDeviationProcess,
          sampledPredictableRealizedVarianceProcess,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledPredictableRealizedCompensated_succ_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
              tilt htilt_nonneg htilt_le_one)
  have htail :=
    Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
      (μ := mu) (ℱ := F) Y V (horizon + 1) tilt (tilt ^ 2)
        threshold varianceBudget
        (by simpa [Y, V, Z, sampledPredictableRealizedCompensatedProcess]
          using hadapted)
        (by simpa [Y, V, Z, psiZ,
          sampledPredictableRealizedCompensatedProcess] using hzero)
        (by simpa [Y, V, Z, psiZ,
          sampledPredictableRealizedCompensatedProcess] using hcond)
        htilt_nonneg (sq_nonneg tilt)
  simpa [Y, V, sampledPredictableRealizedDeviationProcess_sum_range_succ,
    sampledPredictableRealizedVarianceProcess_sum_range_succ] using htail

/-- Bernstein radius for realized selected-loss deviation under a pathwise
predictable-variance budget. -/
noncomputable def sampledRealizedPredictableVarianceRadius
    (varianceBudget delta : Real) : Real :=
  let budget := max (Real.log (1 / delta)) 0
  2 * Real.sqrt (varianceBudget * budget) + budget

theorem sampledPredictableRealizedDeviation_sum_tail_predictableVariance_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        sampledRealizedPredictableVarianceRadius varianceBudget delta ≤
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryRealizedDeviationAt
              arms eta gamma loss i sample) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let deviation := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample)
  let predictableVariance := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableRealizedVarianceAt
        arms eta gamma loss i sample)
  have htail :=
    Concentration.measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
      mu deviation predictableVariance 1 varianceBudget 1 delta
        (by norm_num) hvarianceBudget (by norm_num) hdelta (by
          intro tilt htilt_nonneg htilt_le_one
          simpa [mu, deviation, predictableVariance] using
            (sampledPredictableRealizedDeviation_sum_tail_predictableVariance_fixedTilt
              prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
                tilt htilt_nonneg htilt_le_one
                (Concentration.quadraticFixedMGFRadius
                  1 varianceBudget 1 delta) varianceBudget))
  simpa [sampledRealizedPredictableVarianceRadius,
    Concentration.quadraticFixedMGFRadius, mu, deviation,
    predictableVariance] using htail

end BanditRLProof.Exp3
