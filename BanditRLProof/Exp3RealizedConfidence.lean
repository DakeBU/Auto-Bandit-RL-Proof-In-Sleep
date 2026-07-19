import BanditRLProof.Exp3RealizedDeviationTail

/-!
# Delta-shaped confidence for realized EXP3 deviation

This module converts the finite-horizon ENNReal Azuma bound into an explicit
square-root confidence radius.  It closes the one-sided confidence theorem for
realized loss minus the exploration-mixed predictable conditional mean; it
does not identify the estimator-valued Hedge comparator with true comparator
loss.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

noncomputable def sampledPredictableRealizedDeviationConfidenceRadius
    (horizon : Nat) (delta : Real) : Real :=
  Real.sqrt
    (2 * ((((horizon : NNReal) *
      Concentration.intervalVarianceProxy 0 1 : NNReal)) : Real) *
        Real.log (1 / delta))

theorem intervalVarianceProxy_zero_one_pos :
    0 < ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) := by
  norm_num [Concentration.intervalVarianceProxy]

theorem sampledPredictableRealizedDeviationConfidenceRadius_nonneg
    (horizon : Nat) (delta : Real) :
    0 <= sampledPredictableRealizedDeviationConfidenceRadius horizon delta := by
  exact Real.sqrt_nonneg _

theorem sampledPredictableRealizedDeviationConfidenceRadius_sq_domination
    (horizon : Nat) (budget : Real) :
    2 * ((((horizon : NNReal) *
        Concentration.intervalVarianceProxy 0 1 : NNReal)) : Real) * budget <=
      (Real.sqrt
        (2 * ((((horizon : NNReal) *
          Concentration.intervalVarianceProxy 0 1 : NNReal)) : Real) * budget)) ^ 2 := by
  rw [Real.sq_sqrt']
  exact le_max_left _ _

theorem sampledPredictableRealizedDeviation_sum_tail_exp_neg_budget
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (hhorizon : 0 < horizon) (budget : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    mu {sample | Real.sqrt
          (2 * ((((horizon : NNReal) *
            Concentration.intervalVarianceProxy 0 1 : NNReal)) : Real) * budget) <=
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample)} <=
      ENNReal.ofReal (Real.exp (-budget)) := by
  dsimp only
  let variance : Real := ((((horizon : NNReal) *
    Concentration.intervalVarianceProxy 0 1 : NNReal)) : Real)
  let radius : Real := Real.sqrt (2 * variance * budget)
  have hvariance_pos : 0 < variance := by
    change 0 < (horizon : Real) *
      ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
    exact mul_pos (by exact_mod_cast hhorizon)
      intervalVarianceProxy_zero_one_pos
  have htail := sampledPredictableRealizedDeviation_sum_tail_ennreal
    prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss horizon
      (eps := radius) (Real.sqrt_nonneg _)
  have hradius_sq : 2 * variance * budget <= radius ^ 2 := by
    dsimp [radius]
    rw [Real.sq_sqrt']
    exact le_max_left _ _
  have hden_pos : 0 < 2 * variance := mul_pos (by norm_num) hvariance_pos
  have hbudget_le : budget <= radius ^ 2 / (2 * variance) := by
    rw [le_div_iff₀ hden_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hradius_sq
  have hexp_le :
      Real.exp (-radius ^ 2 / (2 * variance)) <= Real.exp (-budget) := by
    apply Real.exp_le_exp.mpr
    simpa [neg_div] using neg_le_neg hbudget_le
  exact htail.trans (ENNReal.ofReal_le_ofReal hexp_le)

theorem sampledPredictableRealizedDeviation_sum_tail_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (hhorizon : 0 < horizon) (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    mu {sample |
        sampledPredictableRealizedDeviationConfidenceRadius horizon delta <=
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have htail :=
    sampledPredictableRealizedDeviation_sum_tail_exp_neg_budget
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss horizon
        hhorizon (Real.log (1 / delta))
  have hscale : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hexp : Real.exp (-(Real.log (1 / delta))) = delta := by
    rw [Real.exp_neg, Real.exp_log hscale]
    field_simp
  rw [hexp] at htail
  simpa only [sampledPredictableRealizedDeviationConfidenceRadius] using htail

end BanditRLProof.Exp3
