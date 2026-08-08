import BanditRLProof.Exp3MixedSquarePredictableVarianceRealizedMarkovHighProbabilityRegret

/-!
# Loss-energy control of realized predictable-variance EXP3 regret

This module bounds the predictable mixed-square variance by the armwise
predictable loss-square energy. It discharges the Markov route's variance
`lintegral` contract from a pathwise cumulative loss-energy budget.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- A finite-action centered mixed-square estimator has variance at most the
inverse probability floor times the armwise loss-square energy. -/
theorem sum_prob_mul_sq_mixedSquaredEstimatorDeviation_le_inv_floor_mul_sum_loss_sq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action → Real)
    (hdist : FiniteActionDistribution arms prob)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hfloor : ∀ action, action ∈ arms → epsilon ≤ prob action)
    (hloss : ∀ action, action ∈ arms → loss action ∈ Set.Icc (0 : Real) 1) :
    arms.sum (fun chosen =>
        prob chosen *
          (mixedSquaredImportanceWeightedLoss arms prob loss chosen -
            arms.sum (fun action => (loss action) ^ 2)) ^ 2) ≤
      (1 / epsilon) * arms.sum (fun action => (loss action) ^ 2) := by
  let raw := fun chosen =>
    mixedSquaredImportanceWeightedLoss arms prob loss chosen
  let mean := arms.sum (fun action => (loss action) ^ 2)
  have hprob_pos (action : Action) (haction : action ∈ arms) :
      0 < prob action := hepsilon.trans_le (hfloor action haction)
  have hfirst : arms.sum (fun chosen => prob chosen * raw chosen) = mean := by
    simpa [raw, mean] using
      sum_prob_mul_mixedSquaredImportanceWeightedLoss_eq_sum_loss_sq
        arms prob loss (fun action haction => (hprob_pos action haction).ne')
  have hsecond : arms.sum (fun chosen => prob chosen * (raw chosen) ^ 2) =
      arms.sum (fun action => (loss action) ^ 4 / prob action) := by
    simpa [raw] using
      sum_prob_mul_sq_mixedSquaredImportanceWeightedLoss_eq
        arms prob loss (fun action haction => (hprob_pos action haction).ne')
  have hcenter (chosen : Action) :
      prob chosen * (raw chosen - mean) ^ 2 =
        (prob chosen * (raw chosen) ^ 2 -
          2 * mean * (prob chosen * raw chosen)) +
          mean ^ 2 * prob chosen := by
    ring
  have hvariance :
      arms.sum (fun chosen => prob chosen * (raw chosen - mean) ^ 2) =
        arms.sum (fun action => (loss action) ^ 4 / prob action) - mean ^ 2 := by
    simp_rw [hcenter]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hsecond, hfirst, hdist.sum_eq_one]
    ring
  have hfourth_le_sq (action : Action) (haction : action ∈ arms) :
      (loss action) ^ 4 ≤ (loss action) ^ 2 := by
    have hsq_nonneg : 0 ≤ (loss action) ^ 2 := sq_nonneg _
    have hsq_le_one : (loss action) ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (hloss action haction).1 zero_le_one).2
        (hloss action haction).2
    nlinarith [sq_nonneg ((loss action) ^ 2)]
  have hterm (action : Action) (haction : action ∈ arms) :
      (loss action) ^ 4 / prob action ≤
        (1 / epsilon) * (loss action) ^ 2 := by
    have hinv : 1 / prob action ≤ 1 / epsilon :=
      one_div_le_one_div_of_le hepsilon (hfloor action haction)
    calc
      (loss action) ^ 4 / prob action ≤
          (loss action) ^ 2 / prob action :=
        div_le_div_of_nonneg_right (hfourth_le_sq action haction)
          (hprob_pos action haction).le
      _ = (loss action) ^ 2 * (1 / prob action) := by ring
      _ ≤ (loss action) ^ 2 * (1 / epsilon) :=
        mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ = (1 / epsilon) * (loss action) ^ 2 := by ring
  have hsecond_le :
      arms.sum (fun action => (loss action) ^ 4 / prob action) ≤
        (1 / epsilon) * arms.sum (fun action => (loss action) ^ 2) := by
    calc
      arms.sum (fun action => (loss action) ^ 4 / prob action) ≤
          arms.sum (fun action => (1 / epsilon) * (loss action) ^ 2) :=
        Finset.sum_le_sum fun action haction => hterm action haction
      _ = (1 / epsilon) * arms.sum (fun action => (loss action) ^ 2) := by
        rw [Finset.mul_sum]
  change arms.sum (fun chosen => prob chosen * (raw chosen - mean) ^ 2) ≤ _
  rw [hvariance]
  nlinarith [sq_nonneg mean]

theorem mixedSquaredEstimatorCenteredSecondMoment_le_inv_floor_mul_sum_loss_sq
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History → Action → Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    mixedSquaredEstimatorCenteredSecondMoment arms prob loss history ≤
      (1 / epsilon) * arms.sum (fun action => (loss history action) ^ 2) := by
  simpa [mixedSquaredEstimatorCenteredSecondMoment] using
    sum_prob_mul_sq_mixedSquaredEstimatorDeviation_le_inv_floor_mul_sum_loss_sq
      arms (prob history) (loss history) hdist epsilon regularity.epsilon_pos
        (regularity.prob_floor history) (regularity.loss_mem_Icc history)

/-- Pointwise generated-time specialization of the finite loss-energy bound. -/
theorem sampledTrajectoryPredictableMixedSquaredVarianceAt_le_inv_floor_mul_lossSquaredAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss t sample ≤
      (1 / (gamma / (arms.card : Real))) *
        arms.sum (fun action => (predictableLossAt loss t sample action) ^ 2) := by
  exact mixedSquaredEstimatorCenteredSecondMoment_le_inv_floor_mul_sum_loss_sq
    arms
    (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
    (predictableLossAt loss t) sample
    ((sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_pos.le hgamma_le_one t).distribution sample)
    (gamma / (arms.card : Real))
    (sampledPredictableTrajectoryLossRegularityAt arms harms eta gamma
      hgamma_pos hgamma_le_one loss t)

/-- Cumulative predictable variance is controlled by cumulative armwise
predictable loss-square energy. -/
theorem sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossSquaredSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    sampledPredictableMixedSquaredVarianceSum
        arms eta gamma loss horizon sample ≤
      (1 / (gamma / (arms.card : Real))) *
        sampledPredictableLossSquaredSum arms loss horizon sample := by
  unfold sampledPredictableMixedSquaredVarianceSum
  unfold sampledPredictableLossSquaredSum
  calc
    (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample) ≤
      (Finset.range horizon).sum (fun i =>
        (1 / (gamma / (arms.card : Real))) *
          arms.sum (fun action =>
            (predictableLossAt loss i sample action) ^ 2)) :=
      Finset.sum_le_sum fun i _hi =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt_le_inv_floor_mul_lossSquaredAt
          arms harms eta gamma hgamma_pos hgamma_le_one loss i sample
    _ = (1 / (gamma / (arms.card : Real))) *
        (Finset.range horizon).sum (fun i =>
          arms.sum (fun action =>
            (predictableLossAt loss i sample action) ^ 2)) := by
      rw [Finset.mul_sum]

/-- A pathwise predictable loss-square budget yields the generated
cumulative-variance `lintegral` budget required by the Markov route. -/
theorem sampledPredictableMixedSquaredVarianceLIntegral_le_of_lossSquaredSum_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (lossSquaredBudget : Real)
    (henergy : ∀ sample,
      sampledPredictableLossSquaredSum arms loss horizon sample ≤
        lossSquaredBudget) :
    sampledPredictableMixedSquaredVarianceLIntegral
        mu arms eta gamma loss horizon ≤
      ENNReal.ofReal
        ((1 / (gamma / (arms.card : Real))) * lossSquaredBudget) := by
  let varianceSum := sampledPredictableMixedSquaredVarianceSum
    arms eta gamma loss horizon
  have hfloor_pos : 0 < gamma / (arms.card : Real) := by
    exact div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
  have hinv_nonneg : 0 ≤ 1 / (gamma / (arms.card : Real)) :=
    one_div_nonneg.2 hfloor_pos.le
  have hpoint (sample : Env × ((k : Nat) → Action × Real)) :
      varianceSum sample ≤
        (1 / (gamma / (arms.card : Real))) * lossSquaredBudget := by
    exact
      (sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossSquaredSum
        arms harms eta gamma hgamma_pos hgamma_le_one loss horizon sample).trans
      (mul_le_mul_of_nonneg_left (henergy sample) hinv_nonneg)
  calc
    sampledPredictableMixedSquaredVarianceLIntegral
        mu arms eta gamma loss horizon =
      ∫⁻ sample, ENNReal.ofReal (varianceSum sample) ∂mu := by rfl
    _ ≤ ∫⁻ _sample,
        ENNReal.ofReal
          ((1 / (gamma / (arms.card : Real))) * lossSquaredBudget) ∂mu := by
      exact lintegral_mono fun sample => ENNReal.ofReal_le_ofReal (hpoint sample)
    _ = ENNReal.ofReal
        ((1 / (gamma / (arms.card : Real))) * lossSquaredBudget) := by
      simp

/-- Realized Markov budget specialized to a cumulative predictable
loss-square energy budget. -/
noncomputable def sampledPredictableVarianceSquareLossEnergyRealizedMarkovHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (lossSquaredBudget delta : Real) : Real :=
  sampledPredictableVarianceSquareRealizedMarkovHighProbabilityRegretBudget
    arms eta gamma horizon
      ((1 / (gamma / (arms.card : Real))) * lossSquaredBudget) delta

/-- Primary small-loss-energy specialization of the Markov-closed realized
EXP3 theorem. -/
theorem sampledPredictable_predictableVarianceSquareLossEnergyRealizedMarkovHighProbabilityRegret_tail_total_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (lossSquaredBudget delta : Real)
    (hlossSquaredBudget : 0 < lossSquaredBudget) (hdelta : 0 < delta)
    (henergy : ∀ sample,
      sampledPredictableLossSquaredSum arms loss horizon sample ≤
        lossSquaredBudget) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareLossEnergyRealizedMarkovHighProbabilityRegretBudget
            arms eta gamma horizon lossSquaredBudget delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta := by
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
  have hinv_pos : 0 < 1 / (gamma / (arms.card : Real)) :=
    one_div_pos.2 hfloor_pos
  have hmean_pos :
      0 < (1 / (gamma / (arms.card : Real))) * lossSquaredBudget :=
    mul_pos hinv_pos hlossSquaredBudget
  have hvarianceLIntegral :
      sampledPredictableMixedSquaredVarianceLIntegral
          mu arms eta gamma loss horizon ≤
        ENNReal.ofReal
          ((1 / (gamma / (arms.card : Real))) * lossSquaredBudget) :=
    sampledPredictableMixedSquaredVarianceLIntegral_le_of_lossSquaredSum_le
      mu arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
        lossSquaredBudget henergy
  have h :=
    sampledPredictable_predictableVarianceSquareRealizedMarkovHighProbabilityRegret_tail_total_delta
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon
        ((1 / (gamma / (arms.card : Real))) * lossSquaredBudget) delta
        hmean_pos hdelta hvarianceLIntegral
  simpa [sampledPredictableVarianceSquareLossEnergyRealizedMarkovHighProbabilityRegretBudget]
    using h

end BanditRLProof.Exp3
