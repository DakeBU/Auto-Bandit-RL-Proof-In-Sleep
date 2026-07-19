import BanditRLProof.Exp3MixedSquarePredictableVarianceLossEnergyRealizedMarkovHighProbabilityRegret

/-!
# Small-loss control of realized predictable-variance EXP3 regret

This module bounds predictable loss-square energy by armwise predictable loss
mass. It turns an almost-everywhere small-loss budget under the exact generated
trajectory measure into the variance `lintegral` contract used by the
Markov-closed realized regret route. Universal pathwise budgets remain valid
as a special case via `Filter.Eventually.of_forall`.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Every generated predictable loss coordinate remains in the unit interval. -/
theorem predictableLossAt_mem_unitInterval
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) (action : Action) :
    predictableLossAt loss t sample action ∈ Set.Icc (0 : Real) 1 := by
  cases t with
  | zero =>
      simpa [predictableLossAt] using
        loss.initial_mem_unitInterval sample.1 action
  | succ n =>
      simpa [predictableLossAt] using
        loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) action

/-- Cumulative armwise predictable loss mass along a generated trajectory. -/
noncomputable def sampledPredictableLossMassSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) → Action × Real)) : Real :=
  (Finset.range horizon).sum (fun t =>
    arms.sum (fun action => predictableLossAt loss t sample action))

/-- Unit-interval losses have armwise square mass at most armwise loss mass. -/
theorem sampledPredictableLossSquaredAt_le_lossMassAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (t : Nat) (sample : Env × ((k : Nat) → Action × Real)) :
    arms.sum (fun action => (predictableLossAt loss t sample action) ^ 2) ≤
      arms.sum (fun action => predictableLossAt loss t sample action) := by
  apply Finset.sum_le_sum
  intro action _haction
  have hloss := predictableLossAt_mem_unitInterval loss t sample action
  have hproduct :
      0 ≤ predictableLossAt loss t sample action *
        (1 - predictableLossAt loss t sample action) :=
    mul_nonneg hloss.1 (sub_nonneg.mpr hloss.2)
  nlinarith

/-- Cumulative predictable loss-square energy is at most cumulative armwise
predictable loss mass. -/
theorem sampledPredictableLossSquaredSum_le_lossMassSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) → Action × Real)) :
    sampledPredictableLossSquaredSum arms loss horizon sample ≤
      sampledPredictableLossMassSum arms loss horizon sample := by
  unfold sampledPredictableLossSquaredSum sampledPredictableLossMassSum
  exact Finset.sum_le_sum fun t _ht =>
    sampledPredictableLossSquaredAt_le_lossMassAt arms loss t sample

/-- Cumulative predictable mixed-square variance is controlled by armwise
predictable loss mass. -/
theorem sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossMassSum
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
        sampledPredictableLossMassSum arms loss horizon sample := by
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
  exact
    (sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossSquaredSum
      arms harms eta gamma hgamma_pos hgamma_le_one loss horizon sample).trans
      (mul_le_mul_of_nonneg_left
        (sampledPredictableLossSquaredSum_le_lossMassSum
          arms loss horizon sample)
        (one_div_nonneg.2 hfloor_pos.le))

/-- An almost-everywhere armwise loss-mass budget supplies the
cumulative-variance `lintegral` contract required by the Markov route. -/
theorem sampledPredictableMixedSquaredVarianceLIntegral_le_of_lossMassSum_le
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
    (lossMassBudget : Real)
    (hmass : ∀ᵐ sample ∂mu,
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget) :
    sampledPredictableMixedSquaredVarianceLIntegral
        mu arms eta gamma loss horizon ≤
      ENNReal.ofReal
        ((1 / (gamma / (arms.card : Real))) * lossMassBudget) := by
  let varianceSum := sampledPredictableMixedSquaredVarianceSum
    arms eta gamma loss horizon
  have hfloor_pos : 0 < gamma / (arms.card : Real) := by
    exact div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
  have hinv_nonneg : 0 ≤ 1 / (gamma / (arms.card : Real)) :=
    one_div_nonneg.2 hfloor_pos.le
  have hpoint : ∀ᵐ sample ∂mu,
      varianceSum sample ≤
        (1 / (gamma / (arms.card : Real))) * lossMassBudget := by
    filter_upwards [hmass] with sample hsample
    exact
      (sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossMassSum
        arms harms eta gamma hgamma_pos hgamma_le_one loss horizon sample).trans
        (mul_le_mul_of_nonneg_left hsample hinv_nonneg)
  calc
    sampledPredictableMixedSquaredVarianceLIntegral
        mu arms eta gamma loss horizon =
      ∫⁻ sample, ENNReal.ofReal (varianceSum sample) ∂mu := by rfl
    _ ≤ ∫⁻ _sample,
        ENNReal.ofReal
          ((1 / (gamma / (arms.card : Real))) * lossMassBudget) ∂mu := by
      exact lintegral_mono_ae
        (hpoint.mono fun _sample hsample => ENNReal.ofReal_le_ofReal hsample)
    _ = ENNReal.ofReal
        ((1 / (gamma / (arms.card : Real))) * lossMassBudget) := by
      simp

/-- Off-bad observed-square tail when the armwise loss-mass budget may fail
on an explicit bad set. No measurability assumption on that set is needed. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_off_bad_of_lossMassSum_le_or_mem
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (lossMassBudget varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta)
    (bad : Set (Env × ((k : Nat) → Action × Real)))
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_le_one loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget ∨ sample ∈ bad) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu ({sample |
        lossMassBudget +
            sampledMixedSquaredPredictableVarianceRadius
              arms gamma varianceBudget delta ≤
          sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} \ bad) ≤
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let radius := sampledMixedSquaredPredictableVarianceRadius
    arms gamma varianceBudget delta
  let centeredBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      radius ≤ (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss i sample) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget}
  have htail :=
    sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
        varianceBudget delta hvarianceBudget hdelta
  have heq := sampledObservedMixedSquaredSum_eq_predictable_ae
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss horizon
  have hsubset : ∀ᵐ sample ∂mu,
      sample ∈ ({sample |
          lossMassBudget + radius ≤
            sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample) ≤ varianceBudget} \ bad) →
        sample ∈ centeredBad := by
    filter_upwards [heq, hmass] with sample hobs hmassSample
    intro hsample
    rcases hmassSample with hmassSample | hbad
    · have hsource := hsample.1
      simp only [Set.mem_setOf_eq] at hsource
      refine ⟨?_, hsource.2⟩
      have hmean :=
        (sampledPredictableLossSquaredSum_le_lossMassSum
          arms loss horizon sample).trans hmassSample
      have hcentered := sampledPredictableMixedSquaredDeviation_sum_eq
        arms eta gamma loss horizon sample
      rw [hobs] at hsource
      linarith
    · exact (hsample.2 hbad).elim
  calc
    mu ({sample |
        lossMassBudget + radius ≤
            sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample) ≤ varianceBudget} \ bad) ≤
        mu centeredBad := measure_mono_ae hsubset
    _ ≤ ENNReal.ofReal delta := by
      simpa [mu, radius, centeredBad] using htail

/-- Residual observed-square tail when the armwise loss-mass budget may fail
on an explicit bad set. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_of_lossMassSum_le_or_mem
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (lossMassBudget varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta)
    (bad : Set (Env × ((k : Nat) → Action × Real)))
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_le_one loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget ∨ sample ∈ bad) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        lossMassBudget +
            sampledMixedSquaredPredictableVarianceRadius
              arms gamma varianceBudget delta ≤
          sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
      ENNReal.ofReal delta + mu bad := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let radius := sampledMixedSquaredPredictableVarianceRadius
    arms gamma varianceBudget delta
  let centeredBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      radius ≤ (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss i sample) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget}
  have htail :=
    sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
        varianceBudget delta hvarianceBudget hdelta
  have heq := sampledObservedMixedSquaredSum_eq_predictable_ae
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss horizon
  have hsubset : ∀ᵐ sample ∂mu,
      (lossMassBudget + radius ≤
          sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget) →
      sample ∈ centeredBad ∪ bad := by
    filter_upwards [heq, hmass] with sample hobs hmassSample
    intro hsample
    rcases hmassSample with hmassSample | hbad
    · left
      refine ⟨?_, hsample.2⟩
      have hmean :=
        (sampledPredictableLossSquaredSum_le_lossMassSum
          arms loss horizon sample).trans hmassSample
      have hcentered := sampledPredictableMixedSquaredDeviation_sum_eq
        arms eta gamma loss horizon sample
      rw [hobs] at hsample
      linarith
    · exact Or.inr hbad
  calc
    mu {sample |
        lossMassBudget + radius ≤
            sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample) ≤ varianceBudget} ≤
        mu (centeredBad ∪ bad) := measure_mono_ae hsubset
    _ ≤ mu centeredBad + mu bad := measure_union_le _ _
    _ ≤ ENNReal.ofReal delta + mu bad := by
      exact add_le_add
        (by simpa [mu, radius, centeredBad] using htail) le_rfl

/-- The observed mixed estimator-square sum has its predictable mean bounded by
the supplied almost-everywhere armwise loss-mass budget. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_of_lossMassSum_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (lossMassBudget varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta)
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_le_one loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        lossMassBudget +
            sampledMixedSquaredPredictableVarianceRadius
              arms gamma varianceBudget delta ≤
          sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
      ENNReal.ofReal delta := by
  have h :=
    sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_of_lossMassSum_le_or_mem
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
        lossMassBudget varianceBudget delta hvarianceBudget hdelta ∅
        (hmass.mono fun _sample hsample => Or.inl hsample)
  simpa using h

/-- Predictable regret budget whose mixed-square mean upper bound is the
supplied armwise loss-mass budget rather than `K * T`. -/
noncomputable def sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (lossMassBudget varianceBudget deltaSquare deltaConfidence : Real) : Real :=
  Real.log arms.card / eta +
    (eta * (1 / (1 - gamma))) *
      (lossMassBudget +
        sampledMixedSquaredPredictableVarianceRadius
          arms gamma varianceBudget deltaSquare) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence

/-- Off-bad predictable small-loss regret on the variance-good event. The
explicit bad set is removed from the source event, so it does not enter the
confidence allocation. -/
theorem sampledPredictable_predictableVarianceSquareSmallLossHighProbabilityRegret_tail_joint_off_bad_of_lossMassSum_le_or_mem
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
    (horizon : Nat) (lossMassBudget varianceBudget : Real)
    (deltaSquare deltaConfidence : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (bad : Set (Env × ((k : Nat) → Action × Real)))
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget ∨ sample ∈ bad) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu ({sample |
        sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} \ bad) ≤
      (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let purePredictable := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample)
  let pureObserved := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryPureObservedLossAt arms eta gamma t sample)
  let comparatorObserved := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      observedImportanceWeightedLossAt arms eta gamma t sample comparator)
  let comparatorTrue := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      predictableLossAt loss t sample comparator)
  let exploredPredictable := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryExploredPredictableLossAt arms eta gamma loss t sample)
  let secondMoment := sampledObservedMixedSquaredSum
    (Env := Env) arms eta gamma horizon
  let predictableVariance := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  let secondMomentBudget := lossMassBudget +
    sampledMixedSquaredPredictableVarianceRadius
      arms gamma varianceBudget deltaSquare
  let pureRadius :=
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence
  let comparatorRadius := sampledComparatorEstimatorBernsteinConfidenceRadius
    arms gamma horizon deltaConfidence
  let secondMomentBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | secondMomentBudget ≤ secondMoment sample}
  let varianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | predictableVariance sample ≤ varianceBudget}
  let pureBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | pureRadius ≤ purePredictable sample - pureObserved sample}
  let comparatorBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | comparatorRadius ≤ comparatorObserved sample - comparatorTrue sample}
  let regretJoint : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence ≤
          exploredPredictable sample - comparatorTrue sample ∧
        predictableVariance sample ≤ varianceBudget}
  have hsecondTail : mu ((secondMomentBad ∩ varianceGood) \ bad) ≤
      ENNReal.ofReal deltaSquare := by
    have h :=
      sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_off_bad_of_lossMassSum_le_or_mem
        prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
          lossMassBudget varianceBudget deltaSquare hvarianceBudget
          hdeltaSquare bad hmass
    dsimp only at h
    simpa [mu, secondMomentBad, varianceGood, secondMomentBudget, secondMoment,
      predictableVariance] using h
  have hpureTail : mu pureBad ≤ ENNReal.ofReal deltaConfidence := by
    have h := sampledPurePredictableMinusObserved_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss
        horizon deltaConfidence hdeltaConfidence
    dsimp only at h
    simpa [mu, pureBad, pureRadius, purePredictable, pureObserved] using h
  have hcomparatorTail : mu comparatorBad ≤ ENNReal.ofReal deltaConfidence := by
    have h := sampledObservedComparatorEstimatorDeviation_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss comparator
        hcomparator horizon deltaConfidence hdeltaConfidence
    dsimp only at h
    simpa [mu, comparatorBad, comparatorRadius, comparatorObserved,
      comparatorTrue,
      sampledTrajectoryObservedComparatorEstimatorDeviationAt] using h
  have hhedge :=
    sampledPredictableTrajectoryMeasure_hedge_exploredSecondMoment_le_ae
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss horizon
        comparator hcomparator
  dsimp only at hhedge
  have hsubset : ∀ᵐ sample ∂mu,
      sample ∈ regretJoint \ bad →
        sample ∈ ((secondMomentBad ∩ varianceGood) \ bad ∪ pureBad) ∪
          comparatorBad := by
    filter_upwards [hhedge] with sample hsampleHedge
    intro hregret
    have hregretSource := hregret.1
    simp only [regretJoint, Set.mem_setOf_eq] at hregretSource
    by_cases hsecond : sample ∈ secondMomentBad
    · exact Or.inl (Or.inl ⟨⟨hsecond, hregretSource.2⟩, hregret.2⟩)
    by_cases hpure : sample ∈ pureBad
    · exact Or.inl (Or.inr hpure)
    by_cases hcomparator : sample ∈ comparatorBad
    · exact Or.inr hcomparator
    exfalso
    have hsecondGood : secondMoment sample < secondMomentBudget := by
      change ¬ secondMomentBudget ≤ secondMoment sample at hsecond
      exact lt_of_not_ge hsecond
    have hpureGood :
        purePredictable sample - pureObserved sample < pureRadius := by
      change ¬ pureRadius ≤ purePredictable sample - pureObserved sample at hpure
      exact lt_of_not_ge hpure
    have hcomparatorGood :
        comparatorObserved sample - comparatorTrue sample <
          comparatorRadius := by
      change ¬ comparatorRadius ≤
        comparatorObserved sample - comparatorTrue sample at hcomparator
      exact lt_of_not_ge hcomparator
    have hexploration :
        exploredPredictable sample ≤
          purePredictable sample + gamma * (horizon : Real) := by
      have h := (sampledTrajectory_finiteHorizon_explorationBias_secondMoment
        arms harms eta gamma hgamma_pos.le hgamma_lt_one loss horizon sample).1
      simpa [exploredPredictable, purePredictable,
        sampledTrajectoryExploredPredictableLossAt,
        sampledTrajectoryPurePredictableLossAt,
        sampledTrajectoryPureProbabilityAt] using h
    have hcoef_pos : 0 < eta * (1 / (1 - gamma)) :=
      mul_pos heta (one_div_pos.mpr (sub_pos.mpr hgamma_lt_one))
    have hweightedSecond :
        (eta * (1 / (1 - gamma))) * secondMoment sample <
          (eta * (1 / (1 - gamma))) * secondMomentBudget :=
      mul_lt_mul_of_pos_left hsecondGood hcoef_pos
    have hhedge' :
        pureObserved sample - comparatorObserved sample ≤
          Real.log arms.card / eta +
            (eta * (1 / (1 - gamma))) * secondMoment sample := by
      simpa [pureObserved, comparatorObserved, secondMoment,
        sampledObservedMixedSquaredSum] using hsampleHedge
    have hfinal : exploredPredictable sample - comparatorTrue sample <
        sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
          arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
            deltaConfidence := by
      dsimp [sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget,
        secondMomentBudget, pureRadius, comparatorRadius]
      linarith
    exact (not_lt_of_ge hregretSource.1) hfinal
  change mu (regretJoint \ bad) ≤
    (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
      ENNReal.ofReal deltaConfidence
  calc
    mu (regretJoint \ bad) ≤
        mu (((secondMomentBad ∩ varianceGood) \ bad ∪ pureBad) ∪
          comparatorBad) := measure_mono_ae hsubset
    _ ≤ (mu ((secondMomentBad ∩ varianceGood) \ bad) + mu pureBad) +
        mu comparatorBad := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence :=
      add_le_add (add_le_add hsecondTail hpureTail) hcomparatorTail

/-- Residual small-loss predictable regret on the variance-good event when the
loss-mass budget may fail on an explicit bad set. -/
theorem sampledPredictable_predictableVarianceSquareSmallLossHighProbabilityRegret_tail_joint_of_lossMassSum_le_or_mem
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
    (horizon : Nat) (lossMassBudget varianceBudget : Real)
    (deltaSquare deltaConfidence : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (bad : Set (Env × ((k : Nat) → Action × Real)))
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget ∨ sample ∈ bad) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
      (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence + mu bad := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let purePredictable := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample)
  let pureObserved := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryPureObservedLossAt arms eta gamma t sample)
  let comparatorObserved := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      observedImportanceWeightedLossAt arms eta gamma t sample comparator)
  let comparatorTrue := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      predictableLossAt loss t sample comparator)
  let exploredPredictable := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryExploredPredictableLossAt arms eta gamma loss t sample)
  let secondMoment := sampledObservedMixedSquaredSum
    (Env := Env) arms eta gamma horizon
  let predictableVariance := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  let secondMomentBudget := lossMassBudget +
    sampledMixedSquaredPredictableVarianceRadius
      arms gamma varianceBudget deltaSquare
  let pureRadius :=
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence
  let comparatorRadius := sampledComparatorEstimatorBernsteinConfidenceRadius
    arms gamma horizon deltaConfidence
  let secondMomentBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | secondMomentBudget ≤ secondMoment sample}
  let varianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | predictableVariance sample ≤ varianceBudget}
  let pureBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | pureRadius ≤ purePredictable sample - pureObserved sample}
  let comparatorBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | comparatorRadius ≤ comparatorObserved sample - comparatorTrue sample}
  have hsecondTail : mu (secondMomentBad ∩ varianceGood) ≤
      ENNReal.ofReal deltaSquare + mu bad := by
    have h :=
      sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_of_lossMassSum_le_or_mem
        prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
          lossMassBudget varianceBudget deltaSquare hvarianceBudget
          hdeltaSquare bad hmass
    dsimp only at h
    simpa [mu, secondMomentBad, varianceGood, secondMomentBudget, secondMoment,
      predictableVariance] using h
  have hpureTail : mu pureBad ≤ ENNReal.ofReal deltaConfidence := by
    have h := sampledPurePredictableMinusObserved_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss
        horizon deltaConfidence hdeltaConfidence
    dsimp only at h
    simpa [mu, pureBad, pureRadius, purePredictable, pureObserved] using h
  have hcomparatorTail : mu comparatorBad ≤ ENNReal.ofReal deltaConfidence := by
    have h := sampledObservedComparatorEstimatorDeviation_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss comparator
        hcomparator horizon deltaConfidence hdeltaConfidence
    dsimp only at h
    simpa [mu, comparatorBad, comparatorRadius, comparatorObserved,
      comparatorTrue,
      sampledTrajectoryObservedComparatorEstimatorDeviationAt] using h
  have hhedge :=
    sampledPredictableTrajectoryMeasure_hedge_exploredSecondMoment_le_ae
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss horizon
        comparator hcomparator
  dsimp only at hhedge
  have hsubset : ∀ᵐ sample ∂mu,
      (sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence ≤ exploredPredictable sample - comparatorTrue sample ∧
        predictableVariance sample ≤ varianceBudget) →
      sample ∈ ((secondMomentBad ∩ varianceGood) ∪ pureBad) ∪ comparatorBad := by
    filter_upwards [hhedge] with sample hsampleHedge
    intro hregret
    by_cases hsecond : sample ∈ secondMomentBad
    · exact Or.inl (Or.inl ⟨hsecond, hregret.2⟩)
    by_cases hpure : sample ∈ pureBad
    · exact Or.inl (Or.inr hpure)
    by_cases hcomparator : sample ∈ comparatorBad
    · exact Or.inr hcomparator
    exfalso
    have hsecondGood : secondMoment sample < secondMomentBudget := by
      change ¬ secondMomentBudget ≤ secondMoment sample at hsecond
      exact lt_of_not_ge hsecond
    have hpureGood :
        purePredictable sample - pureObserved sample < pureRadius := by
      change ¬ pureRadius ≤ purePredictable sample - pureObserved sample at hpure
      exact lt_of_not_ge hpure
    have hcomparatorGood :
        comparatorObserved sample - comparatorTrue sample <
          comparatorRadius := by
      change ¬ comparatorRadius ≤
        comparatorObserved sample - comparatorTrue sample at hcomparator
      exact lt_of_not_ge hcomparator
    have hexploration :
        exploredPredictable sample ≤
          purePredictable sample + gamma * (horizon : Real) := by
      have h := (sampledTrajectory_finiteHorizon_explorationBias_secondMoment
        arms harms eta gamma hgamma_pos.le hgamma_lt_one loss horizon sample).1
      simpa [exploredPredictable, purePredictable,
        sampledTrajectoryExploredPredictableLossAt,
        sampledTrajectoryPurePredictableLossAt,
        sampledTrajectoryPureProbabilityAt] using h
    have hcoef_pos : 0 < eta * (1 / (1 - gamma)) :=
      mul_pos heta (one_div_pos.mpr (sub_pos.mpr hgamma_lt_one))
    have hweightedSecond :
        (eta * (1 / (1 - gamma))) * secondMoment sample <
          (eta * (1 / (1 - gamma))) * secondMomentBudget :=
      mul_lt_mul_of_pos_left hsecondGood hcoef_pos
    have hhedge' :
        pureObserved sample - comparatorObserved sample ≤
          Real.log arms.card / eta +
            (eta * (1 / (1 - gamma))) * secondMoment sample := by
      simpa [pureObserved, comparatorObserved, secondMoment,
        sampledObservedMixedSquaredSum] using hsampleHedge
    have hfinal : exploredPredictable sample - comparatorTrue sample <
        sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
          arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
            deltaConfidence := by
      dsimp [sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget,
        secondMomentBudget, pureRadius, comparatorRadius]
      linarith
    exact (not_lt_of_ge hregret.1) hfinal
  calc
    mu {sample |
        sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
        mu ((secondMomentBad ∩ varianceGood) ∪ pureBad ∪ comparatorBad) := by
      apply measure_mono_ae
      filter_upwards [hsubset] with sample hs
      intro hsource
      apply hs
      refine ⟨?_, ?_⟩
      · simpa [exploredPredictable, comparatorTrue] using hsource.1
      · simpa [predictableVariance] using hsource.2
    _ ≤ (mu (secondMomentBad ∩ varianceGood) + mu pureBad) +
        mu comparatorBad := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence + mu bad := by
      calc
        (mu (secondMomentBad ∩ varianceGood) + mu pureBad) +
            mu comparatorBad ≤
          ((ENNReal.ofReal deltaSquare + mu bad) +
              ENNReal.ofReal deltaConfidence) +
            ENNReal.ofReal deltaConfidence :=
          add_le_add (add_le_add hsecondTail hpureTail) hcomparatorTail
        _ = (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
            ENNReal.ofReal deltaConfidence + mu bad := by
          simp only [add_assoc, add_left_comm, add_comm]

/-- Small-loss predictable regret on the event that cumulative predictable
mixed-square variance stays below `varianceBudget`. -/
theorem sampledPredictable_predictableVarianceSquareSmallLossHighProbabilityRegret_tail_joint
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
    (horizon : Nat) (lossMassBudget varianceBudget : Real)
    (deltaSquare deltaConfidence : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
      (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence := by
  have h :=
    sampledPredictable_predictableVarianceSquareSmallLossHighProbabilityRegret_tail_joint_of_lossMassSum_le_or_mem
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon lossMassBudget varianceBudget deltaSquare
          deltaConfidence hvarianceBudget hdeltaSquare hdeltaConfidence ∅
            (hmass.mono fun _sample hsample => Or.inl hsample)
  simpa using h

/-- Realized small-loss regret budget with a caller-supplied predictable
variance budget. -/
noncomputable def sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (lossMassBudget varianceBudget deltaSquare deltaConfidence deltaRealized : Real) : Real :=
  sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
        deltaConfidence +
    sampledPredictableRealizedDeviationConfidenceRadius horizon deltaRealized

/-- Off-bad realized small-loss regret on the predictable-variance-good event.
The four confidence events are charged here; the explicit bad set can be
charged once by a downstream pathwise decomposition. -/
theorem sampledPredictable_predictableVarianceSquareSmallLossRealizedHighProbabilityRegret_tail_joint_off_bad_of_lossMassSum_le_or_mem
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
    (lossMassBudget varianceBudget : Real)
    (deltaSquare deltaConfidence deltaRealized : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized)
    (bad : Set (Env × ((k : Nat) → Action × Real)))
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget ∨ sample ∈ bad) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu ({sample |
        sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} \ bad) ≤
      ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let predictableRegret := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample) -
      (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator)
  let realizedDeviation := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryRealizedDeviationAt arms eta gamma loss t sample)
  let realizedRegret := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedLossAt t sample) -
      (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator)
  let varianceSum := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  let predictableBudget :=
    sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
        deltaConfidence
  let realizedRadius :=
    sampledPredictableRealizedDeviationConfidenceRadius horizon deltaRealized
  let predictableBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | predictableBudget ≤ predictableRegret sample}
  let varianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | varianceSum sample ≤ varianceBudget}
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | realizedRadius ≤ realizedDeviation sample}
  let regretJoint : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      predictableBudget + realizedRadius ≤ realizedRegret sample ∧
        varianceSum sample ≤ varianceBudget}
  have hpredictableTail :
      mu ((predictableBad ∩ varianceGood) \ bad) ≤
        (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence := by
    have h :=
      sampledPredictable_predictableVarianceSquareSmallLossHighProbabilityRegret_tail_joint_off_bad_of_lossMassSum_le_or_mem
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon lossMassBudget varianceBudget deltaSquare
          deltaConfidence hvarianceBudget hdeltaSquare hdeltaConfidence bad hmass
    dsimp only at h
    simpa [mu, predictableBad, varianceGood, predictableBudget,
      predictableRegret, varianceSum] using h
  have hrealizedTail : mu realizedBad ≤ ENNReal.ofReal deltaRealized := by
    have h := sampledPredictableRealizedDeviation_sum_tail_delta
      prior arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss horizon
        hhorizon deltaRealized hdeltaRealized
    dsimp only at h
    simpa [mu, realizedBad, realizedRadius, realizedDeviation] using h
  have hdecomp : ∀ sample,
      realizedRegret sample = predictableRegret sample + realizedDeviation sample := by
    intro sample
    dsimp [realizedRegret, predictableRegret, realizedDeviation,
      sampledTrajectoryRealizedDeviationAt]
    rw [Finset.sum_sub_distrib]
    ring
  have hsubset :
      regretJoint \ bad ⊆
        ((predictableBad ∩ varianceGood) \ bad) ∪ realizedBad := by
    intro sample hregret
    have hregretSource := hregret.1
    simp only [regretJoint, Set.mem_setOf_eq] at hregretSource
    by_cases hpredictable : sample ∈ predictableBad
    · exact Or.inl ⟨⟨hpredictable, hregretSource.2⟩, hregret.2⟩
    by_cases hrealized : sample ∈ realizedBad
    · exact Or.inr hrealized
    exfalso
    have hpredictableGood : predictableRegret sample < predictableBudget := by
      change ¬ predictableBudget ≤ predictableRegret sample at hpredictable
      exact lt_of_not_ge hpredictable
    have hrealizedGood : realizedDeviation sample < realizedRadius := by
      change ¬ realizedRadius ≤ realizedDeviation sample at hrealized
      exact lt_of_not_ge hrealized
    have hregret' :
        predictableBudget + realizedRadius ≤ realizedRegret sample :=
      hregretSource.1
    rw [hdecomp sample] at hregret'
    linarith
  change mu (regretJoint \ bad) ≤
    ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
      ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized
  calc
    mu (regretJoint \ bad) ≤
        mu (((predictableBad ∩ varianceGood) \ bad) ∪ realizedBad) :=
      measure_mono hsubset
    _ ≤ mu ((predictableBad ∩ varianceGood) \ bad) + mu realizedBad :=
      measure_union_le _ _
    _ ≤ ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized :=
      add_le_add hpredictableTail hrealizedTail

/-- Residual realized small-loss regret on the predictable-variance-good event
when the loss-mass budget may fail on an explicit bad set. -/
theorem sampledPredictable_predictableVarianceSquareSmallLossRealizedHighProbabilityRegret_tail_joint_of_lossMassSum_le_or_mem
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
    (lossMassBudget varianceBudget : Real)
    (deltaSquare deltaConfidence deltaRealized : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized)
    (bad : Set (Env × ((k : Nat) → Action × Real)))
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget ∨ sample ∈ bad) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
      ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized +
          (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
            eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment) bad := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let predictableRegret := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
        sampledTrajectoryExploredPredictableLossAt
          arms eta gamma loss t sample) -
      (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator)
  let realizedDeviation := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryRealizedDeviationAt arms eta gamma loss t sample)
  let realizedRegret := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedLossAt t sample) -
      (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator)
  let varianceSum := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  let predictableBudget :=
    sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
        deltaConfidence
  let realizedRadius :=
    sampledPredictableRealizedDeviationConfidenceRadius horizon deltaRealized
  let predictableBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | predictableBudget ≤ predictableRegret sample}
  let varianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | varianceSum sample ≤ varianceBudget}
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | realizedRadius ≤ realizedDeviation sample}
  have hpredictableTail : mu (predictableBad ∩ varianceGood) ≤
      (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence + mu bad := by
    have h :=
      sampledPredictable_predictableVarianceSquareSmallLossHighProbabilityRegret_tail_joint_of_lossMassSum_le_or_mem
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon lossMassBudget varianceBudget deltaSquare
          deltaConfidence hvarianceBudget hdeltaSquare hdeltaConfidence bad hmass
    dsimp only at h
    simpa [mu, predictableBad, varianceGood, predictableBudget,
      predictableRegret, varianceSum] using h
  have hrealizedTail : mu realizedBad ≤ ENNReal.ofReal deltaRealized := by
    have h := sampledPredictableRealizedDeviation_sum_tail_delta
      prior arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss horizon
        hhorizon deltaRealized hdeltaRealized
    dsimp only at h
    simpa [mu, realizedBad, realizedRadius, realizedDeviation] using h
  have hdecomp : ∀ sample,
      realizedRegret sample = predictableRegret sample + realizedDeviation sample := by
    intro sample
    dsimp [realizedRegret, predictableRegret, realizedDeviation,
      sampledTrajectoryRealizedDeviationAt]
    rw [Finset.sum_sub_distrib]
    ring
  have hsubset :
      {sample |
          predictableBudget + realizedRadius ≤ realizedRegret sample ∧
          varianceSum sample ≤ varianceBudget} ⊆
        (predictableBad ∩ varianceGood) ∪ realizedBad := by
    intro sample hregret
    by_cases hpredictable : sample ∈ predictableBad
    · exact Or.inl ⟨hpredictable, hregret.2⟩
    by_cases hrealized : sample ∈ realizedBad
    · exact Or.inr hrealized
    exfalso
    have hpredictableGood : predictableRegret sample < predictableBudget := by
      change ¬ predictableBudget ≤ predictableRegret sample at hpredictable
      exact lt_of_not_ge hpredictable
    have hrealizedGood : realizedDeviation sample < realizedRadius := by
      change ¬ realizedRadius ≤ realizedDeviation sample at hrealized
      exact lt_of_not_ge hrealized
    have hregret' :
        predictableBudget + realizedRadius ≤ realizedRegret sample := hregret.1
    rw [hdecomp sample] at hregret'
    linarith
  calc
    mu {sample |
        sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
        mu ((predictableBad ∩ varianceGood) ∪ realizedBad) := by
      apply measure_mono
      simpa [sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget,
        predictableBudget, realizedRadius, realizedRegret, varianceSum, mu]
        using hsubset
    _ ≤ mu (predictableBad ∩ varianceGood) + mu realizedBad :=
      measure_union_le _ _
    _ ≤ ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized +
            mu bad := by
      calc
        mu (predictableBad ∩ varianceGood) + mu realizedBad ≤
            (((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
                ENNReal.ofReal deltaConfidence) + mu bad) +
              ENNReal.ofReal deltaRealized :=
          add_le_add hpredictableTail hrealizedTail
        _ = ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
              ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized +
                mu bad := by
          simp only [add_assoc, add_left_comm, add_comm]

/-- Realized small-loss regret on the predictable-variance-good event. -/
theorem sampledPredictable_predictableVarianceSquareSmallLossRealizedHighProbabilityRegret_tail_joint
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
    (lossMassBudget varianceBudget : Real)
    (deltaSquare deltaConfidence deltaRealized : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized)
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget varianceBudget deltaSquare
              deltaConfidence deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ varianceBudget} ≤
      ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized := by
  have h :=
    sampledPredictable_predictableVarianceSquareSmallLossRealizedHighProbabilityRegret_tail_joint_of_lossMassSum_le_or_mem
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon lossMassBudget varianceBudget deltaSquare
          deltaConfidence deltaRealized hvarianceBudget hdeltaSquare
            hdeltaConfidence hdeltaRealized ∅
              (hmass.mono fun _sample hsample => Or.inl hsample)
  simpa using h

/-- Five-event small-loss realized budget: the mixed-square predictable mean is
`lossMassBudget`, while the Markov variance mean is
`(1 / (gamma / K)) * lossMassBudget`. -/
noncomputable def sampledPredictableVarianceSquareSmallLossRealizedMarkovHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (lossMassBudget delta : Real) : Real :=
  sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
    arms eta gamma horizon lossMassBudget
      (((1 / (gamma / (arms.card : Real))) * lossMassBudget) / (delta / 5))
      (delta / 5) (delta / 5) (delta / 5)

/-- Primary armwise small-loss specialization of the Markov-closed realized
EXP3 theorem. -/
theorem sampledPredictable_predictableVarianceSquareSmallLossRealizedMarkovHighProbabilityRegret_tail_total_delta
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
    (lossMassBudget delta : Real)
    (hlossMassBudget : 0 < lossMassBudget) (hdelta : 0 < delta)
    (hmass : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareSmallLossRealizedMarkovHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta := by
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let varianceMeanBudget :=
    (1 / (gamma / (arms.card : Real))) * lossMassBudget
  let varianceBudget := varianceMeanBudget / (delta / 5)
  let realizedBudget :=
    sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget varianceBudget
        (delta / 5) (delta / 5) (delta / 5)
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      realizedBudget ≤
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  let varianceSum := sampledPredictableMixedSquaredVarianceSum
    arms eta gamma loss horizon
  let varianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | varianceSum sample ≤ varianceBudget}
  let varianceBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | varianceBudget < varianceSum sample}
  have hfifth_pos : 0 < delta / 5 := div_pos hdelta (by norm_num)
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
  have hmean_pos : 0 < varianceMeanBudget := by
    dsimp [varianceMeanBudget]
    exact mul_pos (one_div_pos.2 hfloor_pos) hlossMassBudget
  have hvarianceBudget : 0 < varianceBudget := by
    exact div_pos hmean_pos hfifth_pos
  have hjoint : mu (realizedBad ∩ varianceGood) ≤
      ((ENNReal.ofReal (delta / 5) + ENNReal.ofReal (delta / 5)) +
        ENNReal.ofReal (delta / 5)) + ENNReal.ofReal (delta / 5) := by
    have h :=
      sampledPredictable_predictableVarianceSquareSmallLossRealizedHighProbabilityRegret_tail_joint
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon hhorizon lossMassBudget varianceBudget
          (delta / 5) (delta / 5) (delta / 5) hvarianceBudget
          hfifth_pos hfifth_pos hfifth_pos hmass
    dsimp only at h
    simpa [mu, realizedBad, varianceGood, varianceSum, realizedBudget] using h
  have hvarianceLIntegral :
      sampledPredictableMixedSquaredVarianceLIntegral
          mu arms eta gamma loss horizon ≤ ENNReal.ofReal varianceMeanBudget := by
    simpa [varianceMeanBudget] using
      sampledPredictableMixedSquaredVarianceLIntegral_le_of_lossMassSum_le
        mu arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
          lossMassBudget hmass
  have hoverflowBase :=
    measure_sampledPredictableMixedSquaredVarianceSum_gt_le_lintegral_div
      mu arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
        varianceBudget hvarianceBudget
  have hmean_ne_zero : ENNReal.ofReal varianceMeanBudget ≠ 0 :=
    (ENNReal.ofReal_pos.2 hmean_pos).ne'
  have hratio :
      ENNReal.ofReal varianceMeanBudget / ENNReal.ofReal varianceBudget =
        ENNReal.ofReal (delta / 5) := by
    dsimp [varianceBudget]
    rw [ENNReal.ofReal_div_of_pos hfifth_pos]
    exact ENNReal.div_div_cancel hmean_ne_zero ENNReal.ofReal_ne_top
  have hoverflow : mu varianceBad ≤ ENNReal.ofReal (delta / 5) := by
    calc
      mu varianceBad ≤
          sampledPredictableMixedSquaredVarianceLIntegral
              mu arms eta gamma loss horizon /
            ENNReal.ofReal varianceBudget := by
        simpa [varianceBad, varianceSum, sampledPredictableMixedSquaredVarianceSum]
          using hoverflowBase
      _ ≤ ENNReal.ofReal varianceMeanBudget /
          ENNReal.ofReal varianceBudget :=
        ENNReal.div_le_div hvarianceLIntegral le_rfl
      _ = ENNReal.ofReal (delta / 5) := hratio
  have hsplit : realizedBad ⊆ (realizedBad ∩ varianceGood) ∪ varianceBad := by
    intro sample hregret
    by_cases hvariance : varianceSum sample ≤ varianceBudget
    · exact Or.inl ⟨hregret, hvariance⟩
    · exact Or.inr (lt_of_not_ge hvariance)
  have hfifth_nonneg : 0 ≤ delta / 5 := hfifth_pos.le
  have hprob :
      (((ENNReal.ofReal (delta / 5) + ENNReal.ofReal (delta / 5)) +
          ENNReal.ofReal (delta / 5)) + ENNReal.ofReal (delta / 5)) +
          ENNReal.ofReal (delta / 5) = ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hfifth_nonneg hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg hfifth_nonneg hfifth_nonneg) hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg (add_nonneg hfifth_nonneg hfifth_nonneg)
        hfifth_nonneg) hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg
        (add_nonneg (add_nonneg hfifth_nonneg hfifth_nonneg)
          hfifth_nonneg) hfifth_nonneg) hfifth_nonneg]
    congr 1
    ring
  have htail : mu realizedBad ≤ ENNReal.ofReal delta := by
    calc
      mu realizedBad ≤ mu ((realizedBad ∩ varianceGood) ∪ varianceBad) :=
        measure_mono hsplit
      _ ≤ mu (realizedBad ∩ varianceGood) + mu varianceBad :=
        measure_union_le _ _
      _ ≤ (((ENNReal.ofReal (delta / 5) + ENNReal.ofReal (delta / 5)) +
            ENNReal.ofReal (delta / 5)) + ENNReal.ofReal (delta / 5)) +
            ENNReal.ofReal (delta / 5) := add_le_add hjoint hoverflow
      _ = ENNReal.ofReal delta := hprob
  simpa [mu, realizedBad, realizedBudget, varianceBudget, varianceMeanBudget,
    sampledPredictableVarianceSquareSmallLossRealizedMarkovHighProbabilityRegretBudget]
    using htail

end BanditRLProof.Exp3
