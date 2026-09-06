import BanditRLProof.Exp3MixedSquarePredictableVariance

/-!
# Predictable variance for realized EXP3 deviation

This module replaces the fixed interval proxy for the selected-loss deviation
by its exact finite-action centered second moment. It constructs the generated
predictable variance process and the zero-budget conditional MGF of the
variance-compensated realized deviation.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Exact centered second moment of a bounded loss under a finite action law. -/
noncomputable def selectedLossCenteredSecondMoment
    {History : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (prob loss : History → Action → Real)
    (history : History) : Real :=
  let mean := arms.sum fun action => prob history action * loss history action
  arms.sum fun selected =>
    prob history selected * (loss history selected - mean) ^ 2

theorem measurable_selectedLossCenteredSecondMoment
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : History → Action → Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon) :
    Measurable (selectedLossCenteredSecondMoment arms prob loss) := by
  let mean := fun history : History =>
    arms.sum fun action => prob history action * loss history action
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun action haction => ?_
    exact (source.measurable_prob action haction).mul
      (regularity.measurable_loss action haction)
  refine Finset.measurable_sum arms fun selected hselected => ?_
  simpa [selectedLossCenteredSecondMoment, mean] using
    (source.measurable_prob selected hselected).mul
      (((regularity.measurable_loss selected hselected).sub hmean).pow_const 2)

theorem selectedLossCenteredSecondMoment_nonneg
    {History : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (prob loss : History → Action → Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history)) :
    0 ≤ selectedLossCenteredSecondMoment arms prob loss history := by
  unfold selectedLossCenteredSecondMoment
  exact Finset.sum_nonneg fun selected hselected =>
    mul_nonneg (hdist.nonneg selected hselected) (sq_nonneg _)

/-- A probability-weighted centered second moment of `[0,1]` losses is at
most one. -/
theorem selectedLossCenteredSecondMoment_le_one
    {History : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (prob loss : History → Action → Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (hloss : ∀ action ∈ arms, loss history action ∈ Set.Icc (0 : Real) 1) :
    selectedLossCenteredSecondMoment arms prob loss history ≤ 1 := by
  let mean := arms.sum fun action => prob history action * loss history action
  have hmean_nonneg : 0 ≤ mean := by
    exact Finset.sum_nonneg fun action haction =>
      mul_nonneg (hdist.nonneg action haction) (hloss action haction).1
  have hmean_le_one : mean ≤ 1 := by
    calc
      mean ≤ arms.sum (fun action => prob history action * 1) := by
        exact Finset.sum_le_sum fun action haction =>
          mul_le_mul_of_nonneg_left (hloss action haction).2
            (hdist.nonneg action haction)
      _ = 1 := by simpa using hdist.sum_eq_one
  unfold selectedLossCenteredSecondMoment
  change
    (∑ selected ∈ arms,
      prob history selected * (loss history selected - mean) ^ 2) ≤ 1
  calc
    (∑ selected ∈ arms,
        prob history selected * (loss history selected - mean) ^ 2) ≤
        ∑ selected ∈ arms, prob history selected * 1 := by
      exact Finset.sum_le_sum fun selected hselected => by
        have hl := hloss selected hselected
        have hl_nonneg : 0 ≤ loss history selected := hl.1
        have hl_le_one : loss history selected ≤ 1 := hl.2
        have hlower : -1 ≤ loss history selected - mean := by linarith
        have hupper : loss history selected - mean ≤ 1 := by linarith
        have honeplus :
            0 ≤ 1 + (loss history selected - mean) := by
          linarith
        have hproduct :
            0 ≤ (1 - (loss history selected - mean)) *
              (1 + (loss history selected - mean)) :=
          mul_nonneg (sub_nonneg.mpr hupper) honeplus
        have hsquare : (loss history selected - mean) ^ 2 ≤ 1 := by
          nlinarith
        exact mul_le_mul_of_nonneg_left hsquare
          (hdist.nonneg selected hselected)
    _ = 1 := by simpa using hdist.sum_eq_one

/-- For `[0,1]` losses, the exact selected-loss variance is at most the
unweighted armwise loss mass. -/
theorem selectedLossCenteredSecondMoment_le_lossMass
    {History : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (prob loss : History → Action → Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (hloss : ∀ action ∈ arms, loss history action ∈ Set.Icc (0 : Real) 1) :
    selectedLossCenteredSecondMoment arms prob loss history ≤
      arms.sum fun action => loss history action := by
  let mean := arms.sum fun action => prob history action * loss history action
  have hmean_nonneg : 0 ≤ mean := by
    exact Finset.sum_nonneg fun action haction =>
      mul_nonneg (hdist.nonneg action haction) (hloss action haction).1
  have hmean_le_one : mean ≤ 1 := by
    calc
      mean ≤ arms.sum (fun action => prob history action * 1) := by
        exact Finset.sum_le_sum fun action haction =>
          mul_le_mul_of_nonneg_left (hloss action haction).2
            (hdist.nonneg action haction)
      _ = 1 := by simpa using hdist.sum_eq_one
  have hcenter :
      selectedLossCenteredSecondMoment arms prob loss history =
        arms.sum (fun action =>
          prob history action * (loss history action) ^ 2) - mean ^ 2 := by
    have hterm (action : Action) :
        prob history action * (loss history action - mean) ^ 2 =
          (prob history action * (loss history action) ^ 2 -
            2 * mean * (prob history action * loss history action)) +
            mean ^ 2 * prob history action := by
      ring
    change
      (∑ action ∈ arms,
        prob history action * (loss history action - mean) ^ 2) =
      (∑ action ∈ arms, prob history action * loss history action ^ 2) -
        mean ^ 2
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hdist.sum_eq_one]
    change
      (∑ action ∈ arms, prob history action * loss history action ^ 2) -
          2 * mean * mean + mean ^ 2 * 1 =
        (∑ action ∈ arms, prob history action * loss history action ^ 2) -
          mean ^ 2
    ring
  rw [hcenter]
  calc
    (∑ action ∈ arms, prob history action * loss history action ^ 2) -
          mean ^ 2 ≤
        ∑ action ∈ arms, prob history action * loss history action ^ 2 := by
      nlinarith [sq_nonneg mean]
    _ ≤ ∑ action ∈ arms, loss history action := by
      exact Finset.sum_le_sum fun action haction => by
        have hp_nonneg := hdist.nonneg action haction
        have hp_le_one : prob history action ≤ 1 := by
          calc
            prob history action ≤ arms.sum (prob history) :=
              Finset.single_le_sum
                (fun candidate hcandidate => hdist.nonneg candidate hcandidate)
                haction
            _ = 1 := hdist.sum_eq_one
        have hl := hloss action haction
        have hl_sq_le : (loss history action) ^ 2 ≤ loss history action := by
          nlinarith [mul_nonneg hl.1 (sub_nonneg.mpr hl.2)]
        calc
          prob history action * loss history action ^ 2 ≤
              1 * loss history action ^ 2 :=
            mul_le_mul_of_nonneg_right hp_le_one (sq_nonneg _)
          _ ≤ loss history action := by simpa using hl_sq_le

/-- Fixed-tilt MGF budget retaining the exact selected-loss variance. -/
theorem finiteActionSelectedLossDeviation_hasMGFUpperBoundAt_variance
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : History → Action → Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (tilt : Real) (htilt_nonneg : 0 ≤ tilt) (htilt_le_one : tilt ≤ 1) :
    let mean := arms.sum fun action =>
      prob history action * loss history action
    Concentration.HasMGFUpperBoundAt
      (fun selected => loss history selected - mean)
      tilt
      (tilt ^ 2 * selectedLossCenteredSecondMoment arms prob loss history)
      (finiteActionMeasure arms (prob history)) := by
  dsimp only
  let mean := arms.sum fun action =>
    prob history action * loss history action
  let X := fun selected => loss history selected - mean
  let variance := selectedLossCenteredSecondMoment arms prob loss history
  letI : IsProbabilityMeasure (finiteActionMeasure arms (prob history)) :=
    finiteActionMeasure_isProbabilityMeasure arms (prob history) hdist
  have hmean_nonneg : 0 ≤ mean := by
    exact Finset.sum_nonneg fun action haction =>
      mul_nonneg (hdist.nonneg action haction)
        (regularity.loss_mem_Icc history action haction).1
  have hmean_le_one : mean ≤ 1 := by
    calc
      mean ≤ arms.sum (fun action => prob history action * 1) := by
        exact Finset.sum_le_sum fun action haction =>
          mul_le_mul_of_nonneg_left
            (regularity.loss_mem_Icc history action haction).2
            (hdist.nonneg action haction)
      _ = 1 := by simpa using hdist.sum_eq_one
  have hX_bound (selected : Action) (hselected : selected ∈ arms) :
      |X selected| ≤ 1 := by
    rw [abs_le]
    constructor
    · have hloss_nonneg :=
        (regularity.loss_mem_Icc history selected hselected).1
      linarith
    · have hloss_le :=
        (regularity.loss_mem_Icc history selected hselected).2
      linarith
  constructor
  · intro s
    rw [finiteActionMeasure]
    refine integrable_finset_sum_measure.2 fun action haction => ?_
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · rw [ProbabilityTheory.mgf,
      integral_finiteActionMeasure_eq_sum arms (prob history) hdist]
    have hexp (selected : Action) (hselected : selected ∈ arms) :
        Real.exp (tilt * X selected) ≤
          1 + tilt * X selected + (tilt * X selected) ^ 2 := by
      apply Concentration.exp_le_one_add_self_add_sq_of_abs_le_one
      rw [abs_mul, abs_of_nonneg htilt_nonneg]
      calc
        tilt * |X selected| ≤ tilt * 1 :=
          mul_le_mul_of_nonneg_left (hX_bound selected hselected) htilt_nonneg
        _ ≤ 1 := by simpa using htilt_le_one
    calc
      arms.sum (fun selected =>
          prob history selected * Real.exp (tilt * X selected)) ≤
          arms.sum (fun selected =>
            prob history selected *
              (1 + tilt * X selected + (tilt * X selected) ^ 2)) := by
        exact Finset.sum_le_sum fun selected hselected =>
          mul_le_mul_of_nonneg_left (hexp selected hselected)
            (hdist.nonneg selected hselected)
      _ = 1 +
          tilt * arms.sum (fun selected => prob history selected * X selected) +
          tilt ^ 2 *
            arms.sum (fun selected => prob history selected * X selected ^ 2) := by
        have hterm (selected : Action) :
            prob history selected *
                (1 + tilt * X selected + (tilt * X selected) ^ 2) =
              (prob history selected +
                tilt * (prob history selected * X selected)) +
                tilt ^ 2 *
                  (prob history selected * X selected ^ 2) := by
          ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
          hdist.sum_eq_one]
      _ = 1 + tilt ^ 2 * variance := by
        have hmean_zero :
            arms.sum (fun selected => prob history selected * X selected) = 0 := by
          dsimp only [X]
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hdist.sum_eq_one]
          change mean - 1 * mean = 0
          ring
        rw [hmean_zero, mul_zero, add_zero]
        rfl
      _ ≤ Real.exp (tilt ^ 2 * variance) := by
        simpa [add_comm] using Real.add_one_le_exp (tilt ^ 2 * variance)

theorem finiteActionSelectedLossDeviation_compensated_hasMGFUpperBoundAt
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : History → Action → Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (tilt : Real) (htilt_nonneg : 0 ≤ tilt) (htilt_le_one : tilt ≤ 1) :
    let mean := arms.sum fun action =>
      prob history action * loss history action
    Concentration.HasMGFUpperBoundAt
      (fun selected =>
        tilt * (loss history selected - mean) -
          tilt ^ 2 * selectedLossCenteredSecondMoment arms prob loss history)
      1 0 (finiteActionMeasure arms (prob history)) := by
  dsimp only
  simpa using
    (finiteActionSelectedLossDeviation_hasMGFUpperBoundAt_variance
      arms prob loss history hdist epsilon regularity tilt htilt_nonneg
        htilt_le_one).compensated

/-- Exact selected-loss predictable variance at an actual generated time. -/
noncomputable def sampledTrajectoryPredictableRealizedVarianceAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Env × ((k : Nat) → Action × Real) → Real :=
  selectedLossCenteredSecondMoment arms
    (sampledTrajectoryProbabilityAt arms eta gamma t)
    (predictableLossAt loss t)

theorem measurable_sampledTrajectoryPredictableRealizedVarianceAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Measurable (sampledTrajectoryPredictableRealizedVarianceAt
      arms eta gamma loss t) := by
  exact measurable_selectedLossCenteredSecondMoment arms
    (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
    (predictableLossAt loss t)
    (sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_pos.le hgamma_le_one t)
    (gamma / (arms.card : Real))
    (sampledPredictableTrajectoryLossRegularityAt arms harms eta gamma
      hgamma_pos hgamma_le_one loss t)

theorem sampledTrajectoryPredictableRealizedVarianceAt_nonneg
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    0 ≤ sampledTrajectoryPredictableRealizedVarianceAt
      arms eta gamma loss t sample := by
  exact selectedLossCenteredSecondMoment_nonneg arms
    (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
    (predictableLossAt loss t) sample
    ((sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_nonneg hgamma_le_one t).distribution sample)

theorem sampledTrajectoryPredictableRealizedVarianceAt_le_lossMassAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    sampledTrajectoryPredictableRealizedVarianceAt
        arms eta gamma loss t sample ≤
      arms.sum fun action => predictableLossAt loss t sample action := by
  exact selectedLossCenteredSecondMoment_le_lossMass arms
    (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
    (predictableLossAt loss t) sample
    ((sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_nonneg hgamma_le_one t).distribution sample)
    (fun action _haction => by
      cases t with
      | zero =>
          simpa [predictableLossAt] using
            loss.initial_mem_unitInterval sample.1 action
      | succ n =>
          simpa [predictableLossAt] using
            loss.successor_mem_unitInterval n sample.1
              (Preorder.frestrictLe n sample.2) action)

/-- Every generated selected-loss predictable variance is at most one. -/
theorem sampledTrajectoryPredictableRealizedVarianceAt_le_one
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    sampledTrajectoryPredictableRealizedVarianceAt
        arms eta gamma loss t sample ≤ 1 := by
  exact selectedLossCenteredSecondMoment_le_one arms
    (sampledTrajectoryProbabilityAt (Env := Env) arms eta gamma t)
    (predictableLossAt loss t) sample
    ((sampledTrajectoryProbabilitySourceAt (Env := Env) arms harms eta gamma
      hgamma_nonneg hgamma_le_one t).distribution sample)
    (fun action _haction => by
      cases t with
      | zero =>
          simpa [predictableLossAt] using
            loss.initial_mem_unitInterval sample.1 action
      | succ n =>
          simpa [predictableLossAt] using
            loss.successor_mem_unitInterval n sample.1
              (Preorder.frestrictLe n sample.2) action)

/-- An identified finite conditional action law supplies a zero-budget MGF
for the exact selected-loss variance-compensated increment. -/
theorem selectedLossDeviation_compensated_hasCondMGFUpperBoundAt_of_condDistrib
    {Omega : Type u} {History : Type v} {Action : Type*}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [mHistory : MeasurableSpace History] [StandardBorelSpace History]
    [mAction : MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega → History) (hhistory : Measurable history)
    (action : Omega → Action) (haction : Measurable action)
    (arms : Finset Action) (prob loss : History → Action → Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (hloss : Measurable (fun input : History × Action =>
      loss input.1 input.2))
    (hloss_mem : ∀ history action,
      loss history action ∈ Set.Icc (0 : Real) 1)
    (tilt : Real) (htilt_nonneg : 0 ≤ tilt) (htilt_le_one : tilt ≤ 1)
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source) :
    let mean := fun h =>
      arms.sum fun candidate => prob h candidate * loss h candidate
    Concentration.HasCondMGFUpperBoundAt
      (mHistory.comap history) hhistory.comap_le
      (fun omega =>
        tilt * (loss (history omega) (action omega) - mean (history omega)) -
          tilt ^ 2 *
            selectedLossCenteredSecondMoment arms prob loss (history omega))
      1 0 mu := by
  dsimp only
  let mcond := mHistory.comap history
  let mean := fun h : History =>
    arms.sum fun candidate => prob h candidate * loss h candidate
  let X := fun omega => loss (history omega) (action omega) - mean (history omega)
  let variance := selectedLossCenteredSecondMoment arms prob loss
  let Z := fun omega => tilt * X omega - tilt ^ 2 * variance (history omega)
  have hmcond : mcond ≤ mOmega := hhistory.comap_le
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun candidate hcandidate => ?_
    exact (source.measurable_prob candidate hcandidate).mul
      (regularity.measurable_loss candidate hcandidate)
  have hX : @Measurable Omega Real mOmega inferInstance X :=
    (hloss.comp (hhistory.prodMk haction)).sub
      (hmean.comp hhistory)
  have hvariance : Measurable variance :=
    measurable_selectedLossCenteredSecondMoment
      arms prob loss source epsilon regularity
  have hZ : @Measurable Omega Real mOmega inferInstance Z :=
    (measurable_const.mul hX).sub
      (measurable_const.mul (hvariance.comp hhistory))
  have haction_map :=
    condExpKernel_map_eq_finiteActionMeasure_of_condDistrib_ae_eq
      (mOmega := mOmega) (mCondition := mHistory) (mAction := mAction)
      mu action history haction hhistory arms prob source hcond
  have hhistory_mcond :
      @Measurable Omega History mcond mHistory history :=
    Measurable.of_comap_le le_rfl
  have hhistory_map :=
    ConditionalExpectationReward.condExpKernel_map_eq_dirac_of_measurable
      (mOmega := mOmega) (mTarget := mHistory)
      mu mcond hmcond history hhistory_mcond
  have hhistory_ae :
      Filter.Eventually
        (fun omega => Filter.EventuallyEq
          (ae (@condExpKernel Omega mOmega _ mu _ mcond omega))
          history (fun _ => history omega))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hhistory_map] with omega hmap
    exact ConditionalExpectationReward.eventuallyEq_const_of_map_eq_dirac
      (mOmega := mOmega) (mTarget := mHistory)
      (@condExpKernel Omega mOmega _ mu _ mcond omega)
      history (history omega) hhistory hmap
  have hkernel_X_eq :
      Filter.Eventually
        (fun omega => Filter.EventuallyEq
          (ae (@condExpKernel Omega mOmega _ mu _ mcond omega))
          X (fun y => loss (history omega) (action y) - mean (history omega)))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hhistory_ae] with omega hfreeze
    filter_upwards [hfreeze] with y hy
    simp only [X]
    rw [hy]
  have hkernel_Z_eq :
      Filter.Eventually
        (fun omega => Filter.EventuallyEq
          (ae (@condExpKernel Omega mOmega _ mu _ mcond omega))
          Z (fun y => tilt * X y - tilt ^ 2 * variance (history omega)))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hhistory_ae] with omega hfreeze
    filter_upwards [hfreeze] with y hy
    simp only [Z]
    rw [hy]
  have hkernel_X_map :
      Filter.Eventually
        (fun omega =>
          @Measure.map Omega Real mOmega inferInstance X
              (@condExpKernel Omega mOmega _ mu _ mcond omega) =
            Measure.map
              (fun selected => loss (history omega) selected - mean (history omega))
              (finiteActionMeasure arms (prob (history omega))))
        (ae (mu.trim hmcond)) := by
    filter_upwards [haction_map, hkernel_X_eq] with omega haction_eq hXeq
    let score : Action → Real :=
      fun selected => loss (history omega) selected - mean (history omega)
    have hscore : Measurable score :=
      (hloss.comp
        (measurable_const.prodMk measurable_id)).sub measurable_const
    calc
      @Measure.map Omega Real mOmega inferInstance X
          (@condExpKernel Omega mOmega _ mu _ mcond omega) =
        @Measure.map Omega Real mOmega inferInstance
          (fun y => score (action y))
          (@condExpKernel Omega mOmega _ mu _ mcond omega) :=
        Measure.map_congr hXeq
      _ = Measure.map score
          (@Measure.map Omega Action mOmega mAction action
            (@condExpKernel Omega mOmega _ mu _ mcond omega)) := by
        rw [Measure.map_map hscore haction]
        congr 1
      _ = _ := by rw [haction_eq]
  have hkernel_Z_map :
      Filter.Eventually
        (fun omega =>
          @Measure.map Omega Real mOmega inferInstance Z
              (@condExpKernel Omega mOmega _ mu _ mcond omega) =
            Measure.map
              (fun selected =>
                tilt * (loss (history omega) selected - mean (history omega)) -
                  tilt ^ 2 * variance (history omega))
              (finiteActionMeasure arms (prob (history omega))))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hkernel_X_map, hkernel_Z_eq] with omega hXmap hZeq
    let affine : Real → Real := fun z =>
      tilt * z - tilt ^ 2 * variance (history omega)
    have haffine : Measurable affine := by fun_prop
    let score : Action → Real :=
      fun selected => loss (history omega) selected - mean (history omega)
    have hscore : Measurable score :=
      (hloss.comp
        (measurable_const.prodMk measurable_id)).sub measurable_const
    calc
      @Measure.map Omega Real mOmega inferInstance Z
          (@condExpKernel Omega mOmega _ mu _ mcond omega) =
        @Measure.map Omega Real mOmega inferInstance
          (fun y => affine (X y))
          (@condExpKernel Omega mOmega _ mu _ mcond omega) :=
        Measure.map_congr hZeq
      _ = Measure.map affine
          (@Measure.map Omega Real mOmega inferInstance X
            (@condExpKernel Omega mOmega _ mu _ mcond omega)) := by
        rw [Measure.map_map haffine hX]
        congr 1
      _ = Measure.map affine
          (@Measure.map Action Real mAction inferInstance score
            (finiteActionMeasure arms (prob (history omega)))) := by
        rw [hXmap]
      _ = Measure.map (fun selected => affine (score selected))
          (finiteActionMeasure arms (prob (history omega))) := by
        rw [Measure.map_map haffine hscore]
        congr 1
      _ = _ := rfl
  let target : Omega → Measure Real := fun omega =>
    Measure.map
      (fun selected => loss (history omega) selected - mean (history omega))
      (finiteActionMeasure arms (prob (history omega)))
  have htarget :
      ∀ᵐ omega ∂mu.trim hmcond,
        HasSubgaussianMGF id
          (Concentration.intervalVarianceProxy 0 1) (target omega) := by
    filter_upwards [] with omega
    let actionMu := finiteActionMeasure arms (prob (history omega))
    let raw := loss (history omega)
    let score := fun selected => raw selected - mean (history omega)
    letI : IsProbabilityMeasure actionMu :=
      finiteActionMeasure_isProbabilityMeasure arms (prob (history omega))
        (source.distribution (history omega))
    have hraw : Measurable raw :=
      hloss.comp (measurable_const.prodMk measurable_id)
    have hbound : ∀ᵐ selected ∂actionMu,
        raw selected ∈ Set.Icc (0 : Real) 1 :=
      Filter.Eventually.of_forall fun selected =>
        hloss_mem (history omega) selected
    have hmean_integral : integral actionMu raw = mean (history omega) := by
      simpa [actionMu, raw, mean] using
        (integral_finiteActionMeasure_eq_sum arms (prob (history omega))
          (source.distribution (history omega)) raw)
    have hscoreSubG : HasSubgaussianMGF score
        (Concentration.intervalVarianceProxy 0 1) actionMu := by
      simpa [score, raw] using
        (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
          actionMu hraw.aemeasurable hbound hmean_integral)
    have hscore : Measurable score := hraw.sub measurable_const
    exact (HasSubgaussianMGF.id_map_iff hscore.aemeasurable).2
      (by simpa [target, actionMu, score, raw] using hscoreSubG)
  have hsub0 :=
    @ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
      Omega mOmega inferInstance mu inferInstance mcond hmcond X
        (Concentration.intervalVarianceProxy 0 1) hX target
          (by simpa [target] using hkernel_X_map) htarget
  have hsub : ProbabilityTheory.HasCondSubgaussianMGF
      (mHistory.comap history) hhistory.comap_le X
        (Concentration.intervalVarianceProxy 0 1) mu := by
    simpa [mcond] using hsub0
  change Concentration.Kernel.HasMGFUpperBoundAt Z 1 0
    (@condExpKernel Omega mOmega _ mu _ mcond) (mu.trim hmcond)
  refine ⟨?_, ?_⟩
  · intro s
    rw [@ProbabilityTheory.condExpKernel_comp_trim
      Omega mcond mOmega _ mu _ hmcond]
    have hXint := hsub.integrable_exp_mul (s * tilt)
    let ceiling : Real := arms.card
    let factor := fun omega =>
      Real.exp (-s * tilt ^ 2 * variance (history omega))
    have hfactor_meas : AEStronglyMeasurable[mOmega] factor mu := by
      have hfactor : @Measurable Omega Real mOmega inferInstance factor := by
        dsimp only [factor]
        fun_prop
      exact hfactor.aestronglyMeasurable
    have hfactor_bound :
        ∀ᵐ omega ∂mu, ‖factor omega‖ ≤
          Real.exp (|s| * tilt ^ 2 * ceiling) := by
      filter_upwards [] with omega
      have hnonneg := selectedLossCenteredSecondMoment_nonneg
        arms prob loss (history omega) (source.distribution (history omega))
      have hlossMass :=
        selectedLossCenteredSecondMoment_le_lossMass
          arms prob loss (history omega) (source.distribution (history omega))
          (regularity.loss_mem_Icc (history omega))
      have hlossMass_le :
          (∑ action ∈ arms, loss (history omega) action) ≤ ceiling := by
        calc
          (∑ action ∈ arms, loss (history omega) action) ≤
              ∑ _action ∈ arms, (1 : Real) :=
            Finset.sum_le_sum fun action haction =>
              (regularity.loss_mem_Icc (history omega) action haction).2
          _ = ceiling := by simp [ceiling]
      have hle := hlossMass.trans hlossMass_le
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        -s * tilt ^ 2 * variance (history omega) ≤
            |s| * tilt ^ 2 * variance (history omega) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (neg_le_abs s) (sq_nonneg tilt))
            hnonneg
        _ ≤ |s| * tilt ^ 2 * ceiling :=
          mul_le_mul_of_nonneg_left hle
            (mul_nonneg (abs_nonneg s) (sq_nonneg tilt))
    have hint := hXint.bdd_mul hfactor_meas hfactor_bound
    have heq : (fun omega => Real.exp (s * Z omega)) =
        (fun omega => factor omega * Real.exp ((s * tilt) * X omega)) := by
      funext omega
      simp only [Z, factor]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hint
  · apply Filter.Eventually.mono hkernel_Z_map
    intro omega hmap
    let actionMu := finiteActionMeasure arms (prob (history omega))
    let score : Action → Real := fun selected =>
      tilt * (loss (history omega) selected - mean (history omega)) -
        tilt ^ 2 * variance (history omega)
    have hscore : Measurable score := by
      dsimp only [score]
      exact
        (measurable_const.mul
          ((hloss.comp
            (measurable_const.prodMk measurable_id)).sub measurable_const)).sub
          measurable_const
    have hfinite : Concentration.HasMGFUpperBoundAt score 1 0 actionMu := by
      simpa [score, actionMu, mean, variance] using
        finiteActionSelectedLossDeviation_compensated_hasMGFUpperBoundAt
          arms prob loss (history omega) (source.distribution (history omega))
            epsilon regularity tilt htilt_nonneg htilt_le_one
    have htarget : Concentration.HasMGFUpperBoundAt id 1 0
        (Measure.map score actionMu) :=
      (Concentration.HasMGFUpperBoundAt.id_map_iff hscore.aemeasurable).2
        hfinite
    rw [← hmap] at htarget
    exact ((Concentration.HasMGFUpperBoundAt.id_map_iff hZ.aemeasurable).1
      htarget).mgf_le

/-- Initial generated selected-loss increment with its exact predictable
variance compensation. -/
theorem sampledPredictableSelectedLossCompensated_zero_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (tilt : Real) (htilt_nonneg : 0 ≤ tilt) (htilt_le_one : tilt ≤ 1) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Concentration.HasCondMGFUpperBoundAt
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) → Action × Real) => sample.1))
      measurable_fst.comap_le
      (fun sample =>
        tilt * sampledTrajectorySelectedDeviationAt
            arms eta gamma loss 0 sample -
          tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss 0 sample)
      1 0 mu := by
  dsimp only
  let algorithm := sampledImportanceWeightedHistoryAlgorithm arms harms
    eta gamma hgamma_pos.le hgamma_le_one
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) → Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) → Action × Real) =>
    (sample.2 0).1
  let prob := fun _env : Env => initialExploredDistribution arms eta gamma
  let source := sampledInitialEnvironmentDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one
  let regularity := sampledPredictableInitialLossRegularity
    arms harms eta gamma hgamma_pos hgamma_le_one loss
  have hkernel : Kernel.const Env algorithm.initialAction =
      finiteActionKernel arms prob source := by
    ext env event hevent
    rw [Kernel.const_apply, finiteActionKernel_apply]
    rfl
  have hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source := by
    have hbase :=
      canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
        prior algorithm loss.environment
    rw [hkernel] at hbase
    simpa [mu, algorithm, history, action,
      sampledImportanceWeightedTrajectoryKernel] using hbase
  have hmgf :=
    selectedLossDeviation_compensated_hasCondMGFUpperBoundAt_of_condDistrib
      mu history measurable_fst action (by fun_prop) arms prob loss.initial
        source (gamma / (arms.card : Real)) regularity
        loss.measurable_initial loss.initial_mem_unitInterval
        tilt htilt_nonneg htilt_le_one hcond
  simpa [mu, history, action, prob,
    sampledTrajectorySelectedDeviationAt,
    sampledTrajectoryPredictableRealizedVarianceAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

/-- Successor generated selected-loss increment with its exact predictable
variance compensation. -/
theorem sampledPredictableSelectedLossCompensated_succ_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (n : Nat)
    (tilt : Real) (htilt_nonneg : 0 ≤ tilt) (htilt_le_one : tilt ≤ 1) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) → Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    Concentration.HasCondMGFUpperBoundAt
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (fun sample =>
        tilt * sampledTrajectorySelectedDeviationAt
            arms eta gamma loss (n + 1) sample -
          tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss (n + 1) sample)
      1 0 mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) → Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  let action := fun sample : Env × ((k : Nat) → Action × Real) =>
    (sample.2 (n + 1)).1
  let prob := fun input : Env × History.FinitePairHistory Action Real n =>
    sampledHistoryDistribution arms eta gamma n input.2
  let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
    loss.successor n input.1 input.2
  let source := sampledEnvironmentHistoryDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one n
  let regularity := sampledPredictableSuccessorLossRegularity
    arms harms eta gamma hgamma_pos hgamma_le_one loss n
  have hhistory : Measurable history := measurable_fst.prodMk
    ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable action := by fun_prop
  have hloss : Measurable
      (fun input : (Env × History.FinitePairHistory Action Real n) × Action =>
        roundLoss input.1 input.2) := by
    exact (loss.measurable_successor n).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source := by
    simpa [mu, history, action, prob, source] using
      (sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss n)
  have hmgf :=
    selectedLossDeviation_compensated_hasCondMGFUpperBoundAt_of_condDistrib
      mu history hhistory action haction arms prob roundLoss source
        (gamma / (arms.card : Real)) regularity hloss
        (fun input selected =>
          loss.successor_mem_unitInterval n input.1 input.2 selected)
        tilt htilt_nonneg htilt_le_one hcond
  simpa [mu, history, action, prob, roundLoss,
    sampledTrajectorySelectedDeviationAt,
    sampledTrajectoryPredictableRealizedVarianceAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

/-- The deterministic-feedback realization transports the initial selected
loss compensation to the observed realized-loss increment. -/
theorem sampledPredictableRealizedCompensated_zero_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (tilt : Real) (htilt_nonneg : 0 ≤ tilt) (htilt_le_one : tilt ≤ 1) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Concentration.HasCondMGFUpperBoundAt
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) → Action × Real) => sample.1))
      measurable_fst.comap_le
      (fun sample =>
        tilt * sampledTrajectoryRealizedDeviationAt
            arms eta gamma loss 0 sample -
          tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss 0 sample)
      1 0 mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) → Action × Real) => sample.1
  have hhistory : Measurable history := measurable_fst
  let mcond := (inferInstance : MeasurableSpace Env).comap history
  letI : MeasurableSpace (Env × ((k : Nat) → Action × Real)) :=
    Prod.instMeasurableSpace
  have hmcond : mcond ≤ Prod.instMeasurableSpace := hhistory.comap_le
  have hselected :=
    sampledPredictableSelectedLossCompensated_zero_hasCondMGFUpperBoundAt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss
        tilt htilt_nonneg htilt_le_one
  dsimp only at hselected
  have hreward :=
    sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
      prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss 0
  dsimp only at hreward
  have hcompensated :
      (fun sample =>
        tilt * sampledTrajectorySelectedDeviationAt
            arms eta gamma loss 0 sample -
          tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss 0 sample) =ᵐ[mu]
      (fun sample =>
        tilt * sampledTrajectoryRealizedDeviationAt
            arms eta gamma loss 0 sample -
          tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss 0 sample) := by
    filter_upwards [hreward] with sample hs
    simp only [sampledTrajectorySelectedDeviationAt,
      sampledTrajectoryRealizedDeviationAt]
    rw [hs]
  change Concentration.Kernel.HasMGFUpperBoundAt
    (fun sample =>
      tilt * sampledTrajectorySelectedDeviationAt
          arms eta gamma loss 0 sample -
        tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss 0 sample)
    1 0
    (@condExpKernel (Env × ((k : Nat) → Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hselected
  change Concentration.Kernel.HasMGFUpperBoundAt
    (fun sample =>
      tilt * sampledTrajectoryRealizedDeviationAt
          arms eta gamma loss 0 sample -
        tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss 0 sample)
    1 0
    (@condExpKernel (Env × ((k : Nat) → Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply hselected.congr
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) → Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hcompensated

/-- The deterministic-feedback realization transports each successor selected
loss compensation to the observed realized-loss increment. -/
theorem sampledPredictableRealizedCompensated_succ_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (n : Nat)
    (tilt : Real) (htilt_nonneg : 0 ≤ tilt) (htilt_le_one : tilt ≤ 1) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) → Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    Concentration.HasCondMGFUpperBoundAt
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (fun sample =>
        tilt * sampledTrajectoryRealizedDeviationAt
            arms eta gamma loss (n + 1) sample -
          tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss (n + 1) sample)
      1 0 mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) → Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  have hhistory : Measurable history := measurable_fst.prodMk
    ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  let mcond := (inferInstance : MeasurableSpace
    (Env × History.FinitePairHistory Action Real n)).comap history
  letI : MeasurableSpace (Env × ((k : Nat) → Action × Real)) :=
    Prod.instMeasurableSpace
  have hmcond : mcond ≤ Prod.instMeasurableSpace := hhistory.comap_le
  have hselected :=
    sampledPredictableSelectedLossCompensated_succ_hasCondMGFUpperBoundAt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
        tilt htilt_nonneg htilt_le_one
  dsimp only at hselected
  have hreward :=
    sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
      prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss (n + 1)
  dsimp only at hreward
  have hcompensated :
      (fun sample =>
        tilt * sampledTrajectorySelectedDeviationAt
            arms eta gamma loss (n + 1) sample -
          tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss (n + 1) sample) =ᵐ[mu]
      (fun sample =>
        tilt * sampledTrajectoryRealizedDeviationAt
            arms eta gamma loss (n + 1) sample -
          tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss (n + 1) sample) := by
    filter_upwards [hreward] with sample hs
    simp only [sampledTrajectorySelectedDeviationAt,
      sampledTrajectoryRealizedDeviationAt]
    rw [hs]
  change Concentration.Kernel.HasMGFUpperBoundAt
    (fun sample =>
      tilt * sampledTrajectorySelectedDeviationAt
          arms eta gamma loss (n + 1) sample -
        tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss (n + 1) sample)
    1 0
    (@condExpKernel (Env × ((k : Nat) → Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hselected
  change Concentration.Kernel.HasMGFUpperBoundAt
    (fun sample =>
      tilt * sampledTrajectoryRealizedDeviationAt
          arms eta gamma loss (n + 1) sample -
        tilt ^ 2 * sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss (n + 1) sample)
    1 0
    (@condExpKernel (Env × ((k : Nat) → Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply hselected.congr
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) → Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hcompensated

/-- Shift actual-time selected-loss variances by one so that the process is
predictable for the generated deviation filtration. -/
noncomputable def sampledPredictableRealizedVarianceProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) :
    Nat → Env × ((k : Nat) → Action × Real) → Real
  | 0, _sample => 0
  | i + 1, sample =>
      sampledTrajectoryPredictableRealizedVarianceAt
        arms eta gamma loss i sample

theorem measurable_sampledTrajectoryPredictableRealizedVarianceAt_filtration
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Measurable[sampledPredictableDeviationFiltration Env Action t]
      (sampledTrajectoryPredictableRealizedVarianceAt
        arms eta gamma loss t) := by
  cases t with
  | zero =>
      let prob := fun _env : Env => initialExploredDistribution arms eta gamma
      let roundLoss := loss.initial
      let variance := selectedLossCenteredSecondMoment arms prob roundLoss
      let source := sampledInitialEnvironmentDistributionSource
        (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one
      let regularity := sampledPredictableInitialLossRegularity
        arms harms eta gamma hgamma_pos hgamma_le_one loss
      have hvariance : Measurable variance :=
        measurable_selectedLossCenteredSecondMoment arms prob roundLoss source
          (gamma / (arms.card : Real)) regularity
      have hfst : @Measurable
          (Env × ((k : Nat) → Action × Real)) Env
          (sampledPredictableDeviationFiltration Env Action 0)
          inferInstance Prod.fst := by
        rw [sampledPredictableDeviationFiltration_zero]
        exact Measurable.of_comap_le le_rfl
      simpa [sampledTrajectoryPredictableRealizedVarianceAt,
        selectedLossCenteredSecondMoment, sampledTrajectoryProbabilityAt,
        predictableLossAt, variance, prob, roundLoss] using
        hvariance.comp hfst
  | succ n =>
      let history := fun sample : Env × ((k : Nat) → Action × Real) =>
        (sample.1, Preorder.frestrictLe n sample.2)
      let prob := fun input : Env × History.FinitePairHistory Action Real n =>
        sampledHistoryDistribution arms eta gamma n input.2
      let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
        loss.successor n input.1 input.2
      let variance := selectedLossCenteredSecondMoment arms prob roundLoss
      let source := sampledEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one n
      let regularity := sampledPredictableSuccessorLossRegularity
        arms harms eta gamma hgamma_pos hgamma_le_one loss n
      have hvariance : Measurable variance :=
        measurable_selectedLossCenteredSecondMoment arms prob roundLoss source
          (gamma / (arms.card : Real)) regularity
      have hhistory : @Measurable
          (Env × ((k : Nat) → Action × Real))
          (Env × History.FinitePairHistory Action Real n)
          (sampledPredictableDeviationFiltration Env Action (n + 1))
          inferInstance history := by
        rw [sampledPredictableDeviationFiltration_succ]
        exact Measurable.of_comap_le le_rfl
      simpa [sampledTrajectoryPredictableRealizedVarianceAt,
        selectedLossCenteredSecondMoment, sampledTrajectoryProbabilityAt,
        predictableLossAt, variance, prob, roundLoss, history] using
        hvariance.comp hhistory

theorem sampledPredictableRealizedVarianceProcess_isPredictable
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) :
    IsPredictable (sampledPredictableDeviationFiltration Env Action)
      (sampledPredictableRealizedVarianceProcess arms eta gamma loss) := by
  apply isPredictable_of_measurable_add_one
  · change Measurable[sampledPredictableDeviationFiltration Env Action 0]
      (fun _ : Env × ((k : Nat) → Action × Real) => (0 : Real))
    exact measurable_const
  · intro n
    simpa [sampledPredictableRealizedVarianceProcess] using
      measurable_sampledTrajectoryPredictableRealizedVarianceAt_filtration
        arms harms eta gamma hgamma_pos hgamma_le_one loss n

theorem sampledPredictableRealizedVarianceProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) → Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledPredictableRealizedVarianceProcess
          arms eta gamma loss i sample) =
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss i sample) := by
  induction horizon with
  | zero => simp [sampledPredictableRealizedVarianceProcess]
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by rfl,
        Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      rfl

theorem sampledPredictableRealizedVariance_sum_le_lossMass
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) → Action × Real)) :
    (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss i sample) ≤
      (Finset.range horizon).sum (fun i =>
        arms.sum fun action => predictableLossAt loss i sample action) := by
  exact Finset.sum_le_sum fun i _hi =>
    sampledTrajectoryPredictableRealizedVarianceAt_le_lossMassAt
      arms harms eta gamma hgamma_nonneg hgamma_le_one loss i sample

/-- The first `horizon` generated selected-loss predictable variances have
deterministic total budget `horizon`. -/
theorem sampledPredictableRealizedVariance_sum_le_horizon
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) → Action × Real)) :
    (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss i sample) ≤ (horizon : Real) := by
  calc
    (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss i sample) ≤
        (Finset.range horizon).sum (fun _ => (1 : Real)) := by
      exact Finset.sum_le_sum fun i _hi =>
        sampledTrajectoryPredictableRealizedVarianceAt_le_one
          arms harms eta gamma hgamma_nonneg hgamma_le_one loss i sample
    _ = (horizon : Real) := by simp

end BanditRLProof.Exp3
