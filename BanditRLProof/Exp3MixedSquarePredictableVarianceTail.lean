import BanditRLProof.Exp3MixedSquarePredictableVariance

/-!
# Predictable-variance tail for the mixed-square EXP3 process

This module keeps the exact conditional second moment random. It first
compensates each centered mixed-square increment by its finite-law variance,
then iterates the resulting zero-budget conditional MGF. The main endpoint is
a fixed-tilt tail on the event that the cumulative predictable variance is at
most a caller-supplied budget.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory Real

universe u v

/-- A centered mixed-square score is bounded by the reciprocal probability
floor on the support of the finite sampling distribution. -/
theorem abs_mixedSquaredEstimatorDeviation_le_inv_floor
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (chosen : Action) (hchosen : chosen ∈ arms) :
    |mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
        chosen - arms.sum (fun action => (loss history action) ^ 2)| <=
      1 / epsilon := by
  let raw := fun selected =>
    mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
      selected
  let mean := arms.sum (fun action => (loss history action) ^ 2)
  have hprob_pos (action : Action) (haction : action ∈ arms) :
      0 < prob history action :=
    regularity.epsilon_pos.trans_le (regularity.prob_floor history action haction)
  have hmean_nonneg : 0 <= mean :=
    Finset.sum_nonneg fun action _haction => sq_nonneg (loss history action)
  have hmean_le_card : mean <= (arms.card : Real) := by
    dsimp only [mean]
    calc
      arms.sum (fun action => (loss history action) ^ 2) <=
          arms.sum (fun _action => (1 : Real)) := by
            apply Finset.sum_le_sum
            intro action haction
            simpa using
              (sq_le_sq₀ (regularity.loss_mem_Icc history action haction).1
                zero_le_one).2
                (regularity.loss_mem_Icc history action haction).2
      _ = (arms.card : Real) := by simp
  have hcard_le_inv : (arms.card : Real) <= 1 / epsilon := by
    rw [le_div_iff₀ regularity.epsilon_pos]
    have hsum : arms.sum (fun _action => epsilon) <=
        arms.sum (prob history) :=
      Finset.sum_le_sum fun action haction =>
        regularity.prob_floor history action haction
    simpa [hdist.sum_eq_one, mul_comm] using hsum
  have hraw_nonneg : 0 <= raw chosen := by
    unfold raw mixedSquaredImportanceWeightedLoss
    exact Finset.sum_nonneg fun action haction =>
      mul_nonneg (hdist.nonneg action haction) (sq_nonneg _)
  have hraw_le : raw chosen <= 1 / epsilon := by
    dsimp only [raw]
    rw [mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div
      arms (prob history) (loss history) chosen hchosen
        (hprob_pos chosen hchosen).ne']
    have hsq : (loss history chosen) ^ 2 <= 1 := by
      simpa using
        (sq_le_sq₀ (regularity.loss_mem_Icc history chosen hchosen).1
          zero_le_one).2
          (regularity.loss_mem_Icc history chosen hchosen).2
    calc
      (loss history chosen) ^ 2 / prob history chosen <=
          1 / prob history chosen :=
        div_le_div_of_nonneg_right hsq (hprob_pos chosen hchosen).le
      _ <= 1 / epsilon := one_div_le_one_div_of_le regularity.epsilon_pos
        (regularity.prob_floor history chosen hchosen)
  change |raw chosen - mean| <= 1 / epsilon
  rw [abs_le]
  constructor <;> nlinarith

/-- Exact finite-law fixed-tilt MGF bound. Unlike the deterministic Bernstein
wrapper, its exponent retains the actual centered second moment. -/
theorem finiteActionMixedSquaredEstimator_hasMGFUpperBoundAt_variance
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (tilt : Real) (htilt_nonneg : 0 <= tilt) (htilt_le : tilt <= epsilon) :
    Concentration.HasMGFUpperBoundAt
      (fun chosen =>
        mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
            chosen -
          arms.sum (fun action => (loss history action) ^ 2))
      tilt
      (tilt ^ 2 *
        mixedSquaredEstimatorCenteredSecondMoment arms prob loss history)
      (finiteActionMeasure arms (prob history)) := by
  let raw := fun chosen =>
    mixedSquaredImportanceWeightedLoss arms (prob history) (loss history) chosen
  let mean := arms.sum (fun action => (loss history action) ^ 2)
  let X := fun chosen => raw chosen - mean
  let variance := mixedSquaredEstimatorCenteredSecondMoment arms prob loss history
  letI : IsProbabilityMeasure (finiteActionMeasure arms (prob history)) :=
    finiteActionMeasure_isProbabilityMeasure arms (prob history) hdist
  have hprob_pos (action : Action) (haction : action ∈ arms) :
      0 < prob history action :=
    regularity.epsilon_pos.trans_le (regularity.prob_floor history action haction)
  have hinv_nonneg : 0 <= 1 / epsilon :=
    (one_div_pos.mpr regularity.epsilon_pos).le
  have hX_bound (chosen : Action) (hchosen : chosen ∈ arms) :
      |X chosen| <= 1 / epsilon := by
    simpa [X, raw, mean] using
      abs_mixedSquaredEstimatorDeviation_le_inv_floor
        arms prob loss history hdist epsilon regularity chosen hchosen
  constructor
  · intro s
    rw [finiteActionMeasure]
    refine integrable_finset_sum_measure.2 fun action haction => ?_
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · rw [ProbabilityTheory.mgf,
      integral_finiteActionMeasure_eq_sum arms (prob history) hdist]
    have hexp (chosen : Action) (hchosen : chosen ∈ arms) :
        Real.exp (tilt * X chosen) <=
          1 + tilt * X chosen + (tilt * X chosen) ^ 2 := by
      apply Concentration.exp_le_one_add_self_add_sq_of_abs_le_one
      rw [abs_mul, abs_of_nonneg htilt_nonneg]
      calc
        tilt * |X chosen| <= tilt * (1 / epsilon) :=
          mul_le_mul_of_nonneg_left (hX_bound chosen hchosen) htilt_nonneg
        _ <= epsilon * (1 / epsilon) :=
          mul_le_mul_of_nonneg_right htilt_le hinv_nonneg
        _ = 1 := by field_simp [ne_of_gt regularity.epsilon_pos]
    calc
      arms.sum (fun chosen =>
          prob history chosen * Real.exp (tilt * X chosen)) <=
          arms.sum (fun chosen => prob history chosen *
            (1 + tilt * X chosen + (tilt * X chosen) ^ 2)) := by
        apply Finset.sum_le_sum
        intro chosen hchosen
        exact mul_le_mul_of_nonneg_left (hexp chosen hchosen)
          (hdist.nonneg chosen hchosen)
      _ = 1 + tilt * arms.sum (fun chosen => prob history chosen * X chosen) +
          tilt ^ 2 * arms.sum (fun chosen =>
            prob history chosen * (X chosen) ^ 2) := by
        have hterm (chosen : Action) :
            prob history chosen *
                (1 + tilt * X chosen + (tilt * X chosen) ^ 2) =
              (prob history chosen +
                tilt * (prob history chosen * X chosen)) +
                tilt ^ 2 * (prob history chosen * (X chosen) ^ 2) := by ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
          hdist.sum_eq_one]
      _ = 1 + tilt ^ 2 * variance := by
        have hmean : arms.sum (fun chosen => prob history chosen * X chosen) = 0 := by
          dsimp only [X]
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib,
            sum_prob_mul_mixedSquaredImportanceWeightedLoss_eq_sum_loss_sq
              arms (prob history) (loss history)
                (fun action haction => (hprob_pos action haction).ne'),
            ← Finset.sum_mul, hdist.sum_eq_one]
          simp [mean]
        rw [hmean, mul_zero, add_zero]
        rfl
      _ <= Real.exp (tilt ^ 2 * variance) := by
        simpa [add_comm] using Real.add_one_le_exp (tilt ^ 2 * variance)

/-- Finite-law exponential-supermartingale increment obtained by subtracting
the exact variance budget from the centered mixed-square score. -/
theorem finiteActionMixedSquaredEstimator_compensated_hasMGFUpperBoundAt
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (history : History) (hdist : FiniteActionDistribution arms (prob history))
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (tilt : Real) (htilt_nonneg : 0 <= tilt) (htilt_le : tilt <= epsilon) :
    Concentration.HasMGFUpperBoundAt
      (fun chosen =>
        tilt *
            (mixedSquaredImportanceWeightedLoss arms (prob history)
                (loss history) chosen -
              arms.sum (fun action => (loss history action) ^ 2)) -
          tilt ^ 2 *
            mixedSquaredEstimatorCenteredSecondMoment arms prob loss history)
      1 0 (finiteActionMeasure arms (prob history)) := by
  simpa using
    (finiteActionMixedSquaredEstimator_hasMGFUpperBoundAt_variance
      arms prob loss history hdist epsilon regularity tilt htilt_nonneg
        htilt_le).compensated

/-- An identified finite conditional action law yields a zero-budget
conditional MGF for the exact variance-compensated mixed-square increment. -/
theorem mixedSquaredEstimator_compensated_hasCondMGFUpperBoundAt_of_condDistrib
    {Omega : Type u} {History : Type v} {Action : Type*}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [mHistory : MeasurableSpace History] [StandardBorelSpace History]
    [mAction : MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (tilt : Real) (htilt_nonneg : 0 <= tilt) (htilt_le : tilt <= epsilon)
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source) :
    Concentration.HasCondMGFUpperBoundAt
      (mHistory.comap history) hhistory.comap_le
      (fun omega =>
        tilt *
            (mixedSquaredImportanceWeightedLoss arms (prob (history omega))
                (loss (history omega)) (action omega) -
              arms.sum (fun candidate =>
                (loss (history omega) candidate) ^ 2)) -
          tilt ^ 2 * mixedSquaredEstimatorCenteredSecondMoment
            arms prob loss (history omega))
      1 0 mu := by
  let mcond := mHistory.comap history
  let mean := fun h : History =>
    arms.sum (fun candidate => (loss h candidate) ^ 2)
  let X := fun omega =>
    mixedSquaredImportanceWeightedLoss arms (prob (history omega))
        (loss (history omega)) (action omega) - mean (history omega)
  let variance := mixedSquaredEstimatorCenteredSecondMoment arms prob loss
  let Z := fun omega => tilt * X omega - tilt ^ 2 * variance (history omega)
  have hmcond : mcond <= mOmega := hhistory.comap_le
  have hrawPair := measurable_mixedSquaredImportanceWeightedLoss_score
    arms prob loss source epsilon regularity
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun candidate hcandidate => ?_
    exact (regularity.measurable_loss candidate hcandidate).pow_const 2
  have hX : @Measurable Omega Real mOmega inferInstance X :=
    (hrawPair.comp (hhistory.prodMk haction)).sub (hmean.comp hhistory)
  have hvariance : Measurable variance :=
    measurable_mixedSquaredEstimatorCenteredSecondMoment
      arms prob loss source epsilon regularity
  have hZ : @Measurable Omega Real mOmega inferInstance Z :=
    (measurable_const.mul hX).sub
      (measurable_const.mul (hvariance.comp hhistory))
  have hdevmap :=
    mixedSquaredEstimatorDeviation_condExpKernel_map_eq_finiteActionMeasure_of_condDistrib
      (mOmega := mOmega) (mHistory := mHistory) (mAction := mAction)
      mu history hhistory action haction arms prob loss source epsilon regularity hcond
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
  have hkernel_map :
      Filter.Eventually
        (fun omega =>
          @Measure.map Omega Real mOmega inferInstance Z
              (@condExpKernel Omega mOmega _ mu _ mcond omega) =
            Measure.map
              (fun selected =>
                tilt *
                    (mixedSquaredImportanceWeightedLoss arms
                        (prob (history omega)) (loss (history omega)) selected -
                      mean (history omega)) -
                  tilt ^ 2 * variance (history omega))
              (finiteActionMeasure arms (prob (history omega))))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hdevmap, hkernel_Z_eq] with omega hmap hZeq
    let affine : Real -> Real := fun z =>
      tilt * z - tilt ^ 2 * variance (history omega)
    have haffine : Measurable affine := by fun_prop
    let score : Action -> Real := fun selected =>
      mixedSquaredImportanceWeightedLoss arms (prob (history omega))
          (loss (history omega)) selected - mean (history omega)
    have hscore : Measurable score :=
      (hrawPair.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    calc
      @Measure.map Omega Real mOmega inferInstance Z
          (@condExpKernel Omega mOmega _ mu _ mcond omega) =
          @Measure.map Omega Real mOmega inferInstance (fun y => affine (X y))
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
        rw [hmap]
      _ = Measure.map (fun selected => affine (score selected))
          (finiteActionMeasure arms (prob (history omega))) := by
        rw [Measure.map_map haffine hscore]
        congr 1
      _ = _ := rfl
  have hsub :=
    mixedSquaredEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      (mOmega := mOmega) (mHistory := mHistory) (mAction := mAction)
      mu history hhistory action haction arms prob loss source epsilon regularity hcond
  change Concentration.Kernel.HasMGFUpperBoundAt Z 1 0
    (@condExpKernel Omega mOmega _ mu _ mcond) (mu.trim hmcond)
  refine ⟨?_, ?_⟩
  · intro s
    rw [@ProbabilityTheory.condExpKernel_comp_trim
      Omega mcond mOmega _ mu _ hmcond]
    have hXint := hsub.integrable_exp_mul (s * tilt)
    let ceiling := (arms.card : Real) / epsilon
    let factor := fun omega =>
      Real.exp (-s * tilt ^ 2 * variance (history omega))
    have hfactor_meas : AEStronglyMeasurable[mOmega] factor mu := by
      have hfactor : @Measurable Omega Real mOmega inferInstance factor := by
        dsimp only [factor]
        fun_prop
      exact hfactor.aestronglyMeasurable
    have hfactor_bound :
        ∀ᵐ omega ∂mu, ‖factor omega‖ <=
          Real.exp (|s| * tilt ^ 2 * ceiling) := by
      filter_upwards [] with omega
      have hnonneg := mixedSquaredEstimatorCenteredSecondMoment_nonneg
        arms prob loss (history omega) (source.distribution (history omega))
      have hle := mixedSquaredEstimatorCenteredSecondMoment_le_card_div_floor
        arms prob loss (history omega) (source.distribution (history omega))
          epsilon regularity
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hsq : 0 <= tilt ^ 2 := sq_nonneg tilt
      calc
        -s * tilt ^ 2 * variance (history omega) <=
            |s| * tilt ^ 2 * variance (history omega) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (neg_le_abs s) hsq) hnonneg
        _ <= |s| * tilt ^ 2 * ceiling := by
          exact mul_le_mul_of_nonneg_left hle
            (mul_nonneg (abs_nonneg s) hsq)
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
  · apply Filter.Eventually.mono hkernel_map
    intro omega hmap
    let actionMu := finiteActionMeasure arms (prob (history omega))
    let score : Action -> Real := fun selected =>
      mixedSquaredImportanceWeightedLoss arms (prob (history omega))
          (loss (history omega)) selected - mean (history omega)
    let compensatedScore : Action -> Real := fun selected =>
      tilt * score selected - tilt ^ 2 * variance (history omega)
    have hscore : Measurable score :=
      (hrawPair.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hcompensatedScore : Measurable compensatedScore := by fun_prop
    have hfinite : Concentration.HasMGFUpperBoundAt
        compensatedScore 1 0 actionMu := by
      simpa [compensatedScore, score, actionMu, mean, variance] using
        finiteActionMixedSquaredEstimator_compensated_hasMGFUpperBoundAt
          arms prob loss (history omega) (source.distribution (history omega))
            epsilon regularity tilt htilt_nonneg htilt_le
    have htarget : Concentration.HasMGFUpperBoundAt id 1 0
        (Measure.map compensatedScore actionMu) := by
      exact (Concentration.HasMGFUpperBoundAt.id_map_iff
        hcompensatedScore.aemeasurable).2 hfinite
    rw [← hmap] at htarget
    exact ((Concentration.HasMGFUpperBoundAt.id_map_iff hZ.aemeasurable).1
      htarget).mgf_le

theorem sampledPredictableMixedSquaredCompensated_zero_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (tilt : Real) (htilt_nonneg : 0 <= tilt)
    (htilt_le : tilt <= gamma / (arms.card : Real)) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Concentration.HasCondMGFUpperBoundAt
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (fun sample =>
        tilt * sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss 0 sample -
          tilt ^ 2 * sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss 0 sample)
      1 0 mu := by
  dsimp only
  let algorithm := sampledImportanceWeightedHistoryAlgorithm arms harms
    eta gamma hgamma_pos.le hgamma_le_one
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
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
    mixedSquaredEstimator_compensated_hasCondMGFUpperBoundAt_of_condDistrib
      mu history measurable_fst action (by fun_prop) arms prob loss.initial
        source (gamma / (arms.card : Real)) regularity
        tilt htilt_nonneg htilt_le hcond
  simpa [mu, history, action, prob,
    sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledTrajectoryPredictableMixedSquaredVarianceAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

theorem sampledPredictableMixedSquaredCompensated_succ_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat)
    (tilt : Real) (htilt_nonneg : 0 <= tilt)
    (htilt_le : tilt <= gamma / (arms.card : Real)) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    Concentration.HasCondMGFUpperBoundAt
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (fun sample =>
        tilt * sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss (n + 1) sample -
          tilt ^ 2 * sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss (n + 1) sample)
      1 0 mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
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
  have hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source := by
    simpa [mu, history, action, prob, source] using
      (sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss n)
  have hmgf :=
    mixedSquaredEstimator_compensated_hasCondMGFUpperBoundAt_of_condDistrib
      mu history hhistory action haction arms prob roundLoss source
        (gamma / (arms.card : Real)) regularity
        tilt htilt_nonneg htilt_le hcond
  simpa [mu, history, action, prob, roundLoss,
    sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledTrajectoryPredictableMixedSquaredVarianceAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

/-- Shifted variance-compensated increment process. Index `i + 1` contains
the actual-time `i` centered increment and its predictable variance. -/
noncomputable def sampledPredictableMixedSquaredCompensatedProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma tilt : Real)
    (loss : PredictableLossVector Env Action) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Real :=
  fun i sample =>
    tilt * sampledPredictableMixedSquaredDeviationProcess
        arms eta gamma loss i sample -
      tilt ^ 2 * sampledPredictableMixedSquaredVarianceProcess
        arms eta gamma loss i sample

theorem sampledPredictableMixedSquaredCompensatedProcess_stronglyAdapted
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma tilt : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    StronglyAdapted (sampledPredictableDeviationFiltration Env Action)
      (sampledPredictableMixedSquaredCompensatedProcess
        arms eta gamma tilt loss) := by
  have hdeviation :=
    sampledPredictableMixedSquaredDeviationProcess_stronglyAdapted
      arms harms eta gamma hgamma_pos hgamma_le_one loss
  have hvariance :=
    (sampledPredictableMixedSquaredVarianceProcess_isPredictable
      arms harms eta gamma hgamma_pos hgamma_le_one loss).adapted
  intro i
  exact ((hdeviation i).const_mul tilt).sub
    ((hvariance i).const_mul (tilt ^ 2))

theorem sampledPredictableMixedSquaredCompensatedProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma tilt : Real)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledPredictableMixedSquaredCompensatedProcess
          arms eta gamma tilt loss i sample) =
      tilt * (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss i sample) -
        tilt ^ 2 * (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) := by
  simp_rw [sampledPredictableMixedSquaredCompensatedProcess]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sampledPredictableMixedSquaredDeviationProcess_sum_range_succ,
    sampledPredictableMixedSquaredVarianceProcess_sum_range_succ]

/-- Fixed-tilt predictable-variance tail for the generated centered
mixed-square process. The variance is kept random and enters through the event
`sum V <= varianceBudget`; it is not replaced by the deterministic
`horizon * K / epsilon` envelope. -/
theorem sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_fixedTilt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (tilt : Real) (htilt_nonneg : 0 <= tilt)
    (htilt_le : tilt <= gamma / (arms.card : Real))
    (threshold varianceBudget : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        threshold <= (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss i sample) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
      ENNReal.ofReal (Real.exp
        (-tilt * threshold + tilt ^ 2 * varianceBudget)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Z := sampledPredictableMixedSquaredCompensatedProcess
    arms eta gamma tilt loss
  let psiZ : Nat -> Real := fun _ => 0
  let compensatedThreshold := tilt * threshold - tilt ^ 2 * varianceBudget
  let targetEvent := {sample : Env × ((k : Nat) -> Action × Real) |
    compensatedThreshold <=
      tilt * (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredDeviationAt
          arms eta gamma loss i sample) -
      tilt ^ 2 * (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample)}
  let sourceEvent := {sample : Env × ((k : Nat) -> Action × Real) |
    threshold <= (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss i sample) ∧
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample) <= varianceBudget}
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Z := by
    simpa [F, Z] using
      sampledPredictableMixedSquaredCompensatedProcess_stronglyAdapted
        arms harms eta gamma tilt hgamma_pos hgamma_le_one loss
  have hzero : Concentration.HasMGFUpperBoundAt (Z 0) 1 (psiZ 0) mu := by
    have hzero' : Concentration.HasMGFUpperBoundAt
        (fun _ : Env × ((k : Nat) -> Action × Real) => 0) 1 0 mu := by
      constructor
      · intro s
        simp
      · simp [ProbabilityTheory.mgf]
    have hZ0 : Z 0 =
        (fun _ : Env × ((k : Nat) -> Action × Real) => 0) := by
      funext sample
      simp [Z, sampledPredictableMixedSquaredCompensatedProcess,
        sampledPredictableMixedSquaredDeviationProcess,
        sampledPredictableMixedSquaredVarianceProcess]
    rw [hZ0]
    simpa [psiZ] using hzero'
  have hcond : forall i, i < (horizon + 1) - 1 ->
      Concentration.HasCondMGFUpperBoundAt
        (F i) (F.le i) (Z (i + 1)) 1 (psiZ (i + 1)) mu := by
    intro i _hi
    cases i with
    | zero =>
        simpa [mu, F, Z, psiZ,
          sampledPredictableMixedSquaredCompensatedProcess,
          sampledPredictableMixedSquaredDeviationProcess,
          sampledPredictableMixedSquaredVarianceProcess] using
          (sampledPredictableMixedSquaredCompensated_zero_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss
              tilt htilt_nonneg htilt_le)
    | succ n =>
        simpa [mu, F, Z, psiZ,
          sampledPredictableMixedSquaredCompensatedProcess,
          sampledPredictableMixedSquaredDeviationProcess,
          sampledPredictableMixedSquaredVarianceProcess,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledPredictableMixedSquaredCompensated_succ_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
              tilt htilt_nonneg htilt_le)
  have hreal := Concentration.measure_sum_ge_le_of_hasCondMGFUpperBoundAt
    hadapted hzero (horizon + 1) hcond compensatedThreshold (by norm_num)
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledPredictableMixedSquaredCompensatedProcess_sum_range_succ
      arms eta gamma tilt loss horizon sample
  have hreal' : mu.real targetEvent <=
      Real.exp (-tilt * threshold + tilt ^ 2 * varianceBudget) := by
    simpa [Z, psiZ, targetEvent, compensatedThreshold, hprocess,
      sub_eq_add_neg, add_comm] using hreal
  have htarget : mu targetEvent <=
      ENNReal.ofReal (Real.exp
        (-tilt * threshold + tilt ^ 2 * varianceBudget)) := by
    rw [Measure.real] at hreal'
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu targetEvent) (Real.exp_pos _).le).2 hreal'
  have hsubset : sourceEvent ⊆ targetEvent := by
    intro sample hsample
    change threshold <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredDeviationAt
          arms eta gamma loss i sample) ∧
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample) <= varianceBudget at hsample
    change compensatedThreshold <=
      tilt * (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredDeviationAt
          arms eta gamma loss i sample) -
      tilt ^ 2 * (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample)
    have hdeviation := mul_le_mul_of_nonneg_left hsample.1 htilt_nonneg
    have hvariance := mul_le_mul_of_nonneg_left hsample.2 (sq_nonneg tilt)
    dsimp only [compensatedThreshold]
    linarith
  change mu sourceEvent <= _
  exact (measure_mono hsubset).trans htarget

/-- Optimized radius for the mixed-square predictable-variance event. -/
noncomputable def sampledMixedSquaredPredictableVarianceRadius
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma varianceBudget delta : Real) : Real :=
  let epsilon := gamma / (arms.card : Real)
  let budget := max (Real.log (1 / delta)) 0
  2 * Real.sqrt (varianceBudget * budget) + budget / epsilon

/-- Delta-shaped predictable-variance Bernstein/Freedman bound for the
generated centered mixed-square process. This controls the deviation jointly
with the event that its cumulative predictable variance is at most
`varianceBudget`. -/
theorem sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        sampledMixedSquaredPredictableVarianceRadius
            arms gamma varianceBudget delta <=
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredDeviationAt
              arms eta gamma loss i sample) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let epsilon := gamma / (arms.card : Real)
  have hepsilon : 0 < epsilon := by
    simpa [epsilon] using explorationFloor_pos arms harms gamma hgamma_pos
  let deviation := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss i sample)
  let predictableVariance := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  have htail :=
    Concentration.measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
      mu deviation predictableVariance 1 varianceBudget epsilon delta
        (by norm_num) hvarianceBudget hepsilon hdelta (by
          intro tilt htilt_nonneg htilt_le
          simpa [mu, deviation, predictableVariance, epsilon] using
            (sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_fixedTilt
              prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
                tilt htilt_nonneg (by simpa [epsilon] using htilt_le)
                (Concentration.quadraticFixedMGFRadius
                  1 varianceBudget epsilon delta) varianceBudget))
  simpa [sampledMixedSquaredPredictableVarianceRadius,
    Concentration.quadraticFixedMGFRadius, mu, epsilon, deviation,
    predictableVariance] using htail

end BanditRLProof.Exp3
