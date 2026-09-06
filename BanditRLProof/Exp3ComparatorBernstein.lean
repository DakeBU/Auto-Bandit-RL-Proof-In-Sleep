import BanditRLProof.ConcentrationFixedMGF
import BanditRLProof.Exp3ComparatorConfidence

/-!
# Variance-sensitive fixed-comparator EXP3 concentration

This module replaces the range-squared Hoeffding proxy for one fixed comparator estimator by a
fixed-tilt second-moment bound.  The scalar input is the quadratic exponential remainder on
`[-1, 1]`; the probabilistic input is the exact second moment of the importance-weighted
estimator under its finite sampling law.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Real

namespace Concentration

/-- On `[-1, 1]`, the exponential remainder is bounded by the square. -/
theorem exp_le_one_add_self_add_sq_of_abs_le_one {x : Real} (hx : |x| <= 1) :
    Real.exp x <= 1 + x + x ^ 2 := by
  have hrem := Real.abs_exp_sub_one_sub_id_le hx
  have hle : Real.exp x - 1 - x <= |Real.exp x - 1 - x| := le_abs_self _
  linarith

/-- Optimize a quadratic fixed-tilt MGF budget under the hard constraint `tilt <= epsilon`. -/
theorem exists_tilt_fixedMGF_exponent_le_neg
    (horizon epsilon budget : Real)
    (hhorizon : 0 <= horizon) (hepsilon : 0 < epsilon)
    (hbudget : 0 <= budget) :
    exists tilt : Real, 0 <= tilt ∧ tilt <= epsilon ∧
      -tilt *
          (2 * Real.sqrt (horizon * budget / epsilon) + budget / epsilon) +
        horizon * (tilt ^ 2 / epsilon) <= -budget := by
  by_cases hbudget_zero : budget = 0
  · refine ⟨0, le_rfl, hepsilon.le, ?_⟩
    simp [hbudget_zero]
  have hbudget_pos : 0 < budget :=
    lt_of_le_of_ne hbudget (Ne.symm hbudget_zero)
  by_cases hsmall : budget <= epsilon * horizon
  · have hhorizon_pos : 0 < horizon := by nlinarith
    let tilt := Real.sqrt (epsilon * budget / horizon)
    let scale := Real.sqrt (horizon * budget / epsilon)
    have htilt_nonneg : 0 <= tilt := Real.sqrt_nonneg _
    have hscale_nonneg : 0 <= scale := Real.sqrt_nonneg _
    have htilt_sq : tilt ^ 2 = epsilon * budget / horizon := by
      dsimp only [tilt]
      rw [Real.sq_sqrt]
      positivity
    have hscale_sq : scale ^ 2 = horizon * budget / epsilon := by
      dsimp only [scale]
      rw [Real.sq_sqrt]
      positivity
    have hprod_sq : (tilt * scale) ^ 2 = budget ^ 2 := by
      rw [mul_pow, htilt_sq, hscale_sq]
      field_simp
    have hprod : tilt * scale = budget := by
      nlinarith [mul_nonneg htilt_nonneg hscale_nonneg]
    have htilt_sq_le : tilt ^ 2 <= epsilon ^ 2 := by
      rw [htilt_sq, div_le_iff₀ hhorizon_pos]
      nlinarith
    have htilt_le : tilt <= epsilon :=
      (sq_le_sq₀ htilt_nonneg hepsilon.le).mp htilt_sq_le
    refine ⟨tilt, htilt_nonneg, htilt_le, ?_⟩
    change -tilt * (2 * scale + budget / epsilon) +
      horizon * (tilt ^ 2 / epsilon) <= -budget
    have hbudget_term : horizon * (tilt ^ 2 / epsilon) = budget := by
      rw [htilt_sq]
      field_simp
    have hextra : 0 <= tilt * (budget / epsilon) :=
      mul_nonneg htilt_nonneg (div_nonneg hbudget hepsilon.le)
    rw [hbudget_term]
    nlinarith
  · refine ⟨epsilon, hepsilon.le, le_rfl, ?_⟩
    let scale := Real.sqrt (horizon * budget / epsilon)
    have hscale_nonneg : 0 <= scale :=
      Real.sqrt_nonneg _
    have hscale_sq : scale ^ 2 = horizon * budget / epsilon := by
      dsimp only [scale]
      rw [Real.sq_sqrt]
      positivity
    have hlarge : epsilon * horizon < budget := lt_of_not_ge hsmall
    have hhorizon_sq_le : horizon ^ 2 <= scale ^ 2 := by
      rw [hscale_sq, le_div_iff₀ hepsilon]
      have hmul := mul_le_mul_of_nonneg_right hlarge.le hhorizon
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hmul
    have hhorizon_le_scale : horizon <= scale :=
      (sq_le_sq₀ hhorizon hscale_nonneg).mp hhorizon_sq_le
    have hcover : horizon * epsilon <= 2 * epsilon * scale := by
      calc
        horizon * epsilon = epsilon * horizon := by ring
        _ <= epsilon * scale :=
          mul_le_mul_of_nonneg_left hhorizon_le_scale hepsilon.le
        _ <= 2 * epsilon * scale := by
          nlinarith [mul_nonneg hepsilon.le hscale_nonneg]
    calc
      -epsilon *
            (2 * Real.sqrt (horizon * budget / epsilon) + budget / epsilon) +
          horizon * (epsilon ^ 2 / epsilon) =
        -2 * epsilon * Real.sqrt (horizon * budget / epsilon) - budget +
          horizon * epsilon := by
            field_simp
            ring
      _ <= -budget := by
        change -2 * epsilon * scale - budget + horizon * epsilon <= -budget
        nlinarith

end Concentration

namespace Exp3

universe u

/-- Exact centered second moment of one fixed-arm importance-weighted estimator. -/
theorem sum_prob_mul_sq_comparatorEstimatorDeviation_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hdist : FiniteActionDistribution arms prob)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (hprob : prob comparator ≠ 0) :
    arms.sum (fun chosen =>
        prob chosen *
          (importanceWeightedLoss prob loss chosen comparator - loss comparator) ^ 2) =
      (loss comparator) ^ 2 / prob comparator - (loss comparator) ^ 2 := by
  let raw := fun chosen => importanceWeightedLoss prob loss chosen comparator
  have hfirst : arms.sum (fun chosen => prob chosen * raw chosen) = loss comparator := by
    simpa [raw] using sum_prob_mul_importanceWeightedLoss_eq_loss
      arms prob loss comparator hcomparator hprob
  have hsecond : arms.sum (fun chosen => prob chosen * (raw chosen) ^ 2) =
      (loss comparator) ^ 2 / prob comparator := by
    rw [Finset.sum_eq_single comparator]
    · simp [raw, importanceWeightedLoss]
      field_simp
    · intro chosen hchosen hne
      simp [raw, importanceWeightedLoss, hne]
    · exact fun hnotmem => (hnotmem hcomparator).elim
  have hcenter (chosen : Action) :
      prob chosen * (raw chosen - loss comparator) ^ 2 =
        (prob chosen * (raw chosen) ^ 2 -
          2 * loss comparator * (prob chosen * raw chosen)) +
          (loss comparator) ^ 2 * prob chosen := by
    ring
  change arms.sum (fun chosen =>
    prob chosen * (raw chosen - loss comparator) ^ 2) = _
  simp_rw [hcenter]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsecond, hfirst, hdist.sum_eq_one]
  ring

/-- The centered comparator estimator has second moment at most the reciprocal probability floor. -/
theorem sum_prob_mul_sq_comparatorEstimatorDeviation_le_inv_floor
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hdist : FiniteActionDistribution arms prob)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (hfloor : epsilon <= prob comparator)
    (hloss : loss comparator ∈ Set.Icc (0 : Real) 1) :
    arms.sum (fun chosen =>
        prob chosen *
          (importanceWeightedLoss prob loss chosen comparator - loss comparator) ^ 2) <=
      1 / epsilon := by
  have hprob_pos : 0 < prob comparator := hepsilon.trans_le hfloor
  rw [sum_prob_mul_sq_comparatorEstimatorDeviation_eq arms prob loss hdist
    comparator hcomparator hprob_pos.ne']
  have hloss_sq : (loss comparator) ^ 2 <= 1 := by
    simpa using (sq_le_sq₀ hloss.1 zero_le_one).2 hloss.2
  have hdiv : (loss comparator) ^ 2 / prob comparator <= 1 / epsilon := by
    calc
      (loss comparator) ^ 2 / prob comparator <= 1 / prob comparator :=
        div_le_div_of_nonneg_right hloss_sq hprob_pos.le
      _ <= 1 / epsilon := one_div_le_one_div_of_le hepsilon hfloor
  nlinarith [sq_nonneg (loss comparator)]

/-- Fixed-tilt MGF budget for a finite-law fixed-comparator estimator. -/
theorem finiteActionComparatorEstimator_hasMGFUpperBoundAt
    {Action : Type u} [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hdist : FiniteActionDistribution arms prob)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (hfloor : epsilon <= prob comparator)
    (hloss : loss comparator ∈ Set.Icc (0 : Real) 1)
    (tilt : Real) (htilt_nonneg : 0 <= tilt) (htilt_le : tilt <= epsilon) :
    Concentration.HasMGFUpperBoundAt
      (fun chosen =>
        importanceWeightedLoss prob loss chosen comparator - loss comparator)
      tilt (tilt ^ 2 / epsilon) (finiteActionMeasure arms prob) := by
  let X := fun chosen =>
    importanceWeightedLoss prob loss chosen comparator - loss comparator
  letI : IsProbabilityMeasure (finiteActionMeasure arms prob) :=
    finiteActionMeasure_isProbabilityMeasure arms prob hdist
  have hprob_pos : 0 < prob comparator := hepsilon.trans_le hfloor
  have hprob_le_one : prob comparator <= 1 := by
    calc
      prob comparator <= arms.sum prob := by
        exact Finset.single_le_sum (fun action haction => hdist.nonneg action haction)
          hcomparator
      _ = 1 := hdist.sum_eq_one
  have hepsilon_le_one : epsilon <= 1 := hfloor.trans hprob_le_one
  have hinv_nonneg : 0 <= 1 / epsilon := (one_div_pos.mpr hepsilon).le
  have hone_le_inv : 1 <= 1 / epsilon := by
    rw [le_div_iff₀ hepsilon]
    simpa using hepsilon_le_one
  have hX_bound (chosen : Action) : |X chosen| <= 1 / epsilon := by
    have hraw_nonneg : 0 <= importanceWeightedLoss prob loss chosen comparator :=
      importanceWeightedLoss_nonneg (chosen := chosen)
        (hdist.nonneg comparator hcomparator) hloss.1
    have hraw_le : importanceWeightedLoss prob loss chosen comparator <= 1 / epsilon := by
      unfold importanceWeightedLoss
      split_ifs
      · exact (div_le_div_of_nonneg_right hloss.2 hprob_pos.le).trans
          (one_div_le_one_div_of_le hepsilon hfloor)
      · exact hinv_nonneg
    dsimp only [X]
    rw [abs_le]
    constructor
    · calc
        -(1 / epsilon) <= -loss comparator := by
          exact neg_le_neg (hloss.2.trans hone_le_inv)
        _ <= importanceWeightedLoss prob loss chosen comparator - loss comparator := by
          linarith
    · calc
        importanceWeightedLoss prob loss chosen comparator - loss comparator <=
            importanceWeightedLoss prob loss chosen comparator := by
          linarith [hloss.1]
        _ <= 1 / epsilon := hraw_le
  constructor
  · intro s
    rw [finiteActionMeasure]
    refine integrable_finset_sum_measure.2 fun action haction => ?_
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · rw [ProbabilityTheory.mgf, integral_finiteActionMeasure_eq_sum arms prob hdist]
    have hexp (chosen : Action) (hchosen : chosen ∈ arms) :
        Real.exp (tilt * X chosen) <=
          1 + tilt * X chosen + (tilt * X chosen) ^ 2 := by
      apply Concentration.exp_le_one_add_self_add_sq_of_abs_le_one
      rw [abs_mul, abs_of_nonneg htilt_nonneg]
      calc
        tilt * |X chosen| <= tilt * (1 / epsilon) :=
          mul_le_mul_of_nonneg_left (hX_bound chosen) htilt_nonneg
        _ <= epsilon * (1 / epsilon) :=
          mul_le_mul_of_nonneg_right htilt_le hinv_nonneg
        _ = 1 := by field_simp
    calc
      arms.sum (fun chosen => prob chosen * Real.exp (tilt * X chosen)) <=
          arms.sum (fun chosen =>
            prob chosen * (1 + tilt * X chosen + (tilt * X chosen) ^ 2)) := by
        apply Finset.sum_le_sum
        intro chosen hchosen
        exact mul_le_mul_of_nonneg_left (hexp chosen hchosen)
          (hdist.nonneg chosen hchosen)
      _ = 1 + tilt * arms.sum (fun chosen => prob chosen * X chosen) +
          tilt ^ 2 * arms.sum (fun chosen => prob chosen * (X chosen) ^ 2) := by
        have hterm (chosen : Action) :
            prob chosen * (1 + tilt * X chosen + (tilt * X chosen) ^ 2) =
              (prob chosen + tilt * (prob chosen * X chosen)) +
                tilt ^ 2 * (prob chosen * (X chosen) ^ 2) := by ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hdist.sum_eq_one]
      _ <= 1 + tilt ^ 2 * (1 / epsilon) := by
        have hmean : arms.sum (fun chosen => prob chosen * X chosen) = 0 := by
          dsimp only [X]
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib,
            sum_prob_mul_importanceWeightedLoss_eq_loss arms prob loss comparator
              hcomparator hprob_pos.ne', ← Finset.sum_mul, hdist.sum_eq_one]
          ring
        rw [hmean, mul_zero, add_zero]
        have hsecond := mul_le_mul_of_nonneg_left
          (by
            simpa [X] using
              sum_prob_mul_sq_comparatorEstimatorDeviation_le_inv_floor
                arms prob loss hdist epsilon hepsilon comparator hcomparator hfloor hloss)
          (sq_nonneg tilt)
        simpa only [X, one_div, add_comm] using add_le_add_left hsecond 1
      _ <= Real.exp (tilt ^ 2 / epsilon) := by
        rw [show tilt ^ 2 * (1 / epsilon) = tilt ^ 2 / epsilon by ring]
        simpa [add_comm] using Real.add_one_le_exp (tilt ^ 2 / epsilon)

/-- A finite conditional action law supplies the variance-sensitive fixed-tilt MGF budget for
one fixed comparator estimator. -/
theorem comparatorEstimator_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
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
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (tilt : Real) (htilt_nonneg : 0 <= tilt) (htilt_le : tilt <= epsilon)
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source) :
    Concentration.HasCondMGFUpperBoundAt
      (mHistory.comap history)
      hhistory.comap_le
      (fun omega =>
        importanceWeightedLoss (prob (history omega)) (loss (history omega))
          (action omega) comparator - loss (history omega) comparator)
      tilt (tilt ^ 2 / epsilon) mu := by
  let mcond := mHistory.comap history
  let X := fun omega =>
    importanceWeightedLoss (prob (history omega)) (loss (history omega))
      (action omega) comparator - loss (history omega) comparator
  let target : Omega -> Measure Real := fun omega => Measure.map
    (fun selected =>
      importanceWeightedLoss (prob (history omega)) (loss (history omega))
        selected comparator - loss (history omega) comparator)
    (finiteActionMeasure arms (prob (history omega)))
  have hmcond : mcond <= mOmega := hhistory.comap_le
  have hrawPair := measurable_importanceWeightedLoss_score
    arms prob loss source epsilon regularity comparator hcomparator
  have hX : @Measurable Omega Real mOmega inferInstance X :=
    (hrawPair.comp (hhistory.prodMk haction)).sub
      ((regularity.measurable_loss comparator hcomparator).comp hhistory)
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
          X
          (fun y =>
            importanceWeightedLoss (prob (history omega)) (loss (history omega))
              (action y) comparator - loss (history omega) comparator))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hhistory_ae] with omega hfreeze
    filter_upwards [hfreeze] with y hy
    simp only [X]
    rw [hy]
  have hkernel_map :
      Filter.Eventually
        (fun omega =>
          @Measure.map Omega Real mOmega inferInstance X
              (@condExpKernel Omega mOmega _ mu _ mcond omega) =
            target omega)
        (ae (mu.trim hmcond)) := by
    filter_upwards [haction_map, hkernel_X_eq] with omega haction_eq hXeq
    let score : Action -> Real := fun selected =>
      importanceWeightedLoss (prob (history omega)) (loss (history omega))
        selected comparator - loss (history omega) comparator
    have hscore : Measurable score := by
      exact (hrawPair.comp (measurable_const.prodMk measurable_id)).sub
        measurable_const
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
      _ = target omega := by rw [haction_eq]
  have hsub :=
    comparatorEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      (mOmega := mOmega) (mHistory := mHistory) (mAction := mAction)
      mu history hhistory action haction arms prob loss source epsilon regularity
        comparator hcomparator hcond
  change Concentration.Kernel.HasMGFUpperBoundAt X tilt (tilt ^ 2 / epsilon)
    (@condExpKernel Omega mOmega _ mu _ mcond) (mu.trim hmcond)
  refine ⟨?_, ?_⟩
  · intro s
    rw [@ProbabilityTheory.condExpKernel_comp_trim
      Omega mcond mOmega _ mu _ hmcond]
    simpa [X] using hsub.integrable_exp_mul s
  filter_upwards [hkernel_map] with omega hmap
  let actionMu := finiteActionMeasure arms (prob (history omega))
  let score : Action -> Real := fun selected =>
    importanceWeightedLoss (prob (history omega)) (loss (history omega))
      selected comparator - loss (history omega) comparator
  have hscore : Measurable score :=
    (hrawPair.comp (measurable_const.prodMk measurable_id)).sub measurable_const
  have hfinite : Concentration.HasMGFUpperBoundAt score tilt
      (tilt ^ 2 / epsilon) actionMu := by
    simpa [score, actionMu] using
      finiteActionComparatorEstimator_hasMGFUpperBoundAt
        arms (prob (history omega)) (loss (history omega))
          (source.distribution (history omega)) epsilon regularity.epsilon_pos
          comparator hcomparator
          (regularity.prob_floor (history omega) comparator hcomparator)
          (regularity.loss_mem_Icc (history omega) comparator hcomparator)
          tilt htilt_nonneg htilt_le
  have htarget : Concentration.HasMGFUpperBoundAt id tilt
      (tilt ^ 2 / epsilon) (target omega) := by
    simpa [target, actionMu, score] using
      (Concentration.HasMGFUpperBoundAt.id_map_iff hscore.aemeasurable).2 hfinite
  rw [← hmap] at htarget
  exact ((Concentration.HasMGFUpperBoundAt.id_map_iff hX.aemeasurable).1 htarget).mgf_le

theorem sampledPredictableComparatorEstimatorDeviation_zero_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (tilt : Real) (htilt_nonneg : 0 <= tilt)
    (htilt_le : tilt <= gamma / (arms.card : Real)) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Concentration.HasCondMGFUpperBoundAt
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectoryPredictableComparatorEstimatorDeviationAt
        arms eta gamma loss comparator 0)
      tilt (tilt ^ 2 / (gamma / (arms.card : Real))) mu := by
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
    comparatorEstimator_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
      mu history measurable_fst action (by fun_prop) arms prob loss.initial
        source (gamma / (arms.card : Real)) regularity comparator hcomparator
        tilt htilt_nonneg htilt_le hcond
  simpa [mu, history, action, prob,
    sampledTrajectoryPredictableComparatorEstimatorDeviationAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

theorem sampledPredictableComparatorEstimatorDeviation_succ_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms) (n : Nat)
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
      (sampledTrajectoryPredictableComparatorEstimatorDeviationAt
        arms eta gamma loss comparator (n + 1))
      tilt (tilt ^ 2 / (gamma / (arms.card : Real))) mu := by
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
    comparatorEstimator_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
      mu history hhistory action haction arms prob roundLoss source
        (gamma / (arms.card : Real)) regularity comparator hcomparator
        tilt htilt_nonneg htilt_le hcond
  simpa [mu, history, action, prob, roundLoss,
    sampledTrajectoryPredictableComparatorEstimatorDeviationAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

theorem sampledObservedComparatorEstimatorDeviation_zero_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (tilt : Real) (htilt_nonneg : 0 <= tilt)
    (htilt_le : tilt <= gamma / (arms.card : Real)) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Concentration.HasCondMGFUpperBoundAt
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectoryObservedComparatorEstimatorDeviationAt
        arms eta gamma loss comparator 0)
      tilt (tilt ^ 2 / (gamma / (arms.card : Real))) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  have hhistory : Measurable history := measurable_fst
  let mcond := (inferInstance : MeasurableSpace Env).comap history
  letI : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    Prod.instMeasurableSpace
  have hmcond : mcond <= Prod.instMeasurableSpace := hhistory.comap_le
  have hpredictable :=
    sampledPredictableComparatorEstimatorDeviation_zero_hasCondMGFUpperBoundAt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator hcomparator
        tilt htilt_nonneg htilt_le
  dsimp only at hpredictable
  have hobserved :=
    (observedAt_eq_predictableAt_ae prior arms harms eta gamma hgamma_pos.le
      hgamma_le_one loss 0 comparator).1
  have hdeviation :
      sampledTrajectoryPredictableComparatorEstimatorDeviationAt
          arms eta gamma loss comparator 0 =ᵐ[mu]
        sampledTrajectoryObservedComparatorEstimatorDeviationAt
          arms eta gamma loss comparator 0 := by
    filter_upwards [hobserved] with sample hs
    simp only [sampledTrajectoryPredictableComparatorEstimatorDeviationAt,
      sampledTrajectoryObservedComparatorEstimatorDeviationAt]
    rw [hs]
  change Concentration.Kernel.HasMGFUpperBoundAt
    (sampledTrajectoryPredictableComparatorEstimatorDeviationAt
      arms eta gamma loss comparator 0)
    tilt (tilt ^ 2 / (gamma / (arms.card : Real)))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hpredictable
  change Concentration.Kernel.HasMGFUpperBoundAt
    (sampledTrajectoryObservedComparatorEstimatorDeviationAt
      arms eta gamma loss comparator 0)
    tilt (tilt ^ 2 / (gamma / (arms.card : Real)))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply hpredictable.congr
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

theorem sampledObservedComparatorEstimatorDeviation_succ_hasCondMGFUpperBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms) (n : Nat)
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
      (sampledTrajectoryObservedComparatorEstimatorDeviationAt
        arms eta gamma loss comparator (n + 1))
      tilt (tilt ^ 2 / (gamma / (arms.card : Real))) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  have hhistory : Measurable history := measurable_fst.prodMk
    ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  let mcond := (inferInstance : MeasurableSpace
    (Env × History.FinitePairHistory Action Real n)).comap history
  letI : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    Prod.instMeasurableSpace
  have hmcond : mcond <= Prod.instMeasurableSpace := hhistory.comap_le
  have hpredictable :=
    sampledPredictableComparatorEstimatorDeviation_succ_hasCondMGFUpperBoundAt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator
        hcomparator n tilt htilt_nonneg htilt_le
  dsimp only at hpredictable
  have hobserved :=
    (observedAt_eq_predictableAt_ae prior arms harms eta gamma hgamma_pos.le
      hgamma_le_one loss (n + 1) comparator).1
  have hdeviation :
      sampledTrajectoryPredictableComparatorEstimatorDeviationAt
          arms eta gamma loss comparator (n + 1) =ᵐ[mu]
        sampledTrajectoryObservedComparatorEstimatorDeviationAt
          arms eta gamma loss comparator (n + 1) := by
    filter_upwards [hobserved] with sample hs
    simp only [sampledTrajectoryPredictableComparatorEstimatorDeviationAt,
      sampledTrajectoryObservedComparatorEstimatorDeviationAt]
    rw [hs]
  change Concentration.Kernel.HasMGFUpperBoundAt
    (sampledTrajectoryPredictableComparatorEstimatorDeviationAt
      arms eta gamma loss comparator (n + 1))
    tilt (tilt ^ 2 / (gamma / (arms.card : Real)))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hpredictable
  change Concentration.Kernel.HasMGFUpperBoundAt
    (sampledTrajectoryObservedComparatorEstimatorDeviationAt
      arms eta gamma loss comparator (n + 1))
    tilt (tilt ^ 2 / (gamma / (arms.card : Real)))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply hpredictable.congr
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

/-- Variance-sensitive finite-horizon Chernoff bound for one fixed comparator on the generated
EXP3 trajectory.  The per-round budget is linear, rather than quadratic, in the reciprocal
exploration floor. -/
theorem sampledObservedComparatorEstimatorDeviation_sum_tail_fixedTilt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon : Nat) (tilt : Real) (htilt_nonneg : 0 <= tilt)
    (htilt_le : tilt <= gamma / (arms.card : Real)) (threshold : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu.real {sample | threshold <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryObservedComparatorEstimatorDeviationAt
          arms eta gamma loss comparator i sample)} <=
      Real.exp (-tilt * threshold +
        (horizon : Real) * (tilt ^ 2 / (gamma / (arms.card : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledObservedComparatorEstimatorDeviationProcess
    arms eta gamma loss comparator
  let psiY : Nat -> Real
    | 0 => 0
    | _i + 1 => tilt ^ 2 / (gamma / (arms.card : Real))
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (sampledObservedComparatorEstimatorDeviationProcess_stronglyAdapted
        arms harms eta gamma hgamma_pos.le hgamma_le_one loss comparator hcomparator)
  have hzero : Concentration.HasMGFUpperBoundAt (Y 0) tilt (psiY 0) mu := by
    change Concentration.HasMGFUpperBoundAt (fun _ => 0) tilt 0 mu
    constructor
    · intro s
      simp
    · simp [ProbabilityTheory.mgf]
  have hcond : forall i, i < (horizon + 1) - 1 ->
      Concentration.HasCondMGFUpperBoundAt
        (F i) (F.le i) (Y (i + 1)) tilt (psiY (i + 1)) mu := by
    intro i _hi
    cases i with
    | zero =>
        simpa [mu, F, Y, psiY,
          sampledObservedComparatorEstimatorDeviationProcess] using
          (sampledObservedComparatorEstimatorDeviation_zero_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator
              hcomparator tilt htilt_nonneg htilt_le)
    | succ n =>
        simpa [mu, F, Y, psiY,
          sampledObservedComparatorEstimatorDeviationProcess,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledObservedComparatorEstimatorDeviation_succ_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator
              hcomparator n tilt htilt_nonneg htilt_le)
  have htail := Concentration.measure_sum_ge_le_of_hasCondMGFUpperBoundAt
    hadapted hzero (horizon + 1) hcond threshold htilt_nonneg
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledObservedComparatorEstimatorDeviationProcess_sum_range_succ
      arms eta gamma loss comparator horizon sample
  have hbudget_aux (n : Nat) : (Finset.range (n + 1)).sum psiY =
      (n : Real) * (tilt ^ 2 / (gamma / (arms.card : Real))) := by
    induction n with
    | zero => simp [psiY]
    | succ n ih =>
        rw [show Nat.succ n + 1 = (n + 1) + 1 by omega,
          Finset.sum_range_succ, ih]
        push_cast
        ring
  have hbudget := hbudget_aux horizon
  simpa [Y, hprocess, hbudget] using htail

/-- Variance-sensitive confidence radius obtained by optimizing the fixed-tilt comparator tail. -/
noncomputable def sampledComparatorEstimatorBernsteinConfidenceRadius
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  let budget := max (Real.log (1 / delta)) 0
  2 * Real.sqrt
      ((horizon : Real) * budget / (gamma / (arms.card : Real))) +
    budget / (gamma / (arms.card : Real))

/-- Delta-shaped variance-sensitive confidence bound for one fixed comparator's observed
importance-weighted estimator on the generated EXP3 trajectory. -/
theorem sampledObservedComparatorEstimatorDeviation_sum_tail_bernstein_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon : Nat) (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        sampledComparatorEstimatorBernsteinConfidenceRadius
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryObservedComparatorEstimatorDeviationAt
              arms eta gamma loss comparator i sample)} <=
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let epsilon := gamma / (arms.card : Real)
  let budget := max (Real.log (1 / delta)) 0
  let radius :=
    2 * Real.sqrt ((horizon : Real) * budget / epsilon) + budget / epsilon
  have hepsilon : 0 < epsilon := by
    simpa [epsilon] using explorationFloor_pos arms harms gamma hgamma_pos
  have hbudget : 0 <= budget := by
    exact le_max_right _ _
  obtain ⟨tilt, htilt_nonneg, htilt_le, hexponent⟩ :=
    Concentration.exists_tilt_fixedMGF_exponent_le_neg
      (horizon : Real) epsilon budget (by positivity) hepsilon hbudget
  have htail :=
    sampledObservedComparatorEstimatorDeviation_sum_tail_fixedTilt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator hcomparator
        horizon tilt htilt_nonneg (by simpa [epsilon] using htilt_le) radius
  have hexponent' :
      -tilt * radius +
          (horizon : Real) * (tilt ^ 2 / (gamma / (arms.card : Real))) <=
        -budget := by
    simpa [radius, epsilon] using hexponent
  have hreal :
      mu.real {sample | radius <= (Finset.range horizon).sum (fun i =>
          sampledTrajectoryObservedComparatorEstimatorDeviationAt
            arms eta gamma loss comparator i sample)} <=
        Real.exp (-budget) := by
    exact htail.trans (Real.exp_le_exp.mpr hexponent')
  rw [Measure.real] at hreal
  have hennreal :
      mu {sample | radius <= (Finset.range horizon).sum (fun i =>
          sampledTrajectoryObservedComparatorEstimatorDeviationAt
            arms eta gamma loss comparator i sample)} <=
        ENNReal.ofReal (Real.exp (-budget)) := by
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {sample | radius <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryObservedComparatorEstimatorDeviationAt
          arms eta gamma loss comparator i sample)})
      (Real.exp_pos _).le).2 hreal
  have hscale : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hexp_le_delta : Real.exp (-budget) <= delta := by
    by_cases hdelta_le_one : delta <= 1
    · have hone_le_inv : 1 <= 1 / delta := by
        simpa using one_div_le_one_div_of_le hdelta hdelta_le_one
      have hlog_nonneg : 0 <= Real.log (1 / delta) :=
        Real.log_nonneg hone_le_inv
      have hbudget_eq : budget = Real.log (1 / delta) :=
        max_eq_left hlog_nonneg
      rw [hbudget_eq, Real.exp_neg, Real.exp_log hscale]
      field_simp
      exact le_rfl
    · have hone_lt_delta : 1 < delta := lt_of_not_ge hdelta_le_one
      have hinv_le_one : 1 / delta <= 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1)
          hone_lt_delta.le
      have hlog_nonpos : Real.log (1 / delta) <= 0 :=
        Real.log_nonpos hscale.le hinv_le_one
      have hbudget_eq : budget = 0 := max_eq_right hlog_nonpos
      rw [hbudget_eq, neg_zero, Real.exp_zero]
      exact hone_lt_delta.le
  have hfinal := hennreal.trans (ENNReal.ofReal_le_ofReal hexp_le_delta)
  simpa [radius, budget, epsilon,
    sampledComparatorEstimatorBernsteinConfidenceRadius, mu] using hfinal

end Exp3

end BanditRLProof
