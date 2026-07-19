import BanditRLProof.Exp3ComparatorBernstein
import BanditRLProof.Exp3PureConfidence

/-!
# Variance-sensitive pure-Hedge cross-weight concentration

This module replaces the range-squared Hoeffding proxy for the pure-Hedge
cross-weighted estimator by a fixed-tilt second-moment budget.  The sign is
`predictable pure loss - observed cross-weighted loss`, as consumed by the
sampled Hedge regret decomposition.
-/

namespace BanditRLProof
namespace Exp3

open MeasureTheory ProbabilityTheory Real

universe u v w

/-- On the finite support, the cross-weighted estimator has only the sampled
coordinate as a nonzero summand. -/
theorem weightedImportanceWeightedLoss_eq_selected
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob weight loss : Action -> Real)
    (chosen : Action) (hchosen : chosen ∈ arms) :
    weightedImportanceWeightedLoss arms prob weight loss chosen =
      weight chosen * loss chosen / prob chosen := by
  unfold weightedImportanceWeightedLoss
  rw [Finset.sum_eq_single chosen]
  · simp [importanceWeightedLoss]
    ring
  · intro action _haction hne
    simp [importanceWeightedLoss, Ne.symm hne]
  · exact fun hnotmem => (hnotmem hchosen).elim

/-- The centered pure-Hedge cross-weighted estimator has second moment at most
the reciprocal exploration floor. -/
theorem sum_prob_mul_sq_weightedEstimatorMeanMinusRaw_le_inv_floor
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob weight loss : Action -> Real)
    (hprob : FiniteActionDistribution arms prob)
    (hweight : FiniteActionDistribution arms weight)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hfloor : forall action, action ∈ arms -> epsilon <= prob action)
    (hloss : forall action, action ∈ arms -> loss action ∈ Set.Icc (0 : Real) 1) :
    let mean := arms.sum (fun action => weight action * loss action)
    arms.sum (fun chosen =>
        prob chosen *
          (mean - weightedImportanceWeightedLoss arms prob weight loss chosen) ^ 2) <=
      1 / epsilon := by
  dsimp only
  let mean := arms.sum (fun action => weight action * loss action)
  let raw := fun chosen =>
    weightedImportanceWeightedLoss arms prob weight loss chosen
  have hprob_pos (action : Action) (haction : action ∈ arms) :
      0 < prob action := hepsilon.trans_le (hfloor action haction)
  have hfirst : arms.sum (fun chosen => prob chosen * raw chosen) = mean := by
    simpa [raw, mean] using
      sum_prob_mul_weightedImportanceWeightedLoss_eq_weightedLoss
        arms prob weight loss (fun action haction =>
          (hprob_pos action haction).ne')
  have hsecond : arms.sum (fun chosen => prob chosen * (raw chosen) ^ 2) <=
      1 / epsilon := by
    calc
      arms.sum (fun chosen => prob chosen * (raw chosen) ^ 2) <=
          arms.sum (fun chosen => weight chosen / epsilon) := by
        apply Finset.sum_le_sum
        intro chosen hchosen
        have hp := hprob_pos chosen hchosen
        have hq_nonneg := hweight.nonneg chosen hchosen
        have hq_le_one : weight chosen <= 1 := by
          calc
            weight chosen <= arms.sum weight :=
              Finset.single_le_sum hweight.nonneg hchosen
            _ = 1 := hweight.sum_eq_one
        have hl := hloss chosen hchosen
        have hq_sq_le : (weight chosen) ^ 2 <= weight chosen := by
          nlinarith
        have hl_sq_le : (loss chosen) ^ 2 <= 1 := by
          simpa using (sq_le_sq₀ hl.1 zero_le_one).2 hl.2
        have hnum :
            (weight chosen) ^ 2 * (loss chosen) ^ 2 <= weight chosen := by
          calc
            (weight chosen) ^ 2 * (loss chosen) ^ 2 <=
                (weight chosen) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hl_sq_le (sq_nonneg _)
            _ <= weight chosen := by simpa using hq_sq_le
        change prob chosen *
          (weightedImportanceWeightedLoss arms prob weight loss chosen) ^ 2 <= _
        rw [weightedImportanceWeightedLoss_eq_selected
          arms prob weight loss chosen hchosen]
        calc
          prob chosen * (weight chosen * loss chosen / prob chosen) ^ 2 =
              (weight chosen) ^ 2 * (loss chosen) ^ 2 / prob chosen := by
            field_simp
          _ <= weight chosen / prob chosen :=
            div_le_div_of_nonneg_right hnum hp.le
          _ <= weight chosen / epsilon := by
            simpa [div_eq_mul_inv] using
              mul_le_mul_of_nonneg_left
                (one_div_le_one_div_of_le hepsilon (hfloor chosen hchosen))
                hq_nonneg
      _ = 1 / epsilon := by
        rw [← Finset.sum_div, hweight.sum_eq_one, one_div]
  have hcenter (chosen : Action) :
      prob chosen * (mean - raw chosen) ^ 2 =
        (prob chosen * (raw chosen) ^ 2 -
          2 * mean * (prob chosen * raw chosen)) +
          mean ^ 2 * prob chosen := by
    ring
  change arms.sum (fun chosen => prob chosen * (mean - raw chosen) ^ 2) <= _
  simp_rw [hcenter]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hfirst, hprob.sum_eq_one]
  nlinarith [sq_nonneg mean]

/-- Fixed-tilt MGF budget for the sign used by the pure-Hedge regret route. -/
theorem finiteActionWeightedEstimatorMeanMinusRaw_hasMGFUpperBoundAt
    {Action : Type u} [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (prob weight loss : Action -> Real)
    (hprob : FiniteActionDistribution arms prob)
    (hweight : FiniteActionDistribution arms weight)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hfloor : forall action, action ∈ arms -> epsilon <= prob action)
    (hloss : forall action, action ∈ arms -> loss action ∈ Set.Icc (0 : Real) 1)
    (tilt : Real) (htilt_nonneg : 0 <= tilt) (htilt_le : tilt <= epsilon) :
    let mean := arms.sum (fun action => weight action * loss action)
    Concentration.HasMGFUpperBoundAt
      (fun chosen =>
        mean - weightedImportanceWeightedLoss arms prob weight loss chosen)
      tilt (tilt ^ 2 / epsilon) (finiteActionMeasure arms prob) := by
  dsimp only
  let mean := arms.sum (fun action => weight action * loss action)
  let raw := fun chosen =>
    weightedImportanceWeightedLoss arms prob weight loss chosen
  let X := fun chosen => mean - raw chosen
  letI : IsProbabilityMeasure (finiteActionMeasure arms prob) :=
    finiteActionMeasure_isProbabilityMeasure arms prob hprob
  have hprob_pos (action : Action) (haction : action ∈ arms) :
      0 < prob action := hepsilon.trans_le (hfloor action haction)
  obtain ⟨anchor, hanchor⟩ := harms
  have hprob_anchor_le_one : prob anchor <= 1 := by
    calc
      prob anchor <= arms.sum prob := Finset.single_le_sum hprob.nonneg hanchor
      _ = 1 := hprob.sum_eq_one
  have hepsilon_le_one : epsilon <= 1 :=
    (hfloor anchor hanchor).trans hprob_anchor_le_one
  have hinv_nonneg : 0 <= 1 / epsilon := (one_div_pos.mpr hepsilon).le
  have hone_le_inv : 1 <= 1 / epsilon := by
    rw [le_div_iff₀ hepsilon]
    simpa using hepsilon_le_one
  have hmean_nonneg : 0 <= mean := by
    dsimp only [mean]
    exact Finset.sum_nonneg fun action haction =>
      mul_nonneg (hweight.nonneg action haction) (hloss action haction).1
  have hmean_le_one : mean <= 1 := by
    dsimp only [mean]
    calc
      arms.sum (fun action => weight action * loss action) <=
          arms.sum weight := by
        apply Finset.sum_le_sum
        intro action haction
        simpa using mul_le_of_le_one_right
          (hweight.nonneg action haction) (hloss action haction).2
      _ = 1 := hweight.sum_eq_one
  have hX_bound (chosen : Action) (hchosen : chosen ∈ arms) :
      |X chosen| <= 1 / epsilon := by
    have hq_nonneg := hweight.nonneg chosen hchosen
    have hq_le_one : weight chosen <= 1 := by
      calc
        weight chosen <= arms.sum weight :=
          Finset.single_le_sum hweight.nonneg hchosen
        _ = 1 := hweight.sum_eq_one
    have hl := hloss chosen hchosen
    have hraw_nonneg : 0 <= raw chosen := by
      change 0 <= weightedImportanceWeightedLoss arms prob weight loss chosen
      rw [weightedImportanceWeightedLoss_eq_selected
        arms prob weight loss chosen hchosen]
      exact div_nonneg (mul_nonneg hq_nonneg hl.1)
        (hprob.nonneg chosen hchosen)
    have hraw_le : raw chosen <= 1 / epsilon := by
      change weightedImportanceWeightedLoss arms prob weight loss chosen <= 1 / epsilon
      rw [weightedImportanceWeightedLoss_eq_selected
        arms prob weight loss chosen hchosen]
      calc
        weight chosen * loss chosen / prob chosen <= 1 / prob chosen := by
          apply div_le_div_of_nonneg_right _ (hprob_pos chosen hchosen).le
          calc
            weight chosen * loss chosen <= 1 * loss chosen :=
              mul_le_mul_of_nonneg_right hq_le_one hl.1
            _ <= 1 := by simpa using hl.2
        _ <= 1 / epsilon :=
          one_div_le_one_div_of_le hepsilon (hfloor chosen hchosen)
    dsimp only [X]
    rw [abs_le]
    constructor
    · linarith
    · exact (sub_le_self mean hraw_nonneg).trans (hmean_le_one.trans hone_le_inv)
  constructor
  · intro s
    rw [finiteActionMeasure]
    refine integrable_finset_sum_measure.2 fun action haction => ?_
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · rw [ProbabilityTheory.mgf,
      integral_finiteActionMeasure_eq_sum arms prob hprob]
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
        _ = 1 := by field_simp
    calc
      arms.sum (fun chosen => prob chosen * Real.exp (tilt * X chosen)) <=
          arms.sum (fun chosen =>
            prob chosen * (1 + tilt * X chosen + (tilt * X chosen) ^ 2)) := by
        apply Finset.sum_le_sum
        intro chosen hchosen
        exact mul_le_mul_of_nonneg_left (hexp chosen hchosen)
          (hprob.nonneg chosen hchosen)
      _ = 1 + tilt * arms.sum (fun chosen => prob chosen * X chosen) +
          tilt ^ 2 * arms.sum (fun chosen => prob chosen * (X chosen) ^ 2) := by
        have hterm (chosen : Action) :
            prob chosen * (1 + tilt * X chosen + (tilt * X chosen) ^ 2) =
              (prob chosen + tilt * (prob chosen * X chosen)) +
                tilt ^ 2 * (prob chosen * (X chosen) ^ 2) := by ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
          hprob.sum_eq_one]
      _ <= 1 + tilt ^ 2 * (1 / epsilon) := by
        have hmean_zero : arms.sum (fun chosen => prob chosen * X chosen) = 0 := by
          dsimp only [X, raw, mean]
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hprob.sum_eq_one,
            sum_prob_mul_weightedImportanceWeightedLoss_eq_weightedLoss
              arms prob weight loss (fun action haction =>
                (hprob_pos action haction).ne')]
          ring
        rw [hmean_zero, mul_zero, add_zero]
        have hsecond_base :
            arms.sum (fun chosen => prob chosen * (X chosen) ^ 2) <=
              1 / epsilon := by
          simpa only [X, raw, mean] using
            sum_prob_mul_sq_weightedEstimatorMeanMinusRaw_le_inv_floor
              arms prob weight loss hprob hweight epsilon hepsilon hfloor hloss
        have hsecond := mul_le_mul_of_nonneg_left hsecond_base
          (sq_nonneg tilt)
        simpa [add_comm] using add_le_add_left hsecond 1
      _ <= Real.exp (tilt ^ 2 / epsilon) := by
        rw [show tilt ^ 2 * (1 / epsilon) = tilt ^ 2 / epsilon by ring]
        simpa [add_comm] using Real.add_one_le_exp (tilt ^ 2 / epsilon)

/-- An identified finite conditional action law transports the variance-sensitive
fixed-tilt budget for `mean - cross-weighted estimator`. -/
theorem weightedEstimatorMeanMinusRaw_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
    {Omega : Type u} {History : Type v} {Action : Type w}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [mHistory : MeasurableSpace History] [StandardBorelSpace History]
    [mAction : MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (arms : Finset Action) (harms : arms.Nonempty)
    (prob weight loss : History -> Action -> Real)
    (probSource : MeasurableFiniteActionDistribution arms prob)
    (weightSource : MeasurableFiniteActionDistribution arms weight)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (tilt : Real) (htilt_nonneg : 0 <= tilt) (htilt_le : tilt <= epsilon)
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob probSource) :
    Concentration.HasCondMGFUpperBoundAt
      (mHistory.comap history) hhistory.comap_le
      (fun omega =>
        arms.sum (fun candidate =>
            weight (history omega) candidate * loss (history omega) candidate) -
          weightedImportanceWeightedLoss arms (prob (history omega))
            (weight (history omega)) (loss (history omega)) (action omega))
      tilt (tilt ^ 2 / epsilon) mu := by
  let mcond := mHistory.comap history
  let mean := fun h : History => arms.sum (fun candidate =>
    weight h candidate * loss h candidate)
  let X := fun omega =>
    mean (history omega) -
      weightedImportanceWeightedLoss arms (prob (history omega))
        (weight (history omega)) (loss (history omega)) (action omega)
  let target : Omega -> Measure Real := fun omega => Measure.map
    (fun selected =>
      mean (history omega) -
        weightedImportanceWeightedLoss arms (prob (history omega))
          (weight (history omega)) (loss (history omega)) selected)
    (finiteActionMeasure arms (prob (history omega)))
  have hmcond : mcond <= mOmega := hhistory.comap_le
  have hrawPair := measurable_weightedImportanceWeightedLoss_score
    arms prob weight loss probSource weightSource epsilon regularity
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun candidate hcandidate => ?_
    exact (weightSource.measurable_prob candidate hcandidate).mul
      (regularity.measurable_loss candidate hcandidate)
  have hX : @Measurable Omega Real mOmega inferInstance X :=
    (hmean.comp hhistory).sub
      (hrawPair.comp (hhistory.prodMk haction))
  have haction_map :=
    condExpKernel_map_eq_finiteActionMeasure_of_condDistrib_ae_eq
      (mOmega := mOmega) (mCondition := mHistory) (mAction := mAction)
      mu action history haction hhistory arms prob probSource hcond
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
            mean (history omega) -
              weightedImportanceWeightedLoss arms (prob (history omega))
                (weight (history omega)) (loss (history omega)) (action y)))
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
      mean (history omega) -
        weightedImportanceWeightedLoss arms (prob (history omega))
          (weight (history omega)) (loss (history omega)) selected
    have hscore : Measurable score :=
      measurable_const.sub
        (hrawPair.comp (measurable_const.prodMk measurable_id))
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
    weightedEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      (mOmega := mOmega) (mHistory := mHistory) (mAction := mAction)
      mu history hhistory action haction arms prob weight loss probSource
        weightSource epsilon regularity hcond
  change Concentration.Kernel.HasMGFUpperBoundAt X tilt (tilt ^ 2 / epsilon)
    (@condExpKernel Omega mOmega _ mu _ mcond) (mu.trim hmcond)
  refine ⟨?_, ?_⟩
  · intro s
    simpa [X, mean] using hsub.neg.integrable_exp_mul s
  filter_upwards [hkernel_map] with omega hmap
  let actionMu := finiteActionMeasure arms (prob (history omega))
  let score : Action -> Real := fun selected =>
    mean (history omega) -
      weightedImportanceWeightedLoss arms (prob (history omega))
        (weight (history omega)) (loss (history omega)) selected
  have hscore : Measurable score :=
    measurable_const.sub
      (hrawPair.comp (measurable_const.prodMk measurable_id))
  have hfinite : Concentration.HasMGFUpperBoundAt score tilt
      (tilt ^ 2 / epsilon) actionMu := by
    simpa [score, actionMu, mean] using
      finiteActionWeightedEstimatorMeanMinusRaw_hasMGFUpperBoundAt
        arms harms (prob (history omega)) (weight (history omega))
          (loss (history omega)) (probSource.distribution (history omega))
          (weightSource.distribution (history omega)) epsilon
          regularity.epsilon_pos
          (regularity.prob_floor (history omega))
          (regularity.loss_mem_Icc (history omega))
          tilt htilt_nonneg htilt_le
  have htarget : Concentration.HasMGFUpperBoundAt id tilt
      (tilt ^ 2 / epsilon) (target omega) := by
    simpa [target, actionMu, score] using
      (Concentration.HasMGFUpperBoundAt.id_map_iff hscore.aemeasurable).2 hfinite
  rw [← hmap] at htarget
  exact ((Concentration.HasMGFUpperBoundAt.id_map_iff hX.aemeasurable).1 htarget).mgf_le

/-- Latent predictable form of the sign-correct pure-Hedge deviation. -/
noncomputable def sampledTrajectoryPurePredictableMinusWeightedAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample -
    weightedImportanceWeightedLoss arms
      (sampledTrajectoryProbabilityAt arms eta gamma t sample)
      (sampledTrajectoryPureProbabilityAt arms eta gamma t sample)
      (predictableLossAt loss t sample) (sample.2 t).1

theorem sampledPurePredictableMinusWeighted_zero_hasCondMGFUpperBoundAt
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
      (sampledTrajectoryPurePredictableMinusWeightedAt
        arms eta gamma loss 0)
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
  let weight := fun _env : Env =>
    distribution arms eta (fun _t _action => (0 : Real)) 0
  let source := sampledInitialEnvironmentDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one
  let weightSource : MeasurableFiniteActionDistribution arms weight :=
    { distribution := fun _env =>
        { nonneg := fun selected _hselected =>
            distribution_nonneg arms harms eta
              (fun _t _action => (0 : Real)) 0 selected
          sum_eq_one := sum_distribution arms harms eta
            (fun _t _action => (0 : Real)) 0 }
      measurable_prob := fun _selected _hselected => measurable_const }
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
    weightedEstimatorMeanMinusRaw_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
      mu history measurable_fst action (by fun_prop) arms harms prob weight
        loss.initial source weightSource (gamma / (arms.card : Real)) regularity
        tilt htilt_nonneg htilt_le hcond
  convert hmgf using 1

theorem sampledPurePredictableMinusWeighted_succ_hasCondMGFUpperBoundAt
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
      (sampledTrajectoryPurePredictableMinusWeightedAt
        arms eta gamma loss (n + 1))
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
  let weight := fun input : Env × History.FinitePairHistory Action Real n =>
    normalizedHistoryDistribution arms eta
      (sampledHistoryScore arms eta gamma n) input.2
  let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
    loss.successor n input.1 input.2
  let probSource := sampledEnvironmentHistoryDistributionSource
    (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one n
  let localWeightSource := normalizedHistoryDistributionSource arms harms eta
    (sampledHistoryScore arms eta gamma)
    (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma) n
  let weightSource : MeasurableFiniteActionDistribution arms weight :=
    { distribution := fun input => localWeightSource.distribution input.2
      measurable_prob := fun selected hselected =>
        (localWeightSource.measurable_prob selected hselected).comp measurable_snd }
  let regularity := sampledPredictableSuccessorLossRegularity
    arms harms eta gamma hgamma_pos hgamma_le_one loss n
  have hhistory : Measurable history := measurable_fst.prodMk
    ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable action := by fun_prop
  have hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob probSource := by
    simpa [mu, history, action, prob, probSource] using
      (sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss n)
  have hmgf :=
    weightedEstimatorMeanMinusRaw_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
      mu history hhistory action haction arms harms prob weight roundLoss
        probSource weightSource (gamma / (arms.card : Real)) regularity
        tilt htilt_nonneg htilt_le hcond
  convert hmgf using 1
  funext sample
  unfold sampledTrajectoryPurePredictableMinusWeightedAt
    sampledTrajectoryPurePredictableLossAt
  have hweight :
      sampledTrajectoryPureProbabilityAt arms eta gamma (n + 1) sample =
        normalizedHistoryDistribution arms eta
          (sampledHistoryScore arms eta gamma n)
          (Preorder.frestrictLe n sample.2) := by
    funext selected
    exact distribution_sampledTrajectoryObservedLoss_succ
      arms eta gamma sample n selected
  rw [hweight]
  rfl

theorem sampledPurePredictableMinusObserved_zero_hasCondMGFUpperBoundAt
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
      (sampledTrajectoryPurePredictableMinusObservedAt
        arms eta gamma loss 0)
      tilt (tilt ^ 2 / (gamma / (arms.card : Real))) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let mcond := (inferInstance : MeasurableSpace Env).comap history
  letI : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    Prod.instMeasurableSpace
  have hmcond : mcond <= Prod.instMeasurableSpace := measurable_fst.comap_le
  have hpredictable :=
    sampledPurePredictableMinusWeighted_zero_hasCondMGFUpperBoundAt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss
        tilt htilt_nonneg htilt_le
  dsimp only at hpredictable
  have hobserved := sampledTrajectoryPureObservedLossAt_ae_eq_weightedPredictable
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss 0
  have hdeviation :
      sampledTrajectoryPurePredictableMinusWeightedAt
          arms eta gamma loss 0 =ᵐ[mu]
        sampledTrajectoryPurePredictableMinusObservedAt
          arms eta gamma loss 0 := by
    filter_upwards [hobserved] with sample hs
    simp only [sampledTrajectoryPurePredictableMinusWeightedAt,
      sampledTrajectoryPurePredictableMinusObservedAt]
    rw [hs]
  change Concentration.Kernel.HasMGFUpperBoundAt
    (sampledTrajectoryPurePredictableMinusWeightedAt arms eta gamma loss 0)
    tilt (tilt ^ 2 / (gamma / (arms.card : Real)))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hpredictable
  change Concentration.Kernel.HasMGFUpperBoundAt
    (sampledTrajectoryPurePredictableMinusObservedAt arms eta gamma loss 0)
    tilt (tilt ^ 2 / (gamma / (arms.card : Real)))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply hpredictable.congr
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

theorem sampledPurePredictableMinusObserved_succ_hasCondMGFUpperBoundAt
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
      (sampledTrajectoryPurePredictableMinusObservedAt
        arms eta gamma loss (n + 1))
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
    sampledPurePredictableMinusWeighted_succ_hasCondMGFUpperBoundAt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
        tilt htilt_nonneg htilt_le
  dsimp only at hpredictable
  have hobserved := sampledTrajectoryPureObservedLossAt_ae_eq_weightedPredictable
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss (n + 1)
  have hdeviation :
      sampledTrajectoryPurePredictableMinusWeightedAt
          arms eta gamma loss (n + 1) =ᵐ[mu]
        sampledTrajectoryPurePredictableMinusObservedAt
          arms eta gamma loss (n + 1) := by
    filter_upwards [hobserved] with sample hs
    simp only [sampledTrajectoryPurePredictableMinusWeightedAt,
      sampledTrajectoryPurePredictableMinusObservedAt]
    rw [hs]
  change Concentration.Kernel.HasMGFUpperBoundAt
    (sampledTrajectoryPurePredictableMinusWeightedAt
      arms eta gamma loss (n + 1))
    tilt (tilt ^ 2 / (gamma / (arms.card : Real)))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hpredictable
  change Concentration.Kernel.HasMGFUpperBoundAt
    (sampledTrajectoryPurePredictableMinusObservedAt
      arms eta gamma loss (n + 1))
    tilt (tilt ^ 2 / (gamma / (arms.card : Real)))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply hpredictable.congr
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

/-- Variance-sensitive fixed-tilt tail for the pure-Hedge predictable loss minus
its observed cross-weighted estimator. -/
theorem sampledPurePredictableMinusObserved_sum_tail_fixedTilt
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
    (htilt_le : tilt <= gamma / (arms.card : Real)) (threshold : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu.real {sample | threshold <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPurePredictableMinusObservedAt
          arms eta gamma loss i sample)} <=
      Real.exp (-tilt * threshold +
        (horizon : Real) * (tilt ^ 2 / (gamma / (arms.card : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledPurePredictableMinusObservedProcess arms eta gamma loss
  let psiY : Nat -> Real
    | 0 => 0
    | _i + 1 => tilt ^ 2 / (gamma / (arms.card : Real))
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (sampledPurePredictableMinusObservedProcess_stronglyAdapted
        arms harms eta gamma hgamma_pos.le hgamma_le_one loss)
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
          sampledPurePredictableMinusObservedProcess] using
          (sampledPurePredictableMinusObserved_zero_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss
              tilt htilt_nonneg htilt_le)
    | succ n =>
        simpa [mu, F, Y, psiY,
          sampledPurePredictableMinusObservedProcess,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledPurePredictableMinusObserved_succ_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
              tilt htilt_nonneg htilt_le)
  have htail := Concentration.measure_sum_ge_le_of_hasCondMGFUpperBoundAt
    hadapted hzero (horizon + 1) hcond threshold htilt_nonneg
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledPurePredictableMinusObservedProcess_sum_range_succ
      arms eta gamma loss horizon sample
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

/-- Variance-sensitive confidence radius for the pure-Hedge cross-weighted
deviation in the sign consumed by the regret decomposition. -/
noncomputable def sampledPurePredictableMinusObservedBernsteinConfidenceRadius
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  let budget := max (Real.log (1 / delta)) 0
  2 * Real.sqrt
      ((horizon : Real) * budget / (gamma / (arms.card : Real))) +
    budget / (gamma / (arms.card : Real))

/-- Delta-shaped variance-sensitive confidence bound for the pure-Hedge
predictable loss minus its observed cross-weighted estimator. -/
theorem sampledPurePredictableMinusObserved_sum_tail_bernstein_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        sampledPurePredictableMinusObservedBernsteinConfidenceRadius
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPurePredictableLossAt
                arms eta gamma loss i sample -
              sampledTrajectoryPureObservedLossAt arms eta gamma i sample)} <=
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
  have hbudget : 0 <= budget := le_max_right _ _
  obtain ⟨tilt, htilt_nonneg, htilt_le, hexponent⟩ :=
    Concentration.exists_tilt_fixedMGF_exponent_le_neg
      (horizon : Real) epsilon budget (by positivity) hepsilon hbudget
  have htail :=
    sampledPurePredictableMinusObserved_sum_tail_fixedTilt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss
        horizon tilt htilt_nonneg (by simpa [epsilon] using htilt_le) radius
  have hexponent' :
      -tilt * radius +
          (horizon : Real) * (tilt ^ 2 / (gamma / (arms.card : Real))) <=
        -budget := by
    simpa [radius, epsilon] using hexponent
  have hreal :
      mu.real {sample | radius <= (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPurePredictableMinusObservedAt
            arms eta gamma loss i sample)} <=
        Real.exp (-budget) := by
    exact htail.trans (Real.exp_le_exp.mpr hexponent')
  rw [Measure.real] at hreal
  have hennreal :
      mu {sample | radius <= (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPurePredictableMinusObservedAt
            arms eta gamma loss i sample)} <=
        ENNReal.ofReal (Real.exp (-budget)) := by
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {sample | radius <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPurePredictableMinusObservedAt
          arms eta gamma loss i sample)})
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
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledTrajectoryPurePredictableMinusObservedAt, mu] using hfinal

end Exp3
end BanditRLProof
