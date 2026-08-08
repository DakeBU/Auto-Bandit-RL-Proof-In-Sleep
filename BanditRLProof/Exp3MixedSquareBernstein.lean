import BanditRLProof.Exp3ComparatorBernstein
import BanditRLProof.Exp3MixedSquareConfidence
import BanditRLProof.ConcentrationQuadraticFixedMGF

/-!
# Variance-sensitive mixed-square EXP3 concentration

The interval-sub-Gaussian route treats the mixed estimator square as an
arbitrary variable in `[0, 1 / epsilon]`, producing a variance proxy quadratic
in the reciprocal exploration floor.  Here the exact finite sampling law gives
a centered second moment at most `K / epsilon`.  A fixed-tilt conditional MGF
argument then yields a generated finite-horizon Bernstein tail whose square-root
term is linear, rather than quadratic, in that reciprocal floor.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Real

namespace Exp3

universe u v

/-- Exact uncentered second moment of one mixed importance-weighted square. -/
theorem sum_prob_mul_sq_mixedSquaredImportanceWeightedLoss_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hprob : forall action, action ∈ arms -> prob action ≠ 0) :
    arms.sum (fun chosen =>
        prob chosen *
          (mixedSquaredImportanceWeightedLoss arms prob loss chosen) ^ 2) =
      arms.sum (fun action => (loss action) ^ 4 / prob action) := by
  apply Finset.sum_congr rfl
  intro chosen hchosen
  rw [mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div
    arms prob loss chosen hchosen (hprob chosen hchosen)]
  field_simp

/-- The centered mixed-square score has second moment at most `K / epsilon`
under a uniform probability floor. -/
theorem sum_prob_mul_sq_mixedSquaredEstimatorDeviation_le_card_div_floor
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hdist : FiniteActionDistribution arms prob)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hfloor : forall action, action ∈ arms -> epsilon <= prob action)
    (hloss : forall action, action ∈ arms ->
      loss action ∈ Set.Icc (0 : Real) 1) :
    arms.sum (fun chosen =>
        prob chosen *
          (mixedSquaredImportanceWeightedLoss arms prob loss chosen -
            arms.sum (fun action => (loss action) ^ 2)) ^ 2) <=
      (arms.card : Real) / epsilon := by
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
  have hfourth (action : Action) (haction : action ∈ arms) :
      (loss action) ^ 4 <= 1 := by
    have hsq : (loss action) ^ 2 <= 1 := by
      simpa using (sq_le_sq₀ (hloss action haction).1 zero_le_one).2
        (hloss action haction).2
    have hsq_nonneg : 0 <= (loss action) ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg ((loss action) ^ 2)]
  have hterm (action : Action) (haction : action ∈ arms) :
      (loss action) ^ 4 / prob action <= 1 / epsilon := by
    calc
      (loss action) ^ 4 / prob action <= 1 / prob action :=
        div_le_div_of_nonneg_right (hfourth action haction)
          (hprob_pos action haction).le
      _ <= 1 / epsilon := one_div_le_one_div_of_le hepsilon
        (hfloor action haction)
  have hsecond_le :
      arms.sum (fun action => (loss action) ^ 4 / prob action) <=
        (arms.card : Real) / epsilon := by
    calc
      arms.sum (fun action => (loss action) ^ 4 / prob action) <=
          arms.sum (fun _action => 1 / epsilon) :=
        Finset.sum_le_sum fun action haction => hterm action haction
      _ = (arms.card : Real) / epsilon := by simp [div_eq_mul_inv]
  change arms.sum (fun chosen => prob chosen * (raw chosen - mean) ^ 2) <= _
  rw [hvariance]
  nlinarith [sq_nonneg mean]

/-- Fixed-tilt MGF budget for a centered mixed estimator square under a finite
sampling law. The quadratic coefficient is `K / epsilon`, while the admissible
tilt is controlled by the sharper range cap `epsilon`. -/
theorem finiteActionMixedSquaredEstimator_hasMGFUpperBoundAt
    {Action : Type u} [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hdist : FiniteActionDistribution arms prob)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hfloor : forall action, action ∈ arms -> epsilon <= prob action)
    (hloss : forall action, action ∈ arms ->
      loss action ∈ Set.Icc (0 : Real) 1)
    (tilt : Real) (htilt_nonneg : 0 <= tilt) (htilt_le : tilt <= epsilon) :
    Concentration.HasMGFUpperBoundAt
      (fun chosen =>
        mixedSquaredImportanceWeightedLoss arms prob loss chosen -
          arms.sum (fun action => (loss action) ^ 2))
      tilt (tilt ^ 2 * ((arms.card : Real) / epsilon))
      (finiteActionMeasure arms prob) := by
  let raw := fun chosen =>
    mixedSquaredImportanceWeightedLoss arms prob loss chosen
  let mean := arms.sum (fun action => (loss action) ^ 2)
  let X := fun chosen => raw chosen - mean
  letI : IsProbabilityMeasure (finiteActionMeasure arms prob) :=
    finiteActionMeasure_isProbabilityMeasure arms prob hdist
  have hprob_pos (action : Action) (haction : action ∈ arms) :
      0 < prob action := hepsilon.trans_le (hfloor action haction)
  have hinv_nonneg : 0 <= 1 / epsilon := (one_div_pos.mpr hepsilon).le
  have hmean_nonneg : 0 <= mean := by
    exact Finset.sum_nonneg fun action _haction => sq_nonneg (loss action)
  have hmean_le_card : mean <= (arms.card : Real) := by
    dsimp only [mean]
    calc
      arms.sum (fun action => (loss action) ^ 2) <=
          arms.sum (fun _action => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro action haction
        simpa using (sq_le_sq₀ (hloss action haction).1 zero_le_one).2
          (hloss action haction).2
      _ = (arms.card : Real) := by simp
  have hcard_le_inv : (arms.card : Real) <= 1 / epsilon := by
    rw [le_div_iff₀ hepsilon]
    have hsum : arms.sum (fun _action => epsilon) <= arms.sum prob := by
      exact Finset.sum_le_sum fun action haction => hfloor action haction
    simpa [hdist.sum_eq_one, mul_comm] using hsum
  have hX_bound (chosen : Action) (hchosen : chosen ∈ arms) :
      |X chosen| <= 1 / epsilon := by
    have hraw_nonneg : 0 <= raw chosen := by
      unfold raw mixedSquaredImportanceWeightedLoss
      exact Finset.sum_nonneg fun action haction =>
        mul_nonneg (hdist.nonneg action haction) (sq_nonneg _)
    have hraw_le : raw chosen <= 1 / epsilon := by
      dsimp only [raw]
      rw [mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div
        arms prob loss chosen hchosen (hprob_pos chosen hchosen).ne']
      have hsq : (loss chosen) ^ 2 <= 1 := by
        simpa using (sq_le_sq₀ (hloss chosen hchosen).1 zero_le_one).2
          (hloss chosen hchosen).2
      calc
        (loss chosen) ^ 2 / prob chosen <= 1 / prob chosen :=
          div_le_div_of_nonneg_right hsq (hprob_pos chosen hchosen).le
        _ <= 1 / epsilon := one_div_le_one_div_of_le hepsilon
          (hfloor chosen hchosen)
    dsimp only [X]
    rw [abs_le]
    constructor
    · nlinarith [hmean_le_card, hcard_le_inv]
    · nlinarith
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
          (hdist.nonneg chosen hchosen)
      _ = 1 + tilt * arms.sum (fun chosen => prob chosen * X chosen) +
          tilt ^ 2 * arms.sum (fun chosen => prob chosen * (X chosen) ^ 2) := by
        have hterm (chosen : Action) :
            prob chosen * (1 + tilt * X chosen + (tilt * X chosen) ^ 2) =
              (prob chosen + tilt * (prob chosen * X chosen)) +
                tilt ^ 2 * (prob chosen * (X chosen) ^ 2) := by ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hdist.sum_eq_one]
      _ <= 1 + tilt ^ 2 * ((arms.card : Real) / epsilon) := by
        have hmean : arms.sum (fun chosen => prob chosen * X chosen) = 0 := by
          dsimp only [X]
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib,
            sum_prob_mul_mixedSquaredImportanceWeightedLoss_eq_sum_loss_sq
              arms prob loss
                (fun action haction => (hprob_pos action haction).ne'),
            ← Finset.sum_mul, hdist.sum_eq_one]
          simp [mean]
        rw [hmean, mul_zero, add_zero]
        have hsecond := mul_le_mul_of_nonneg_left
          (by
            simpa [X, mean] using
              sum_prob_mul_sq_mixedSquaredEstimatorDeviation_le_card_div_floor
                arms prob loss hdist epsilon hepsilon hfloor hloss)
          (sq_nonneg tilt)
        simpa [X, add_comm] using add_le_add_left hsecond 1
      _ <= Real.exp (tilt ^ 2 * ((arms.card : Real) / epsilon)) := by
        simpa [add_comm] using
          Real.add_one_le_exp (tilt ^ 2 * ((arms.card : Real) / epsilon))

/-- A finite conditional action law supplies the fixed-tilt mixed-square MGF
budget with second-moment coefficient `K / epsilon`. -/
theorem mixedSquaredEstimator_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
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
      (mHistory.comap history)
      hhistory.comap_le
      (fun omega =>
        mixedSquaredImportanceWeightedLoss arms (prob (history omega))
            (loss (history omega)) (action omega) -
          arms.sum (fun candidate => (loss (history omega) candidate) ^ 2))
      tilt (tilt ^ 2 * ((arms.card : Real) / epsilon)) mu := by
  let mcond := mHistory.comap history
  let mean := fun h : History =>
    arms.sum (fun candidate => (loss h candidate) ^ 2)
  let X := fun omega =>
    mixedSquaredImportanceWeightedLoss arms (prob (history omega))
        (loss (history omega)) (action omega) - mean (history omega)
  let target : Omega -> Measure Real := fun omega => Measure.map
    (fun selected =>
      mixedSquaredImportanceWeightedLoss arms (prob (history omega))
          (loss (history omega)) selected - mean (history omega))
    (finiteActionMeasure arms (prob (history omega)))
  have hmcond : mcond <= mOmega := hhistory.comap_le
  have hrawPair := measurable_mixedSquaredImportanceWeightedLoss_score
    arms prob loss source epsilon regularity
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun candidate hcandidate => ?_
    exact (regularity.measurable_loss candidate hcandidate).pow_const 2
  have hX : @Measurable Omega Real mOmega inferInstance X :=
    (hrawPair.comp (hhistory.prodMk haction)).sub (hmean.comp hhistory)
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
            mixedSquaredImportanceWeightedLoss arms (prob (history omega))
                (loss (history omega)) (action y) - mean (history omega)))
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
      mixedSquaredImportanceWeightedLoss arms (prob (history omega))
          (loss (history omega)) selected - mean (history omega)
    have hscore : Measurable score :=
      (hrawPair.comp (measurable_const.prodMk measurable_id)).sub measurable_const
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
    mixedSquaredEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      (mOmega := mOmega) (mHistory := mHistory) (mAction := mAction)
      mu history hhistory action haction arms prob loss source epsilon regularity hcond
  change Concentration.Kernel.HasMGFUpperBoundAt X tilt
    (tilt ^ 2 * ((arms.card : Real) / epsilon))
    (@condExpKernel Omega mOmega _ mu _ mcond) (mu.trim hmcond)
  refine ⟨?_, ?_⟩
  · intro s
    rw [@ProbabilityTheory.condExpKernel_comp_trim
      Omega mcond mOmega _ mu _ hmcond]
    simpa [X] using hsub.integrable_exp_mul s
  filter_upwards [hkernel_map] with omega hmap
  let actionMu := finiteActionMeasure arms (prob (history omega))
  let score : Action -> Real := fun selected =>
    mixedSquaredImportanceWeightedLoss arms (prob (history omega))
        (loss (history omega)) selected - mean (history omega)
  have hscore : Measurable score :=
    (hrawPair.comp (measurable_const.prodMk measurable_id)).sub measurable_const
  have hfinite : Concentration.HasMGFUpperBoundAt score tilt
      (tilt ^ 2 * ((arms.card : Real) / epsilon)) actionMu := by
    simpa [score, actionMu, mean] using
      finiteActionMixedSquaredEstimator_hasMGFUpperBoundAt
        arms (prob (history omega)) (loss (history omega))
          (source.distribution (history omega)) epsilon regularity.epsilon_pos
          (regularity.prob_floor (history omega))
          (regularity.loss_mem_Icc (history omega))
          tilt htilt_nonneg htilt_le
  have htarget : Concentration.HasMGFUpperBoundAt id tilt
      (tilt ^ 2 * ((arms.card : Real) / epsilon)) (target omega) := by
    simpa [target, actionMu, score] using
      (Concentration.HasMGFUpperBoundAt.id_map_iff hscore.aemeasurable).2 hfinite
  rw [← hmap] at htarget
  exact ((Concentration.HasMGFUpperBoundAt.id_map_iff hX.aemeasurable).1 htarget).mgf_le

theorem sampledPredictableMixedSquaredDeviation_zero_hasCondMGFUpperBoundAt
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
      (sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss 0)
      tilt (tilt ^ 2 *
        ((arms.card : Real) / (gamma / (arms.card : Real)))) mu := by
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
    mixedSquaredEstimator_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
      mu history measurable_fst action (by fun_prop) arms prob loss.initial
        source (gamma / (arms.card : Real)) regularity
        tilt htilt_nonneg htilt_le hcond
  simpa [mu, history, action, prob,
    sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

theorem sampledPredictableMixedSquaredDeviation_succ_hasCondMGFUpperBoundAt
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
      (sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss (n + 1))
      tilt (tilt ^ 2 *
        ((arms.card : Real) / (gamma / (arms.card : Real)))) mu := by
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
    mixedSquaredEstimator_hasCondMGFUpperBoundAt_of_condDistrib_ae_eq_finiteActionKernel
      mu history hhistory action haction arms prob roundLoss source
        (gamma / (arms.card : Real)) regularity
        tilt htilt_nonneg htilt_le hcond
  simpa [mu, history, action, prob, roundLoss,
    sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

/-- Fixed-tilt Bernstein tail for the centered predictable mixed-square process
on the generated EXP3 trajectory. -/
theorem sampledPredictableMixedSquaredDeviation_sum_tail_fixedTilt
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
    mu {sample | threshold <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredDeviationAt
          arms eta gamma loss i sample)} <=
      ENNReal.ofReal (Real.exp (-tilt * threshold +
        (horizon : Real) *
          (tilt ^ 2 * ((arms.card : Real) /
            (gamma / (arms.card : Real)))))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledPredictableMixedSquaredDeviationProcess arms eta gamma loss
  let psiY : Nat -> Real
    | 0 => 0
    | _i + 1 => tilt ^ 2 *
        ((arms.card : Real) / (gamma / (arms.card : Real)))
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (sampledPredictableMixedSquaredDeviationProcess_stronglyAdapted
        arms harms eta gamma hgamma_pos hgamma_le_one loss)
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
          sampledPredictableMixedSquaredDeviationProcess] using
          (sampledPredictableMixedSquaredDeviation_zero_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss
              tilt htilt_nonneg htilt_le)
    | succ n =>
        simpa [mu, F, Y, psiY,
          sampledPredictableMixedSquaredDeviationProcess,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledPredictableMixedSquaredDeviation_succ_hasCondMGFUpperBoundAt
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
              tilt htilt_nonneg htilt_le)
  have hreal := Concentration.measure_sum_ge_le_of_hasCondMGFUpperBoundAt
    hadapted hzero (horizon + 1) hcond threshold htilt_nonneg
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledPredictableMixedSquaredDeviationProcess_sum_range_succ
      arms eta gamma loss horizon sample
  have hbudget_aux (n : Nat) : (Finset.range (n + 1)).sum psiY =
      (n : Real) * (tilt ^ 2 *
        ((arms.card : Real) / (gamma / (arms.card : Real)))) := by
    induction n with
    | zero => simp [psiY]
    | succ n ih =>
        rw [show Nat.succ n + 1 = (n + 1) + 1 by omega,
          Finset.sum_range_succ, ih]
        push_cast
        ring
  have hbudget := hbudget_aux horizon
  have hreal' :
      mu.real {sample | threshold <= (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss i sample)} <=
        Real.exp (-tilt * threshold +
          (horizon : Real) * (tilt ^ 2 *
            ((arms.card : Real) / (gamma / (arms.card : Real))))) := by
    simpa [Y, hprocess, hbudget] using hreal
  rw [Measure.real] at hreal'
  exact (ENNReal.le_ofReal_iff_toReal_le
    (measure_ne_top mu {sample | threshold <= (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss i sample)})
    (Real.exp_pos _).le).2 hreal'

/-- Fixed-tilt Bernstein tail for the observed, uncentered mixed estimator-square
sum on the generated trajectory. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_bernstein_fixedTilt
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
    mu {sample |
        (arms.card : Real) * (horizon : Real) + threshold <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample} <=
      ENNReal.ofReal (Real.exp (-tilt * threshold +
        (horizon : Real) *
          (tilt ^ 2 * ((arms.card : Real) /
            (gamma / (arms.card : Real)))))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  have htail := sampledPredictableMixedSquaredDeviation_sum_tail_fixedTilt
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
      tilt htilt_nonneg htilt_le threshold
  have heq := sampledObservedMixedSquaredSum_eq_predictable_ae
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss horizon
  have hsubset : ∀ᵐ sample ∂mu,
      (arms.card : Real) * (horizon : Real) + threshold <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample ->
        threshold <= (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss i sample) := by
    filter_upwards [heq] with sample hobs
    intro hsample
    have hmean := sampledPredictableLossSquaredSum_le_card_mul
      arms loss horizon sample
    have hcentered := sampledPredictableMixedSquaredDeviation_sum_eq
      arms eta gamma loss horizon sample
    rw [hobs] at hsample
    linarith
  exact (measure_mono_ae hsubset).trans (by simpa [mu] using htail)

/-- Variance coefficient in the mixed-square fixed-tilt MGF budget. -/
noncomputable def sampledMixedSquaredBernsteinVarianceCoefficient
    {Action : Type v} (arms : Finset Action) (gamma : Real) : Real :=
  (arms.card : Real) / (gamma / (arms.card : Real))

/-- Optimized Bernstein radius for the observed mixed estimator-square sum. -/
noncomputable def sampledMixedSquaredBernsteinConfidenceRadius
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  let epsilon := gamma / (arms.card : Real)
  let variance := sampledMixedSquaredBernsteinVarianceCoefficient arms gamma
  let budget := max (Real.log (1 / delta)) 0
  2 * Real.sqrt ((horizon : Real) * variance * budget) + budget / epsilon

/-- Delta-shaped variance-sensitive confidence bound for the generated observed
mixed estimator-square sum. The square-root term uses the second-moment
coefficient `K / epsilon`, while the linear correction uses the reciprocal
range cap `1 / epsilon`. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_bernstein_delta
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
        (arms.card : Real) * (horizon : Real) +
            sampledMixedSquaredBernsteinConfidenceRadius
              arms gamma horizon delta <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample} <=
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let epsilon := gamma / (arms.card : Real)
  let variance := (arms.card : Real) / epsilon
  let budget := max (Real.log (1 / delta)) 0
  let radius := 2 * Real.sqrt ((horizon : Real) * variance * budget) +
    budget / epsilon
  have hepsilon : 0 < epsilon := by
    simpa [epsilon] using explorationFloor_pos arms harms gamma hgamma_pos
  have hcard_pos : 0 < (arms.card : Real) := by
    exact_mod_cast harms.card_pos
  have hvariance : 0 < variance := by
    exact div_pos hcard_pos hepsilon
  have hbudget : 0 <= budget := le_max_right _ _
  obtain ⟨tilt, htilt_nonneg, htilt_le, hexponent⟩ :=
    Concentration.exists_tilt_quadratic_fixedMGF_exponent_le_neg
      (horizon : Real) variance epsilon budget (by positivity)
        hvariance hepsilon hbudget
  have htail :=
    sampledPredictableObservedMixedSquared_sum_tail_bernstein_fixedTilt
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
        tilt htilt_nonneg (by simpa [epsilon] using htilt_le) radius
  have hexponent' :
      -tilt * radius +
          (horizon : Real) *
            (tilt ^ 2 * ((arms.card : Real) /
              (gamma / (arms.card : Real)))) <=
        -budget := by
    simpa [radius, variance, epsilon, mul_assoc] using hexponent
  have hbudget_tail :
      mu {sample |
          (arms.card : Real) * (horizon : Real) + radius <=
            sampledObservedMixedSquaredSum arms eta gamma horizon sample} <=
        ENNReal.ofReal (Real.exp (-budget)) := by
    exact htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent'))
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
  have hfinal := hbudget_tail.trans (ENNReal.ofReal_le_ofReal hexp_le_delta)
  simpa [radius, budget, variance, epsilon,
    sampledMixedSquaredBernsteinConfidenceRadius,
    sampledMixedSquaredBernsteinVarianceCoefficient, mu] using hfinal

end Exp3

end BanditRLProof
