import BanditRLProof.Exp3ComparatorConfidence

/-!
# Pure-Hedge cross-weighted EXP3 confidence

This module proves finite-horizon confidence bounds for the pure-Hedge weighted
importance estimator, including the predictable-minus-observed direction needed
by the regret decomposition.  It first identifies the conditional
mean under the exploration action law, transports the latent predictable score
to the observed trajectory score, proves adaptedness, and applies the local
conditional sub-Gaussian finite-sum tail theorem.

The bounded-range proxy is Hoeffding's interval proxy for `[0, K / gamma]`.
This closes the pure-q cross-weight concentration leaf; it does not control the
random estimator-square term in the sampled Hedge inequality.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v w

theorem weightedEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
    {Omega : Type u} {History : Type v} {Action : Type w}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [mHistory : MeasurableSpace History] [StandardBorelSpace History]
    [mAction : MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (arms : Finset Action) (prob weight loss : History -> Action -> Real)
    (probSource : MeasurableFiniteActionDistribution arms prob)
    (weightSource : MeasurableFiniteActionDistribution arms weight)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob probSource) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (mHistory.comap history) hhistory.comap_le
      (fun omega =>
        weightedImportanceWeightedLoss arms (prob (history omega))
            (weight (history omega)) (loss (history omega)) (action omega) -
          arms.sum (fun candidate =>
            weight (history omega) candidate * loss (history omega) candidate))
      (Concentration.intervalVarianceProxy 0 (1 / epsilon)) mu := by
  let mcond := mHistory.comap history
  let mean := fun h : History => arms.sum (fun candidate =>
    weight h candidate * loss h candidate)
  let X := fun omega =>
    weightedImportanceWeightedLoss arms (prob (history omega))
        (weight (history omega)) (loss (history omega)) (action omega) -
      mean (history omega)
  let target : Omega -> Measure Real := fun omega => Measure.map
    (fun selected =>
      weightedImportanceWeightedLoss arms (prob (history omega))
          (weight (history omega)) (loss (history omega)) selected -
        mean (history omega))
    (finiteActionMeasure arms (prob (history omega)))
  have hmcond : mcond <= mOmega := hhistory.comap_le
  have hrawPair := measurable_weightedImportanceWeightedLoss_score
    arms prob weight loss probSource weightSource epsilon regularity
  have hmean : Measurable mean := by
    refine Finset.measurable_sum arms fun candidate hcandidate => ?_
    exact (weightSource.measurable_prob candidate hcandidate).mul
      (regularity.measurable_loss candidate hcandidate)
  have hX : @Measurable Omega Real mOmega inferInstance X :=
    (hrawPair.comp (hhistory.prodMk haction)).sub (hmean.comp hhistory)
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
            weightedImportanceWeightedLoss arms (prob (history omega))
                (weight (history omega)) (loss (history omega)) (action y) -
              mean (history omega)))
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
      weightedImportanceWeightedLoss arms (prob (history omega))
          (weight (history omega)) (loss (history omega)) selected -
        mean (history omega)
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
  have htarget_subG :
      Filter.Eventually
        (fun omega => HasSubgaussianMGF (fun z : Real => z)
          (Concentration.intervalVarianceProxy 0 (1 / epsilon)) (target omega))
        (ae (mu.trim hmcond)) := by
    filter_upwards [] with omega
    let actionMu := finiteActionMeasure arms (prob (history omega))
    let raw : Action -> Real := fun selected =>
      weightedImportanceWeightedLoss arms (prob (history omega))
        (weight (history omega)) (loss (history omega)) selected
    let score : Action -> Real := fun selected => raw selected - mean (history omega)
    letI : IsProbabilityMeasure actionMu :=
      finiteActionMeasure_isProbabilityMeasure arms (prob (history omega))
        (probSource.distribution (history omega))
    have hraw : Measurable raw :=
      hrawPair.comp (measurable_const.prodMk measurable_id)
    have hbound : Filter.Eventually
        (fun selected => raw selected ∈ Set.Icc (0 : Real) (1 / epsilon))
        (ae actionMu) := Filter.Eventually.of_forall fun selected => by
      have hnonneg : 0 <= raw selected := by
        unfold raw weightedImportanceWeightedLoss
        exact Finset.sum_nonneg fun candidate hcandidate =>
          mul_nonneg
            ((weightSource.distribution (history omega)).nonneg candidate hcandidate)
            (importanceWeightedLoss_nonneg
              ((probSource.distribution (history omega)).nonneg candidate hcandidate)
              (regularity.loss_mem_Icc (history omega) candidate hcandidate).1)
      refine ⟨hnonneg, ?_⟩
      change weightedImportanceWeightedLoss arms (prob (history omega))
        (weight (history omega)) (loss (history omega)) selected <= 1 / epsilon
      have hnonneg' : 0 <= weightedImportanceWeightedLoss arms
          (prob (history omega)) (weight (history omega))
          (loss (history omega)) selected := by simpa [raw] using hnonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg'] using
        (norm_weightedImportanceWeightedLoss_score_le_inv_floor
          arms prob weight loss weightSource epsilon regularity
            (history omega) selected)
    have hmean_eq : integral actionMu raw = mean (history omega) := by
      rw [integral_finiteActionMeasure_eq_sum arms (prob (history omega))
        (probSource.distribution (history omega)) raw]
      simpa [raw, mean] using
        (sum_prob_mul_weightedImportanceWeightedLoss_eq_weightedLoss
          arms (prob (history omega)) (weight (history omega))
            (loss (history omega))
            (fun candidate hcandidate =>
              (regularity.prob_pos (history omega) candidate hcandidate).ne'))
    have hsub : HasSubgaussianMGF score
        (Concentration.intervalVarianceProxy 0 (1 / epsilon)) actionMu := by
      simpa [score, raw] using
        (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
          actionMu hraw.aemeasurable hbound hmean_eq)
    have hscore : Measurable score := hraw.sub measurable_const
    apply (HasSubgaussianMGF.id_map_iff hscore.aemeasurable).2
    simpa [target, actionMu, score, raw] using hsub
  exact ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
    (mOmega := mOmega)
    mu mcond hmcond X (Concentration.intervalVarianceProxy 0 (1 / epsilon))
      hX target hkernel_map htarget_subG

noncomputable def sampledTrajectoryWeightedPurePredictableDeviationAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  weightedImportanceWeightedLoss arms
      (sampledTrajectoryProbabilityAt arms eta gamma t sample)
      (sampledTrajectoryPureProbabilityAt arms eta gamma t sample)
      (predictableLossAt loss t sample) (sample.2 t).1 -
    sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample

noncomputable def sampledTrajectoryPureObservedDeviationAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  sampledTrajectoryPureObservedLossAt arms eta gamma t sample -
    sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample

theorem sampledWeightedPurePredictableDeviation_zero_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectoryWeightedPurePredictableDeviationAt
        arms eta gamma loss 0)
      (sampledComparatorEstimatorVarianceProxy arms gamma) mu := by
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
    weightedEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      mu history measurable_fst action (by fun_prop) arms prob weight loss.initial
        source weightSource (gamma / (arms.card : Real)) regularity hcond
  convert hmgf using 1

theorem sampledWeightedPurePredictableDeviation_succ_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (sampledTrajectoryWeightedPurePredictableDeviationAt
        arms eta gamma loss (n + 1))
      (sampledComparatorEstimatorVarianceProxy arms gamma) mu := by
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
    weightedEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      mu history hhistory action haction arms prob weight roundLoss probSource
        weightSource (gamma / (arms.card : Real)) regularity hcond
  convert hmgf using 1
  funext sample
  unfold sampledTrajectoryWeightedPurePredictableDeviationAt
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

theorem sampledPureObservedDeviation_zero_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectoryPureObservedDeviationAt arms eta gamma loss 0)
      (sampledComparatorEstimatorVarianceProxy arms gamma) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  have hhistory : Measurable history := measurable_fst
  let mcond := (inferInstance : MeasurableSpace Env).comap history
  letI : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    Prod.instMeasurableSpace
  have hmcond : mcond <= Prod.instMeasurableSpace := hhistory.comap_le
  have hpredictable := sampledWeightedPurePredictableDeviation_zero_hasCondSubgaussianMGF
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss
  dsimp only at hpredictable
  have hobserved := sampledTrajectoryPureObservedLossAt_ae_eq_weightedPredictable
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss 0
  have hdeviation :
      sampledTrajectoryWeightedPurePredictableDeviationAt
          arms eta gamma loss 0 =ᵐ[mu]
        sampledTrajectoryPureObservedDeviationAt arms eta gamma loss 0 := by
    filter_upwards [hobserved] with sample hs
    simp only [sampledTrajectoryWeightedPurePredictableDeviationAt,
      sampledTrajectoryPureObservedDeviationAt]
    rw [hs]
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryWeightedPurePredictableDeviationAt arms eta gamma loss 0)
    (sampledComparatorEstimatorVarianceProxy arms gamma)
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hpredictable
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryPureObservedDeviationAt arms eta gamma loss 0)
    (sampledComparatorEstimatorVarianceProxy arms gamma)
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply (ProbabilityTheory.Kernel.HasSubgaussianMGF_congr ?_).1 hpredictable
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

theorem sampledPureObservedDeviation_succ_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (sampledTrajectoryPureObservedDeviationAt arms eta gamma loss (n + 1))
      (sampledComparatorEstimatorVarianceProxy arms gamma) mu := by
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
  have hpredictable := sampledWeightedPurePredictableDeviation_succ_hasCondSubgaussianMGF
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
  dsimp only at hpredictable
  have hobserved := sampledTrajectoryPureObservedLossAt_ae_eq_weightedPredictable
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss (n + 1)
  have hdeviation :
      sampledTrajectoryWeightedPurePredictableDeviationAt
          arms eta gamma loss (n + 1) =ᵐ[mu]
        sampledTrajectoryPureObservedDeviationAt
          arms eta gamma loss (n + 1) := by
    filter_upwards [hobserved] with sample hs
    simp only [sampledTrajectoryWeightedPurePredictableDeviationAt,
      sampledTrajectoryPureObservedDeviationAt]
    rw [hs]
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryWeightedPurePredictableDeviationAt
      arms eta gamma loss (n + 1))
    (sampledComparatorEstimatorVarianceProxy arms gamma)
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hpredictable
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryPureObservedDeviationAt arms eta gamma loss (n + 1))
    (sampledComparatorEstimatorVarianceProxy arms gamma)
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply (ProbabilityTheory.Kernel.HasSubgaussianMGF_congr ?_).1 hpredictable
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

noncomputable def sampledPureObservedDeviationProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Real
  | 0, _sample => 0
  | i + 1, sample =>
      sampledTrajectoryPureObservedDeviationAt arms eta gamma loss i sample

theorem sampledPureObservedDeviationProcess_stronglyAdapted
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    StronglyAdapted
      (sampledPredictableDeviationFiltration Env Action)
      (sampledPureObservedDeviationProcess arms eta gamma loss) := by
  intro t
  cases t with
  | zero =>
      simpa [sampledPureObservedDeviationProcess] using
        (stronglyMeasurable_const :
          StronglyMeasurable[
            sampledPredictableDeviationFiltration Env Action 0]
              (fun _ : Env × ((k : Nat) -> Action × Real) => (0 : Real)))
  | succ i =>
      cases i with
      | zero =>
          let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.1, Preorder.frestrictLe 0 sample.2)
          let zeroIndex : Finset.Iic 0 := ⟨0, by simp⟩
          let selectedAction := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            (input.2 zeroIndex).1
          let selectedReward := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            (input.2 zeroIndex).2
          let prob := fun _input :
              Env × History.FinitePairHistory Action Real 0 =>
            initialExploredDistribution arms eta gamma
          let weight := fun _input :
              Env × History.FinitePairHistory Action Real 0 =>
            distribution arms eta (fun _ _ => 0) 0
          let trueLoss := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            arms.sum (fun candidate =>
              weight input candidate * loss.initial input.1 candidate)
          let score := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            arms.sum (fun candidate =>
                weight input candidate *
                  importanceWeightedLoss (prob input)
                    (fun _ => selectedReward input) (selectedAction input) candidate) -
              trueLoss input
          have hhistory :
              @Measurable (Env × ((k : Nat) -> Action × Real))
                (Env × History.FinitePairHistory Action Real 0)
                (sampledPredictableDeviationFiltration Env Action 1)
                inferInstance history := by
            rw [sampledPredictableDeviationFiltration_succ]
            exact Measurable.of_comap_le le_rfl
          have hcoordinate : Measurable
              (fun h : History.FinitePairHistory Action Real 0 =>
                h zeroIndex) := measurable_pi_apply zeroIndex
          have hselectedAction : Measurable selectedAction :=
            measurable_fst.comp (hcoordinate.comp measurable_snd)
          have hselectedReward : Measurable selectedReward :=
            measurable_snd.comp (hcoordinate.comp measurable_snd)
          have hraw : Measurable (fun input => arms.sum (fun candidate =>
              weight input candidate *
                importanceWeightedLoss (prob input)
                  (fun _ => selectedReward input) (selectedAction input) candidate)) := by
            refine Finset.measurable_sum arms fun candidate _hcandidate => ?_
            exact measurable_const.mul
              (measurable_observedImportanceWeightedLoss prob selectedAction
                selectedReward candidate measurable_const hselectedAction
                  hselectedReward)
          have htrueLoss : Measurable trueLoss := by
            refine Finset.measurable_sum arms fun candidate _hcandidate => ?_
            exact measurable_const.mul
              (loss.measurable_initial.comp
                (measurable_fst.prodMk measurable_const))
          have hscore : Measurable score := hraw.sub htrueLoss
          have hfactor :
              sampledPureObservedDeviationProcess arms eta gamma loss 1 =
                score ∘ history := by
            funext sample
            simp [sampledPureObservedDeviationProcess, score, weight, prob,
              selectedAction, selectedReward, trueLoss, history, zeroIndex,
              sampledTrajectoryPureObservedDeviationAt,
              sampledTrajectoryPureObservedLossAt,
              sampledTrajectoryPurePredictableLossAt,
              sampledTrajectoryPureProbabilityAt, sampledTrajectoryObservedLoss,
              observedImportanceWeightedLossAt, sampledTrajectoryProbabilityAt,
              predictableLossAt, mixedLoss, distribution, totalWeight,
              Exp3.weight, cumulativeLoss]
          rw [hfactor]
          exact (hscore.comp hhistory).stronglyMeasurable
      | succ n =>
          let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.1, Preorder.frestrictLe (n + 1) sample.2)
          let previous := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            (input.1, Preorder.frestrictLe₂
              (π := fun _ : Nat => Action × Real) n.le_succ input.2)
          let currentIndex : Finset.Iic (n + 1) := ⟨n + 1, by simp⟩
          let selectedAction := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            (input.2 currentIndex).1
          let selectedReward := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            (input.2 currentIndex).2
          let prob := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            sampledHistoryDistribution arms eta gamma n (previous input).2
          let weight := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            normalizedHistoryDistribution arms eta
              (sampledHistoryScore arms eta gamma n) (previous input).2
          let trueLoss := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            arms.sum (fun candidate =>
              weight input candidate *
                loss.successor n (previous input).1 (previous input).2 candidate)
          let score := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            arms.sum (fun candidate =>
                weight input candidate *
                  importanceWeightedLoss (prob input)
                    (fun _ => selectedReward input) (selectedAction input) candidate) -
              trueLoss input
          have hhistory :
              @Measurable (Env × ((k : Nat) -> Action × Real))
                (Env × History.FinitePairHistory Action Real (n + 1))
                (sampledPredictableDeviationFiltration Env Action (n + 2))
                inferInstance history := by
            rw [show n + 2 = (n + 1) + 1 by omega,
              sampledPredictableDeviationFiltration_succ]
            exact Measurable.of_comap_le le_rfl
          have hprevious : Measurable previous :=
            measurable_fst.prodMk
              ((Preorder.measurable_frestrictLe₂ n.le_succ).comp measurable_snd)
          have hcoordinate : Measurable
              (fun h : History.FinitePairHistory Action Real (n + 1) =>
                h currentIndex) := measurable_pi_apply currentIndex
          have hselectedAction : Measurable selectedAction :=
            measurable_fst.comp (hcoordinate.comp measurable_snd)
          have hselectedReward : Measurable selectedReward :=
            measurable_snd.comp (hcoordinate.comp measurable_snd)
          let probSource := sampledEnvironmentHistoryDistributionSource
            (Env := Env) arms harms eta gamma hgamma_nonneg hgamma_le_one n
          let localWeightSource := normalizedHistoryDistributionSource arms harms eta
            (sampledHistoryScore arms eta gamma)
            (measurableFiniteHistoryScore_sampledHistoryScore arms eta gamma) n
          have hraw : Measurable (fun input => arms.sum (fun candidate =>
              weight input candidate *
                importanceWeightedLoss (prob input)
                  (fun _ => selectedReward input) (selectedAction input) candidate)) := by
            refine Finset.measurable_sum arms fun candidate hcandidate => ?_
            exact
              ((localWeightSource.measurable_prob candidate hcandidate).comp
                (measurable_snd.comp hprevious)).mul
                (measurable_observedImportanceWeightedLoss prob selectedAction
                  selectedReward candidate
                    ((probSource.measurable_prob candidate hcandidate).comp hprevious)
                    hselectedAction hselectedReward)
          have htrueLoss : Measurable trueLoss := by
            refine Finset.measurable_sum arms fun candidate hcandidate => ?_
            exact
              ((localWeightSource.measurable_prob candidate hcandidate).comp
                (measurable_snd.comp hprevious)).mul
                ((loss.measurable_successor n).comp
                  ((measurable_fst.comp hprevious).prodMk
                    ((measurable_snd.comp hprevious).prodMk measurable_const)))
          have hscore : Measurable score := hraw.sub htrueLoss
          have hfactor :
              sampledPureObservedDeviationProcess arms eta gamma loss (n + 2) =
                score ∘ history := by
            funext sample
            have hprefix :
                Preorder.frestrictLe₂
                    (π := fun _ : Nat => Action × Real) n.le_succ
                    (Preorder.frestrictLe (n + 1) sample.2) =
                  Preorder.frestrictLe n sample.2 := by
              rfl
            simp [sampledPureObservedDeviationProcess, score, weight, prob,
              selectedAction, selectedReward, trueLoss, previous, history,
              currentIndex, sampledTrajectoryPureObservedDeviationAt,
              sampledTrajectoryPureObservedLossAt,
              sampledTrajectoryPurePredictableLossAt,
              sampledTrajectoryPureProbabilityAt, sampledTrajectoryObservedLoss,
              observedImportanceWeightedLossAt, sampledTrajectoryProbabilityAt,
              predictableLossAt, mixedLoss,
              distribution_sampledTrajectoryObservedLoss_succ, hprefix]
          rw [hfactor]
          exact (hscore.comp hhistory).stronglyMeasurable

noncomputable abbrev sampledPureObservedDeviationVarianceProxy
    {Action : Type v} (arms : Finset Action) (gamma : Real) : NNReal :=
  sampledComparatorEstimatorVarianceProxy arms gamma

noncomputable abbrev sampledPureObservedDeviationProxy
    {Action : Type v} (arms : Finset Action) (gamma : Real) : Nat -> NNReal :=
  sampledComparatorEstimatorDeviationProxy arms gamma

theorem sampledPureObservedDeviationProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledPureObservedDeviationProcess arms eta gamma loss i sample) =
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPureObservedDeviationAt
          arms eta gamma loss i sample) := by
  induction horizon with
  | zero =>
      simp [sampledPureObservedDeviationProcess]
  | succ n ih =>
      calc
        (Finset.range (Nat.succ n + 1)).sum (fun i =>
            sampledPureObservedDeviationProcess arms eta gamma loss i sample) =
            (Finset.range (n + 1)).sum (fun i =>
              sampledPureObservedDeviationProcess arms eta gamma loss i sample) +
              sampledPureObservedDeviationProcess
                arms eta gamma loss (n + 1) sample := by
                  rw [Finset.sum_range_succ]
        _ = (Finset.range n).sum (fun i =>
              sampledTrajectoryPureObservedDeviationAt
                arms eta gamma loss i sample) +
              sampledTrajectoryPureObservedDeviationAt
                arms eta gamma loss n sample := by
                  rw [ih]
                  rfl
        _ = (Finset.range (Nat.succ n)).sum (fun i =>
              sampledTrajectoryPureObservedDeviationAt
                arms eta gamma loss i sample) := by
                  rw [Finset.sum_range_succ]

/-- One-sided concentration for the pure-Hedge cross-weighted observed EXP3
estimator minus its true pure-Hedge predictable loss. -/
theorem sampledPureObservedDeviation_sum_tail_ennreal
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) {eps : Real} (heps : 0 <= eps) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample | eps <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPureObservedDeviationAt
          arms eta gamma loss i sample)} <=
      ENNReal.ofReal (Real.exp
        (-eps ^ 2 /
          (2 * ((((horizon : NNReal) *
            sampledPureObservedDeviationVarianceProxy arms gamma : NNReal)) : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledPureObservedDeviationProcess arms eta gamma loss
  let cY := sampledPureObservedDeviationProxy arms gamma
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (sampledPureObservedDeviationProcess_stronglyAdapted
        arms harms eta gamma hgamma_pos.le hgamma_le_one loss)
  have hzero : ProbabilityTheory.HasSubgaussianMGF
      (Y 0) (cY 0) mu := by
    change ProbabilityTheory.HasSubgaussianMGF (fun _ => 0) 0 mu
    exact ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have hcond : forall i, i < (horizon + 1) - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu := by
    intro i _hi
    cases i with
    | zero =>
        simpa [mu, F, Y, cY,
          sampledPureObservedDeviationProcess,
          sampledPureObservedDeviationProxy,
          sampledPureObservedDeviationVarianceProxy,
          sampledComparatorEstimatorDeviationProxy,
          sampledComparatorEstimatorVarianceProxy] using
          (sampledPureObservedDeviation_zero_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss)
    | succ n =>
        simpa [mu, F, Y, cY,
          sampledPureObservedDeviationProcess,
          sampledPureObservedDeviationProxy,
          sampledPureObservedDeviationVarianceProxy,
          sampledComparatorEstimatorDeviationProxy,
          sampledComparatorEstimatorVarianceProxy,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledPureObservedDeviation_succ_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss n)
  have htail := Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
    hadapted hzero (horizon + 1) hcond heps
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledPureObservedDeviationProcess_sum_range_succ
      arms eta gamma loss horizon sample
  have hproxy :=
    sampledComparatorEstimatorDeviationProxy_sum_range_succ arms gamma horizon
  simpa [Y, cY, sampledPureObservedDeviationProxy,
    sampledPureObservedDeviationVarianceProxy, hprocess, hproxy] using htail

noncomputable def sampledPureObservedDeviationConfidenceRadius
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  Real.sqrt
    (2 * ((((horizon : NNReal) *
      sampledPureObservedDeviationVarianceProxy arms gamma : NNReal)) : Real) *
        Real.log (1 / delta))

theorem sampledPureObservedDeviation_sum_tail_exp_neg_budget
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon : 0 < horizon) (budget : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample | Real.sqrt
          (2 * ((((horizon : NNReal) *
            sampledPureObservedDeviationVarianceProxy arms gamma : NNReal)) : Real) *
              budget) <=
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPureObservedDeviationAt
            arms eta gamma loss i sample)} <=
      ENNReal.ofReal (Real.exp (-budget)) := by
  dsimp only
  let variance : Real := ((((horizon : NNReal) *
    sampledPureObservedDeviationVarianceProxy arms gamma : NNReal)) : Real)
  let radius : Real := Real.sqrt (2 * variance * budget)
  have hvariance_pos : 0 < variance := by
    change 0 < (horizon : Real) *
      ((sampledComparatorEstimatorVarianceProxy arms gamma : NNReal) : Real)
    exact mul_pos (by exact_mod_cast hhorizon)
      (sampledComparatorEstimatorVarianceProxy_pos arms harms gamma hgamma_pos)
  have htail := sampledPureObservedDeviation_sum_tail_ennreal
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss
      horizon (eps := radius) (Real.sqrt_nonneg _)
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

/-- Delta-shaped one-sided confidence bound for the pure-Hedge cross-weighted
observed EXP3 estimator against its true pure-Hedge predictable loss. -/
theorem sampledPureObservedDeviation_sum_tail_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        sampledPureObservedDeviationConfidenceRadius
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPureObservedLossAt arms eta gamma i sample -
              sampledTrajectoryPurePredictableLossAt
                arms eta gamma loss i sample)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have htail :=
    sampledPureObservedDeviation_sum_tail_exp_neg_budget
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss
        horizon hhorizon (Real.log (1 / delta))
  have hscale : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hexp : Real.exp (-(Real.log (1 / delta))) = delta := by
    rw [Real.exp_neg, Real.exp_log hscale]
    field_simp
  rw [hexp] at htail
  simpa only [sampledPureObservedDeviationConfidenceRadius,
    sampledTrajectoryPureObservedDeviationAt] using htail

/-- The pure-Hedge predictable loss minus its observed cross-weighted estimator.
This is the sign needed when the sampled Hedge inequality is converted to true
predictable regret. -/
noncomputable def sampledTrajectoryPurePredictableMinusObservedAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample -
    sampledTrajectoryPureObservedLossAt arms eta gamma t sample

theorem sampledPurePredictableMinusObserved_zero_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectoryPurePredictableMinusObservedAt
        arms eta gamma loss 0)
      (sampledPureObservedDeviationVarianceProxy arms gamma) mu := by
  dsimp only
  have h := sampledPureObservedDeviation_zero_hasCondSubgaussianMGF
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss
  dsimp only at h
  change ProbabilityTheory.Kernel.HasSubgaussianMGF _ _ _ _ at h ⊢
  refine h.neg.congr (Filter.Eventually.of_forall fun sample => ?_)
  unfold sampledTrajectoryPurePredictableMinusObservedAt
    sampledTrajectoryPureObservedDeviationAt
  simp

theorem sampledPurePredictableMinusObserved_succ_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (sampledTrajectoryPurePredictableMinusObservedAt
        arms eta gamma loss (n + 1))
      (sampledPureObservedDeviationVarianceProxy arms gamma) mu := by
  dsimp only
  have h := sampledPureObservedDeviation_succ_hasCondSubgaussianMGF
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss n
  dsimp only at h
  change ProbabilityTheory.Kernel.HasSubgaussianMGF _ _ _ _ at h ⊢
  refine h.neg.congr (Filter.Eventually.of_forall fun sample => ?_)
  unfold sampledTrajectoryPurePredictableMinusObservedAt
    sampledTrajectoryPureObservedDeviationAt
  simp

noncomputable def sampledPurePredictableMinusObservedProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Real
  | 0, _sample => 0
  | i + 1, sample =>
      sampledTrajectoryPurePredictableMinusObservedAt
        arms eta gamma loss i sample

theorem sampledPurePredictableMinusObservedProcess_stronglyAdapted
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    StronglyAdapted
      (sampledPredictableDeviationFiltration Env Action)
      (sampledPurePredictableMinusObservedProcess arms eta gamma loss) := by
  have h := sampledPureObservedDeviationProcess_stronglyAdapted
    arms harms eta gamma hgamma_nonneg hgamma_le_one loss
  intro t
  have ht := (h t).neg
  convert ht using 1
  funext sample
  cases t with
  | zero =>
      simp [sampledPurePredictableMinusObservedProcess,
        sampledPureObservedDeviationProcess]
  | succ i =>
      simp [sampledPurePredictableMinusObservedProcess,
        sampledPureObservedDeviationProcess,
        sampledTrajectoryPurePredictableMinusObservedAt,
        sampledTrajectoryPureObservedDeviationAt]

theorem sampledPurePredictableMinusObservedProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledPurePredictableMinusObservedProcess
          arms eta gamma loss i sample) =
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPurePredictableMinusObservedAt
          arms eta gamma loss i sample) := by
  induction horizon with
  | zero =>
      simp [sampledPurePredictableMinusObservedProcess]
  | succ n ih =>
      calc
        (Finset.range (Nat.succ n + 1)).sum (fun i =>
            sampledPurePredictableMinusObservedProcess
              arms eta gamma loss i sample) =
            (Finset.range (n + 1)).sum (fun i =>
              sampledPurePredictableMinusObservedProcess
                arms eta gamma loss i sample) +
              sampledPurePredictableMinusObservedProcess
                arms eta gamma loss (n + 1) sample := by
                  rw [Finset.sum_range_succ]
        _ = (Finset.range n).sum (fun i =>
              sampledTrajectoryPurePredictableMinusObservedAt
                arms eta gamma loss i sample) +
              sampledTrajectoryPurePredictableMinusObservedAt
                arms eta gamma loss n sample := by
                  rw [ih]
                  rfl
        _ = (Finset.range (Nat.succ n)).sum (fun i =>
              sampledTrajectoryPurePredictableMinusObservedAt
                arms eta gamma loss i sample) := by
                  rw [Finset.sum_range_succ]

/-- One-sided concentration in the sign required by the predictable-regret
decomposition: true pure-Hedge predictable loss minus its observed estimator. -/
theorem sampledPurePredictableMinusObserved_sum_tail_ennreal
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) {eps : Real} (heps : 0 <= eps) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample | eps <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPurePredictableMinusObservedAt
          arms eta gamma loss i sample)} <=
      ENNReal.ofReal (Real.exp
        (-eps ^ 2 /
          (2 * ((((horizon : NNReal) *
            sampledPureObservedDeviationVarianceProxy arms gamma : NNReal)) : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledPurePredictableMinusObservedProcess arms eta gamma loss
  let cY := sampledPureObservedDeviationProxy arms gamma
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (sampledPurePredictableMinusObservedProcess_stronglyAdapted
        arms harms eta gamma hgamma_pos.le hgamma_le_one loss)
  have hzero : ProbabilityTheory.HasSubgaussianMGF
      (Y 0) (cY 0) mu := by
    change ProbabilityTheory.HasSubgaussianMGF (fun _ => 0) 0 mu
    exact ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have hcond : forall i, i < (horizon + 1) - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu := by
    intro i _hi
    cases i with
    | zero =>
        simpa [mu, F, Y, cY,
          sampledPurePredictableMinusObservedProcess,
          sampledPureObservedDeviationProxy,
          sampledPureObservedDeviationVarianceProxy,
          sampledComparatorEstimatorDeviationProxy,
          sampledComparatorEstimatorVarianceProxy] using
          (sampledPurePredictableMinusObserved_zero_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss)
    | succ n =>
        simpa [mu, F, Y, cY,
          sampledPurePredictableMinusObservedProcess,
          sampledPureObservedDeviationProxy,
          sampledPureObservedDeviationVarianceProxy,
          sampledComparatorEstimatorDeviationProxy,
          sampledComparatorEstimatorVarianceProxy,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledPurePredictableMinusObserved_succ_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss n)
  have htail := Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
    hadapted hzero (horizon + 1) hcond heps
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledPurePredictableMinusObservedProcess_sum_range_succ
      arms eta gamma loss horizon sample
  have hproxy :=
    sampledComparatorEstimatorDeviationProxy_sum_range_succ arms gamma horizon
  simpa [Y, cY, sampledPureObservedDeviationProxy,
    sampledPureObservedDeviationVarianceProxy, hprocess, hproxy] using htail

theorem sampledPurePredictableMinusObserved_sum_tail_exp_neg_budget
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon : 0 < horizon) (budget : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample | Real.sqrt
          (2 * ((((horizon : NNReal) *
            sampledPureObservedDeviationVarianceProxy arms gamma : NNReal)) : Real) *
              budget) <=
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPurePredictableMinusObservedAt
            arms eta gamma loss i sample)} <=
      ENNReal.ofReal (Real.exp (-budget)) := by
  dsimp only
  let variance : Real := ((((horizon : NNReal) *
    sampledPureObservedDeviationVarianceProxy arms gamma : NNReal)) : Real)
  let radius : Real := Real.sqrt (2 * variance * budget)
  have hvariance_pos : 0 < variance := by
    change 0 < (horizon : Real) *
      ((sampledComparatorEstimatorVarianceProxy arms gamma : NNReal) : Real)
    exact mul_pos (by exact_mod_cast hhorizon)
      (sampledComparatorEstimatorVarianceProxy_pos arms harms gamma hgamma_pos)
  have htail := sampledPurePredictableMinusObserved_sum_tail_ennreal
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss
      horizon (eps := radius) (Real.sqrt_nonneg _)
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

/-- Delta-shaped lower-tail counterpart in the sign needed by the generated
predictable EXP3 regret decomposition. -/
theorem sampledPurePredictableMinusObserved_sum_tail_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        sampledPureObservedDeviationConfidenceRadius
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPurePredictableLossAt
                arms eta gamma loss i sample -
              sampledTrajectoryPureObservedLossAt arms eta gamma i sample)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have htail :=
    sampledPurePredictableMinusObserved_sum_tail_exp_neg_budget
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss
        horizon hhorizon (Real.log (1 / delta))
  have hscale : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hexp : Real.exp (-(Real.log (1 / delta))) = delta := by
    rw [Real.exp_neg, Real.exp_log hscale]
    field_simp
  rw [hexp] at htail
  simpa only [sampledPureObservedDeviationConfidenceRadius,
    sampledTrajectoryPurePredictableMinusObservedAt] using htail

end BanditRLProof.Exp3
