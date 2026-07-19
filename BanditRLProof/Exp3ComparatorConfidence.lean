import BanditRLProof.Exp3RealizedDeviationTail

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v w

theorem comparatorEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
    {Omega : Type u} {History : Type v} {Action : Type w}
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
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (mHistory.comap history)
      hhistory.comap_le
      (fun omega =>
        importanceWeightedLoss (prob (history omega)) (loss (history omega))
          (action omega) comparator - loss (history omega) comparator)
      (Concentration.intervalVarianceProxy 0 (1 / epsilon)) mu := by
  let mcond := mHistory.comap history
  let X := fun omega =>
    importanceWeightedLoss (prob (history omega)) (loss (history omega))
      (action omega) comparator - loss (history omega) comparator
  let target : Omega -> Measure Real := fun omega => Measure.map
    (fun selected =>
      importanceWeightedLoss (prob (history omega)) (loss (history omega))
        selected comparator - loss (history omega) comparator)
    (finiteActionMeasure arms (prob (history omega)))
  have hmcond : mcond <= mOmega :=
    hhistory.comap_le
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
      _ = target omega := by
        rw [haction_eq]
  have htarget_subG :
      Filter.Eventually
        (fun omega => HasSubgaussianMGF (fun z : Real => z)
          (Concentration.intervalVarianceProxy 0 (1 / epsilon)) (target omega))
        (ae (mu.trim hmcond)) := by
    filter_upwards [] with omega
    let actionMu := finiteActionMeasure arms (prob (history omega))
    let raw : Action -> Real := fun selected =>
      importanceWeightedLoss (prob (history omega)) (loss (history omega))
        selected comparator
    let score : Action -> Real := fun selected =>
      raw selected - loss (history omega) comparator
    letI : IsProbabilityMeasure actionMu :=
      finiteActionMeasure_isProbabilityMeasure arms (prob (history omega))
        (source.distribution (history omega))
    have hraw : Measurable raw :=
      hrawPair.comp (measurable_const.prodMk measurable_id)
    have hbound : Filter.Eventually
        (fun selected => raw selected ∈ Set.Icc (0 : Real) (1 / epsilon))
        (ae actionMu) := Filter.Eventually.of_forall fun selected => by
      have hnonneg := importanceWeightedLoss_nonneg (chosen := selected)
        ((source.distribution (history omega)).nonneg comparator hcomparator)
        (regularity.loss_mem_Icc (history omega) comparator hcomparator).1
      refine ⟨hnonneg, ?_⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
        (norm_importanceWeightedLoss_score_le_inv_floor
          arms prob loss epsilon regularity (history omega) selected comparator
            hcomparator)
    have hmean : integral actionMu raw = loss (history omega) comparator := by
      rw [integral_finiteActionMeasure_eq_sum arms (prob (history omega))
        (source.distribution (history omega)) raw]
      simpa [raw] using sum_prob_mul_importanceWeightedLoss_eq_loss
        arms (prob (history omega)) (loss (history omega)) comparator hcomparator
          (regularity.prob_pos (history omega) comparator hcomparator).ne'
    have hsub : HasSubgaussianMGF score
        (Concentration.intervalVarianceProxy 0 (1 / epsilon)) actionMu := by
      simpa [score, raw] using
        (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
          actionMu hraw.aemeasurable hbound hmean)
    have hscore : Measurable score := hraw.sub measurable_const
    apply (HasSubgaussianMGF.id_map_iff hscore.aemeasurable).2
    simpa [target, actionMu, score, raw] using hsub
  exact ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
    (mOmega := mOmega)
    mu mcond hmcond X (Concentration.intervalVarianceProxy 0 (1 / epsilon))
      hX target hkernel_map htarget_subG

noncomputable def sampledTrajectoryPredictableComparatorEstimatorDeviationAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  importanceWeightedLoss
      (sampledTrajectoryProbabilityAt arms eta gamma t sample)
      (predictableLossAt loss t sample) (sample.2 t).1 comparator -
    predictableLossAt loss t sample comparator

noncomputable def sampledTrajectoryObservedComparatorEstimatorDeviationAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  observedImportanceWeightedLossAt arms eta gamma t sample comparator -
    predictableLossAt loss t sample comparator

theorem sampledPredictableComparatorEstimatorDeviation_zero_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectoryPredictableComparatorEstimatorDeviationAt
        arms eta gamma loss comparator 0)
      (Concentration.intervalVarianceProxy 0
        (1 / (gamma / (arms.card : Real)))) mu := by
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
    comparatorEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      mu history measurable_fst action (by fun_prop) arms prob loss.initial
        source (gamma / (arms.card : Real)) regularity comparator hcomparator hcond
  simpa [mu, history, action, prob,
    sampledTrajectoryPredictableComparatorEstimatorDeviationAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

theorem sampledPredictableComparatorEstimatorDeviation_succ_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (sampledTrajectoryPredictableComparatorEstimatorDeviationAt
        arms eta gamma loss comparator (n + 1))
      (Concentration.intervalVarianceProxy 0
        (1 / (gamma / (arms.card : Real)))) mu := by
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
    comparatorEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      mu history hhistory action haction arms prob roundLoss source
        (gamma / (arms.card : Real)) regularity comparator hcomparator hcond
  simpa [mu, history, action, prob, roundLoss,
    sampledTrajectoryPredictableComparatorEstimatorDeviationAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

theorem sampledObservedComparatorEstimatorDeviation_zero_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectoryObservedComparatorEstimatorDeviationAt
        arms eta gamma loss comparator 0)
      (Concentration.intervalVarianceProxy 0
        (1 / (gamma / (arms.card : Real)))) mu := by
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
    sampledPredictableComparatorEstimatorDeviation_zero_hasCondSubgaussianMGF
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator hcomparator
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
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryPredictableComparatorEstimatorDeviationAt
      arms eta gamma loss comparator 0)
    (Concentration.intervalVarianceProxy 0
      (1 / (gamma / (arms.card : Real))))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hpredictable
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryObservedComparatorEstimatorDeviationAt
      arms eta gamma loss comparator 0)
    (Concentration.intervalVarianceProxy 0
      (1 / (gamma / (arms.card : Real))))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply (ProbabilityTheory.Kernel.HasSubgaussianMGF_congr ?_).1 hpredictable
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

theorem sampledObservedComparatorEstimatorDeviation_succ_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (sampledTrajectoryObservedComparatorEstimatorDeviationAt
        arms eta gamma loss comparator (n + 1))
      (Concentration.intervalVarianceProxy 0
        (1 / (gamma / (arms.card : Real)))) mu := by
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
    sampledPredictableComparatorEstimatorDeviation_succ_hasCondSubgaussianMGF
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator
        hcomparator n
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
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryPredictableComparatorEstimatorDeviationAt
      arms eta gamma loss comparator (n + 1))
    (Concentration.intervalVarianceProxy 0
      (1 / (gamma / (arms.card : Real))))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hpredictable
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryObservedComparatorEstimatorDeviationAt
      arms eta gamma loss comparator (n + 1))
    (Concentration.intervalVarianceProxy 0
      (1 / (gamma / (arms.card : Real))))
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply (ProbabilityTheory.Kernel.HasSubgaussianMGF_congr ?_).1 hpredictable
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

noncomputable def sampledObservedComparatorEstimatorDeviationProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Real
  | 0, _sample => 0
  | i + 1, sample =>
      sampledTrajectoryObservedComparatorEstimatorDeviationAt
        arms eta gamma loss comparator i sample

noncomputable def sampledComparatorEstimatorVarianceProxy
    {Action : Type v} (arms : Finset Action) (gamma : Real) : NNReal :=
  Concentration.intervalVarianceProxy 0
    (1 / (gamma / (arms.card : Real)))

noncomputable def sampledComparatorEstimatorDeviationProxy
    {Action : Type v} (arms : Finset Action) (gamma : Real) : Nat -> NNReal
  | 0 => 0
  | _i + 1 => sampledComparatorEstimatorVarianceProxy arms gamma

theorem sampledObservedComparatorEstimatorDeviationProcess_stronglyAdapted
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    StronglyAdapted
      (sampledPredictableDeviationFiltration Env Action)
      (sampledObservedComparatorEstimatorDeviationProcess
        arms eta gamma loss comparator) := by
  intro t
  cases t with
  | zero =>
      simpa [sampledObservedComparatorEstimatorDeviationProcess] using
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
          let trueLoss := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            loss.initial input.1 comparator
          let score := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            importanceWeightedLoss (prob input)
                (fun _ => selectedReward input) (selectedAction input) comparator -
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
          have htrueLoss : Measurable trueLoss :=
            loss.measurable_initial.comp
              (measurable_fst.prodMk measurable_const)
          have hraw : Measurable (fun input =>
              importanceWeightedLoss (prob input)
                (fun _ => selectedReward input) (selectedAction input) comparator) :=
            measurable_observedImportanceWeightedLoss prob selectedAction
              selectedReward comparator measurable_const hselectedAction hselectedReward
          have hscore : Measurable score := hraw.sub htrueLoss
          have hfactor :
              sampledObservedComparatorEstimatorDeviationProcess
                  arms eta gamma loss comparator 1 = score ∘ history := by
            funext sample
            simp [sampledObservedComparatorEstimatorDeviationProcess, score,
              prob, selectedAction, selectedReward, trueLoss, history, zeroIndex,
              sampledTrajectoryObservedComparatorEstimatorDeviationAt,
              observedImportanceWeightedLossAt, sampledTrajectoryProbabilityAt,
              predictableLossAt]
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
          let trueLoss := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            loss.successor n (previous input).1 (previous input).2 comparator
          let score := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            importanceWeightedLoss (prob input)
                (fun _ => selectedReward input) (selectedAction input) comparator -
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
          let source := sampledEnvironmentHistoryDistributionSource
            (Env := Env) arms harms eta gamma hgamma_nonneg hgamma_le_one n
          have hprob : Measurable (fun input => prob input comparator) :=
            (source.measurable_prob comparator hcomparator).comp hprevious
          have htrueLoss : Measurable trueLoss :=
            (loss.measurable_successor n).comp
              ((measurable_fst.comp hprevious).prodMk
                ((measurable_snd.comp hprevious).prodMk measurable_const))
          have hraw : Measurable (fun input =>
              importanceWeightedLoss (prob input)
                (fun _ => selectedReward input) (selectedAction input) comparator) :=
            measurable_observedImportanceWeightedLoss prob selectedAction
              selectedReward comparator hprob hselectedAction hselectedReward
          have hscore : Measurable score := hraw.sub htrueLoss
          have hfactor :
              sampledObservedComparatorEstimatorDeviationProcess
                  arms eta gamma loss comparator (n + 2) = score ∘ history := by
            funext sample
            have hprefix :
                Preorder.frestrictLe₂
                    (π := fun _ : Nat => Action × Real) n.le_succ
                    (Preorder.frestrictLe (n + 1) sample.2) =
                  Preorder.frestrictLe n sample.2 := by
              rfl
            simp [sampledObservedComparatorEstimatorDeviationProcess, score,
              prob, selectedAction, selectedReward, trueLoss, previous, history,
              currentIndex, sampledTrajectoryObservedComparatorEstimatorDeviationAt,
              observedImportanceWeightedLossAt, sampledTrajectoryProbabilityAt,
              predictableLossAt, hprefix]
          rw [hfactor]
          exact (hscore.comp hhistory).stronglyMeasurable

theorem sampledObservedComparatorEstimatorDeviationProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledObservedComparatorEstimatorDeviationProcess
          arms eta gamma loss comparator i sample) =
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryObservedComparatorEstimatorDeviationAt
          arms eta gamma loss comparator i sample) := by
  induction horizon with
  | zero =>
      simp [sampledObservedComparatorEstimatorDeviationProcess]
  | succ n ih =>
      calc
        (Finset.range (Nat.succ n + 1)).sum (fun i =>
            sampledObservedComparatorEstimatorDeviationProcess
              arms eta gamma loss comparator i sample) =
            (Finset.range (n + 1)).sum (fun i =>
              sampledObservedComparatorEstimatorDeviationProcess
                arms eta gamma loss comparator i sample) +
              sampledObservedComparatorEstimatorDeviationProcess
                arms eta gamma loss comparator (n + 1) sample := by
                  rw [Finset.sum_range_succ]
        _ = (Finset.range n).sum (fun i =>
              sampledTrajectoryObservedComparatorEstimatorDeviationAt
                arms eta gamma loss comparator i sample) +
              sampledTrajectoryObservedComparatorEstimatorDeviationAt
                arms eta gamma loss comparator n sample := by
                  rw [ih]
                  rfl
        _ = (Finset.range (Nat.succ n)).sum (fun i =>
              sampledTrajectoryObservedComparatorEstimatorDeviationAt
                arms eta gamma loss comparator i sample) := by
                  rw [Finset.sum_range_succ]

theorem sampledComparatorEstimatorDeviationProxy_sum_range_succ
    {Action : Type v} (arms : Finset Action) (gamma : Real) (horizon : Nat) :
    (Finset.range (horizon + 1)).sum
        (sampledComparatorEstimatorDeviationProxy arms gamma) =
      (horizon : NNReal) * sampledComparatorEstimatorVarianceProxy arms gamma := by
  induction horizon with
  | zero =>
      simp [sampledComparatorEstimatorDeviationProxy]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by rfl,
        Finset.sum_range_succ, ih]
      simp only [sampledComparatorEstimatorDeviationProxy]
      push_cast
      ring

/-- Fixed-comparator concentration for the observed importance-weighted EXP3
estimator minus its true predictable comparator loss. -/
theorem sampledObservedComparatorEstimatorDeviation_sum_tail_ennreal
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
    (horizon : Nat) {eps : Real} (heps : 0 <= eps) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample | eps <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryObservedComparatorEstimatorDeviationAt
          arms eta gamma loss comparator i sample)} <=
      ENNReal.ofReal (Real.exp
        (-eps ^ 2 /
          (2 * ((((horizon : NNReal) *
            sampledComparatorEstimatorVarianceProxy arms gamma : NNReal)) : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledObservedComparatorEstimatorDeviationProcess
    arms eta gamma loss comparator
  let cY := sampledComparatorEstimatorDeviationProxy arms gamma
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (sampledObservedComparatorEstimatorDeviationProcess_stronglyAdapted
        arms harms eta gamma hgamma_pos.le hgamma_le_one loss comparator hcomparator)
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
          sampledObservedComparatorEstimatorDeviationProcess,
          sampledComparatorEstimatorDeviationProxy,
          sampledComparatorEstimatorVarianceProxy] using
          (sampledObservedComparatorEstimatorDeviation_zero_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator
              hcomparator)
    | succ n =>
        simpa [mu, F, Y, cY,
          sampledObservedComparatorEstimatorDeviationProcess,
          sampledComparatorEstimatorDeviationProxy,
          sampledComparatorEstimatorVarianceProxy,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledObservedComparatorEstimatorDeviation_succ_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator
              hcomparator n)
  have htail := Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
    hadapted hzero (horizon + 1) hcond heps
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledObservedComparatorEstimatorDeviationProcess_sum_range_succ
      arms eta gamma loss comparator horizon sample
  have hproxy :=
    sampledComparatorEstimatorDeviationProxy_sum_range_succ arms gamma horizon
  simpa [Y, cY, hprocess, hproxy] using htail

noncomputable def sampledComparatorEstimatorConfidenceRadius
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  Real.sqrt
    (2 * ((((horizon : NNReal) *
      sampledComparatorEstimatorVarianceProxy arms gamma : NNReal)) : Real) *
        Real.log (1 / delta))

theorem sampledComparatorEstimatorVarianceProxy_pos
    {Action : Type v} (arms : Finset Action) (harms : arms.Nonempty)
    (gamma : Real) (hgamma_pos : 0 < gamma) :
    0 < ((sampledComparatorEstimatorVarianceProxy arms gamma : NNReal) : Real) := by
  have hfloor : 0 < gamma / (arms.card : Real) :=
    explorationFloor_pos arms harms gamma hgamma_pos
  have hinv : 0 < 1 / (gamma / (arms.card : Real)) := one_div_pos.mpr hfloor
  unfold sampledComparatorEstimatorVarianceProxy
  unfold Concentration.intervalVarianceProxy
  rw [NNReal.coe_pos]
  apply sq_pos_of_pos
  rw [← NNReal.coe_pos]
  push_cast
  rw [Real.norm_of_nonneg]
  · simpa using div_pos hinv (by norm_num : (0 : Real) < 2)
  · simpa using hinv.le

theorem sampledObservedComparatorEstimatorDeviation_sum_tail_exp_neg_budget
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
    (horizon : Nat) (hhorizon : 0 < horizon) (budget : Real) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample | Real.sqrt
          (2 * ((((horizon : NNReal) *
            sampledComparatorEstimatorVarianceProxy arms gamma : NNReal)) : Real) *
              budget) <=
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryObservedComparatorEstimatorDeviationAt
            arms eta gamma loss comparator i sample)} <=
      ENNReal.ofReal (Real.exp (-budget)) := by
  dsimp only
  let variance : Real := ((((horizon : NNReal) *
    sampledComparatorEstimatorVarianceProxy arms gamma : NNReal)) : Real)
  let radius : Real := Real.sqrt (2 * variance * budget)
  have hvariance_pos : 0 < variance := by
    change 0 < (horizon : Real) *
      ((sampledComparatorEstimatorVarianceProxy arms gamma : NNReal) : Real)
    exact mul_pos (by exact_mod_cast hhorizon)
      (sampledComparatorEstimatorVarianceProxy_pos arms harms gamma hgamma_pos)
  have htail := sampledObservedComparatorEstimatorDeviation_sum_tail_ennreal
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator hcomparator
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

/-- Delta-shaped one-sided confidence bound for a fixed comparator's observed
importance-weighted estimator against its true predictable loss. -/
theorem sampledObservedComparatorEstimatorDeviation_sum_tail_delta
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
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        sampledComparatorEstimatorConfidenceRadius arms gamma horizon delta <=
          (Finset.range horizon).sum (fun i =>
            observedImportanceWeightedLossAt arms eta gamma i sample comparator -
              predictableLossAt loss i sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have htail :=
    sampledObservedComparatorEstimatorDeviation_sum_tail_exp_neg_budget
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss comparator hcomparator
        horizon hhorizon (Real.log (1 / delta))
  have hscale : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hexp : Real.exp (-(Real.log (1 / delta))) = delta := by
    rw [Real.exp_neg, Real.exp_log hscale]
    field_simp
  rw [hexp] at htail
  simpa only [sampledComparatorEstimatorConfidenceRadius,
    sampledTrajectoryObservedComparatorEstimatorDeviationAt] using htail

end BanditRLProof.Exp3
