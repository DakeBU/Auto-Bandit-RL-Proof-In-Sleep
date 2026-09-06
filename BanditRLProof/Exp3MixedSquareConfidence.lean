import BanditRLProof.Exp3RandomSquareHighProbabilityRegret

/-!
# Exponential confidence for the EXP3 mixed estimator-square sum

This module replaces the Markov-only confidence step for the observed mixed
importance-weighted estimator-square sum by a finite-action conditional
sub-Gaussian route.  The raw score lies in `[0, 1 / epsilon]` and its
conditional mean is the armwise predictable loss-square sum.  Consequently,
the centered generated process has an exponential finite-horizon tail.

The proxy remains Hoeffding's interval proxy for `[0, |arms| / gamma]`.  This
is a genuine exponential tail, but not the sharper variance-sensitive
Freedman/EXP3.P rate.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v w

/-- Under a positive probability floor and unit losses, the mixed estimator
square has the sharper reciprocal-floor bound, rather than the generic square
of that reciprocal. -/
theorem mixedSquaredImportanceWeightedLoss_le_inv_floor
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (epsilon : Real)
    (regularity : BoundedMeasurableLossWithProbabilityFloor
      arms prob loss epsilon)
    (history : History) (chosen : Action) :
    mixedSquaredImportanceWeightedLoss arms (prob history) (loss history)
        chosen <= 1 / epsilon := by
  by_cases hchosen : chosen ∈ arms
  · have hprob_pos := regularity.prob_pos history chosen hchosen
    have hloss := regularity.loss_mem_Icc history chosen hchosen
    have hsq : (loss history chosen) ^ 2 <= 1 := by
      nlinarith [hloss.1, hloss.2]
    have hone_le : 1 <= (1 / epsilon) * prob history chosen := by
      rw [one_div_mul_eq_div, le_div_iff₀ regularity.epsilon_pos]
      simpa using regularity.prob_floor history chosen hchosen
    rw [mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div
      arms (prob history) (loss history) chosen hchosen hprob_pos.ne']
    apply (div_le_iff₀ hprob_pos).2
    exact hsq.trans hone_le
  · have hzero : mixedSquaredImportanceWeightedLoss arms (prob history)
        (loss history) chosen = 0 := by
      unfold mixedSquaredImportanceWeightedLoss
      apply Finset.sum_eq_zero
      intro candidate hcandidate
      have hne : chosen ≠ candidate := by
        intro heq
        exact hchosen (heq ▸ hcandidate)
      simp [importanceWeightedLoss, hne]
    rw [hzero]
    exact one_div_nonneg.mpr regularity.epsilon_pos.le

/-- A finite-action mixed estimator square, centered by its exact conditional
mean, is conditionally sub-Gaussian whenever the selected action has the stated
finite-action conditional distribution. -/
theorem mixedSquaredEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
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
    (hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (mHistory.comap history)
      hhistory.comap_le
      (fun omega =>
        mixedSquaredImportanceWeightedLoss arms (prob (history omega))
            (loss (history omega)) (action omega) -
          arms.sum (fun candidate => (loss (history omega) candidate) ^ 2))
      (Concentration.intervalVarianceProxy 0 (1 / epsilon)) mu := by
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
  have htarget_subG :
      Filter.Eventually
        (fun omega => HasSubgaussianMGF (fun z : Real => z)
          (Concentration.intervalVarianceProxy 0 (1 / epsilon)) (target omega))
        (ae (mu.trim hmcond)) := by
    filter_upwards [] with omega
    let actionMu := finiteActionMeasure arms (prob (history omega))
    let raw : Action -> Real := fun selected =>
      mixedSquaredImportanceWeightedLoss arms (prob (history omega))
        (loss (history omega)) selected
    let score : Action -> Real := fun selected => raw selected - mean (history omega)
    letI : IsProbabilityMeasure actionMu :=
      finiteActionMeasure_isProbabilityMeasure arms (prob (history omega))
        (source.distribution (history omega))
    have hraw : Measurable raw :=
      hrawPair.comp (measurable_const.prodMk measurable_id)
    have hbound : Filter.Eventually
        (fun selected => raw selected ∈ Set.Icc (0 : Real) (1 / epsilon))
        (ae actionMu) := Filter.Eventually.of_forall fun selected => by
      have hnonneg : 0 <= raw selected := by
        unfold raw mixedSquaredImportanceWeightedLoss
        exact Finset.sum_nonneg fun candidate hcandidate =>
          mul_nonneg
            ((source.distribution (history omega)).nonneg candidate hcandidate)
            (sq_nonneg _)
      exact ⟨hnonneg,
        mixedSquaredImportanceWeightedLoss_le_inv_floor arms prob loss
          epsilon regularity (history omega) selected⟩
    have hmean_eq : integral actionMu raw = mean (history omega) := by
      rw [integral_finiteActionMeasure_eq_sum arms (prob (history omega))
        (source.distribution (history omega)) raw]
      simpa [raw, mean] using
        (sum_prob_mul_mixedSquaredImportanceWeightedLoss_eq_sum_loss_sq
          arms (prob (history omega)) (loss (history omega))
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

/-- The predictable mixed-square deviation at an actual generated time. -/
noncomputable def sampledTrajectoryPredictableMixedSquaredDeviationAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  mixedSquaredImportanceWeightedLoss arms
      (sampledTrajectoryProbabilityAt arms eta gamma t sample)
      (predictableLossAt loss t sample) (sample.2 t).1 -
    arms.sum (fun candidate => (predictableLossAt loss t sample candidate) ^ 2)

theorem sampledPredictableMixedSquaredDeviation_zero_hasCondSubgaussianMGF
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
      (sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss 0)
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
    mixedSquaredEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      mu history measurable_fst action (by fun_prop) arms prob loss.initial
        source (gamma / (arms.card : Real)) regularity hcond
  simpa [mu, history, action, prob,
    sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

theorem sampledPredictableMixedSquaredDeviation_succ_hasCondSubgaussianMGF
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
      (sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss (n + 1))
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
    mixedSquaredEstimator_hasCondSubgaussianMGF_of_condDistrib_ae_eq_finiteActionKernel
      mu history hhistory action haction arms prob roundLoss source
        (gamma / (arms.card : Real)) regularity hcond
  simpa [mu, history, action, prob, roundLoss,
    sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledTrajectoryProbabilityAt, predictableLossAt] using hmgf

/-- Shift the actual-time predictable mixed-square deviations by one so that
the process starts with the deterministic zero required by the finite-sum
conditional concentration API. -/
noncomputable def sampledPredictableMixedSquaredDeviationProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Real
  | 0, _sample => 0
  | i + 1, sample =>
      sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss i sample

noncomputable def sampledMixedSquaredVarianceProxy
    {Action : Type v} (arms : Finset Action) (gamma : Real) : NNReal :=
  Concentration.intervalVarianceProxy 0
    (1 / (gamma / (arms.card : Real)))

noncomputable def sampledMixedSquaredDeviationProxy
    {Action : Type v} (arms : Finset Action) (gamma : Real) : Nat -> NNReal
  | 0 => 0
  | _i + 1 => sampledMixedSquaredVarianceProxy arms gamma

set_option maxHeartbeats 800000 in
theorem sampledPredictableMixedSquaredDeviationProcess_stronglyAdapted
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    StronglyAdapted
      (sampledPredictableDeviationFiltration Env Action)
      (sampledPredictableMixedSquaredDeviationProcess
        arms eta gamma loss) := by
  intro t
  cases t with
  | zero =>
      simpa [sampledPredictableMixedSquaredDeviationProcess] using
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
          let prob := fun _env : Env =>
            initialExploredDistribution arms eta gamma
          let roundLoss := loss.initial
          let mean := fun env : Env =>
            arms.sum (fun candidate => (roundLoss env candidate) ^ 2)
          let raw := fun input : Env × History.FinitePairHistory Action Real 0 =>
            mixedSquaredImportanceWeightedLoss arms (prob input.1)
              (roundLoss input.1) (selectedAction input)
          let score := fun input : Env × History.FinitePairHistory Action Real 0 =>
            raw input - mean input.1
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
          let source := sampledInitialEnvironmentDistributionSource
            (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one
          let regularity := sampledPredictableInitialLossRegularity
            arms harms eta gamma hgamma_pos hgamma_le_one loss
          have hrawBase : Measurable (fun input : Env × Action =>
              mixedSquaredImportanceWeightedLoss arms (prob input.1)
                (roundLoss input.1) input.2) :=
            measurable_mixedSquaredImportanceWeightedLoss_score
              arms prob roundLoss source (gamma / (arms.card : Real)) regularity
          have hrawInput : Measurable (fun input :
              Env × History.FinitePairHistory Action Real 0 =>
                (input.1, selectedAction input)) :=
            measurable_fst.prodMk hselectedAction
          have hraw : Measurable raw := by
            simpa [raw, prob, roundLoss] using hrawBase.comp hrawInput
          have hmean : Measurable mean := by
            refine Finset.measurable_sum arms fun candidate _hcandidate => ?_
            exact (loss.measurable_initial.comp
              (measurable_id.prodMk measurable_const)).pow_const 2
          have hscore : Measurable score := hraw.sub (hmean.comp measurable_fst)
          have hfactor :
              sampledPredictableMixedSquaredDeviationProcess
                  arms eta gamma loss 1 = score ∘ history := by
            funext sample
            simp [sampledPredictableMixedSquaredDeviationProcess, score, raw,
              mean, prob, roundLoss, selectedAction, history, zeroIndex,
              sampledTrajectoryPredictableMixedSquaredDeviationAt,
              sampledTrajectoryProbabilityAt, predictableLossAt]
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
          let prob := fun input : Env × History.FinitePairHistory Action Real n =>
            sampledHistoryDistribution arms eta gamma n input.2
          let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
            loss.successor n input.1 input.2
          let mean := fun input : Env × History.FinitePairHistory Action Real n =>
            arms.sum (fun candidate => (roundLoss input candidate) ^ 2)
          let raw := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            mixedSquaredImportanceWeightedLoss arms (prob (previous input))
              (roundLoss (previous input)) (selectedAction input)
          let score := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            raw input - mean (previous input)
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
          let source := sampledEnvironmentHistoryDistributionSource
            (Env := Env) arms harms eta gamma hgamma_pos.le hgamma_le_one n
          let regularity := sampledPredictableSuccessorLossRegularity
            arms harms eta gamma hgamma_pos hgamma_le_one loss n
          have hrawBase : Measurable
              (fun input : (Env × History.FinitePairHistory Action Real n) × Action =>
                mixedSquaredImportanceWeightedLoss arms (prob input.1)
                  (roundLoss input.1) input.2) :=
            measurable_mixedSquaredImportanceWeightedLoss_score
              arms prob roundLoss source (gamma / (arms.card : Real)) regularity
          have hrawInput : Measurable (fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
                (previous input, selectedAction input)) :=
            hprevious.prodMk hselectedAction
          have hraw : Measurable raw := by
            simpa [raw] using hrawBase.comp hrawInput
          have hmean : Measurable mean := by
            refine Finset.measurable_sum arms fun candidate hcandidate => ?_
            exact (regularity.measurable_loss candidate hcandidate).pow_const 2
          have hscore : Measurable score :=
            hraw.sub (hmean.comp hprevious)
          have hfactor :
              sampledPredictableMixedSquaredDeviationProcess
                  arms eta gamma loss (n + 2) = score ∘ history := by
            funext sample
            have hprefix :
                Preorder.frestrictLe₂
                    (π := fun _ : Nat => Action × Real) n.le_succ
                    (Preorder.frestrictLe (n + 1) sample.2) =
                  Preorder.frestrictLe n sample.2 := by
              rfl
            simp [sampledPredictableMixedSquaredDeviationProcess, score, raw,
              mean, prob, roundLoss, previous, selectedAction, history,
              currentIndex, sampledTrajectoryPredictableMixedSquaredDeviationAt,
              sampledTrajectoryProbabilityAt, predictableLossAt, hprefix]
          rw [hfactor]
          exact (hscore.comp hhistory).stronglyMeasurable

theorem sampledPredictableMixedSquaredDeviationProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledPredictableMixedSquaredDeviationProcess
          arms eta gamma loss i sample) =
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredDeviationAt
          arms eta gamma loss i sample) := by
  induction horizon with
  | zero => simp [sampledPredictableMixedSquaredDeviationProcess]
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by rfl,
        Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      rfl

theorem sampledMixedSquaredDeviationProxy_sum_range_succ
    {Action : Type v} (arms : Finset Action) (gamma : Real) (horizon : Nat) :
    (Finset.range (horizon + 1)).sum
        (sampledMixedSquaredDeviationProxy arms gamma) =
      (horizon : NNReal) * sampledMixedSquaredVarianceProxy arms gamma := by
  induction horizon with
  | zero => simp [sampledMixedSquaredDeviationProxy]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by rfl,
        Finset.sum_range_succ, ih]
      simp only [sampledMixedSquaredDeviationProxy]
      push_cast
      ring

/-- Exponential tail for the centered predictable mixed estimator-square sum. -/
theorem sampledPredictableMixedSquaredDeviation_sum_tail_ennreal
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
        sampledTrajectoryPredictableMixedSquaredDeviationAt
          arms eta gamma loss i sample)} <=
      ENNReal.ofReal (Real.exp
        (-eps ^ 2 /
          (2 * ((((horizon : NNReal) *
            sampledMixedSquaredVarianceProxy arms gamma : NNReal)) : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledPredictableMixedSquaredDeviationProcess arms eta gamma loss
  let cY := sampledMixedSquaredDeviationProxy arms gamma
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (sampledPredictableMixedSquaredDeviationProcess_stronglyAdapted
        arms harms eta gamma hgamma_pos hgamma_le_one loss)
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
          sampledPredictableMixedSquaredDeviationProcess,
          sampledMixedSquaredDeviationProxy,
          sampledMixedSquaredVarianceProxy] using
          (sampledPredictableMixedSquaredDeviation_zero_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss)
    | succ n =>
        simpa [mu, F, Y, cY,
          sampledPredictableMixedSquaredDeviationProcess,
          sampledMixedSquaredDeviationProxy,
          sampledMixedSquaredVarianceProxy,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledPredictableMixedSquaredDeviation_succ_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_pos hgamma_le_one loss n)
  have htail := Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
    hadapted hzero (horizon + 1) hcond heps
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledPredictableMixedSquaredDeviationProcess_sum_range_succ
      arms eta gamma loss horizon sample
  have hproxy :=
    sampledMixedSquaredDeviationProxy_sum_range_succ arms gamma horizon
  simpa [Y, cY, hprocess, hproxy] using htail

/-- The latent predictable mixed estimator-square sum. -/
noncomputable def sampledPredictableMixedSquaredSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range horizon).sum (fun t =>
    mixedSquaredImportanceWeightedLoss arms
      (sampledTrajectoryProbabilityAt arms eta gamma t sample)
      (predictableLossAt loss t sample) (sample.2 t).1)

/-- The sum of exact conditional means of the latent mixed-square scores. -/
noncomputable def sampledPredictableLossSquaredSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range horizon).sum (fun t =>
    arms.sum (fun candidate => (predictableLossAt loss t sample candidate) ^ 2))

theorem sampledPredictableLossSquaredAt_le_card
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    arms.sum (fun candidate => (predictableLossAt loss t sample candidate) ^ 2) <=
      (arms.card : Real) := by
  calc
    arms.sum (fun candidate => (predictableLossAt loss t sample candidate) ^ 2) <=
        arms.sum (fun _candidate => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro candidate _hcandidate
      cases t with
      | zero =>
          have hloss := loss.initial_mem_unitInterval sample.1 candidate
          simpa [predictableLossAt] using
            (sq_le_sq₀ hloss.1 zero_le_one).2 hloss.2
      | succ n =>
          have hloss := loss.successor_mem_unitInterval n sample.1
            (Preorder.frestrictLe n sample.2) candidate
          simpa [predictableLossAt] using
            (sq_le_sq₀ hloss.1 zero_le_one).2 hloss.2
    _ = (arms.card : Real) := by simp

theorem sampledPredictableLossSquaredSum_le_card_mul
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledPredictableLossSquaredSum arms loss horizon sample <=
      (arms.card : Real) * (horizon : Real) := by
  unfold sampledPredictableLossSquaredSum
  calc
    (Finset.range horizon).sum (fun t =>
        arms.sum (fun candidate => (predictableLossAt loss t sample candidate) ^ 2)) <=
      (Finset.range horizon).sum (fun _t => (arms.card : Real)) := by
        exact Finset.sum_le_sum fun t _ht =>
          sampledPredictableLossSquaredAt_le_card arms loss t sample
    _ = (arms.card : Real) * (horizon : Real) := by
      simp [mul_comm]

theorem sampledPredictableMixedSquaredDeviation_sum_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range horizon).sum (fun t =>
        sampledTrajectoryPredictableMixedSquaredDeviationAt
          arms eta gamma loss t sample) =
      sampledPredictableMixedSquaredSum arms eta gamma loss horizon sample -
        sampledPredictableLossSquaredSum arms loss horizon sample := by
  simp [sampledTrajectoryPredictableMixedSquaredDeviationAt,
    sampledPredictableMixedSquaredSum, sampledPredictableLossSquaredSum,
    Finset.sum_sub_distrib]

/-- Exponential tail for the latent, uncentered mixed estimator-square sum. -/
theorem sampledPredictableMixedSquared_sum_tail_ennreal
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
    mu {sample |
        (arms.card : Real) * (horizon : Real) + eps <=
          sampledPredictableMixedSquaredSum arms eta gamma loss horizon sample} <=
      ENNReal.ofReal (Real.exp
        (-eps ^ 2 /
          (2 * ((((horizon : NNReal) *
            sampledMixedSquaredVarianceProxy arms gamma : NNReal)) : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  have htail := sampledPredictableMixedSquaredDeviation_sum_tail_ennreal
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon heps
  let raw := sampledPredictableMixedSquaredSum
    (Env := Env) arms eta gamma loss horizon
  let mean := sampledPredictableLossSquaredSum arms loss horizon
  let centered := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryPredictableMixedSquaredDeviationAt
        arms eta gamma loss t sample)
  have hsubset :
      {sample | (arms.card : Real) * (horizon : Real) + eps <= raw sample} ⊆
        {sample | eps <= centered sample} := by
    intro sample hsample
    have hmean := sampledPredictableLossSquaredSum_le_card_mul
      arms loss horizon sample
    have hcentered := sampledPredictableMixedSquaredDeviation_sum_eq
      arms eta gamma loss horizon sample
    dsimp [raw, mean, centered] at hsample hmean hcentered ⊢
    linarith
  exact (measure_mono hsubset).trans (by simpa [mu, centered] using htail)

/-- The observed scalar-feedback mixed-square sum agrees almost everywhere
with the latent predictable mixed-square sum. -/
theorem sampledObservedMixedSquaredSum_eq_predictable_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    sampledObservedMixedSquaredSum arms eta gamma horizon =ᵐ[mu]
      sampledPredictableMixedSquaredSum arms eta gamma loss horizon := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  induction horizon with
  | zero =>
      exact Filter.Eventually.of_forall fun sample => by
        simp [sampledObservedMixedSquaredSum, sampledPredictableMixedSquaredSum]
  | succ n ih =>
      have hterm :=
        (observedAt_eq_predictableAt_ae prior arms harms eta gamma hgamma_nonneg
          hgamma_le_one loss n (Classical.choice inferInstance)).2
      filter_upwards [ih, hterm] with sample hsum hscore
      simp only [sampledObservedMixedSquaredSum, sampledPredictableMixedSquaredSum,
        Finset.sum_range_succ] at hsum ⊢
      rw [hsum, hscore]

/-- Exponential confidence for the observed mixed estimator-square sum. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_exponential
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
    mu {sample |
        (arms.card : Real) * (horizon : Real) + eps <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample} <=
      ENNReal.ofReal (Real.exp
        (-eps ^ 2 /
          (2 * ((((horizon : NNReal) *
            sampledMixedSquaredVarianceProxy arms gamma : NNReal)) : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  have htail := sampledPredictableMixedSquared_sum_tail_ennreal
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon heps
  have heq := sampledObservedMixedSquaredSum_eq_predictable_ae
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss horizon
  have hevents :
      {sample | (arms.card : Real) * (horizon : Real) + eps <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample} =ᵐ[mu]
        {sample | (arms.card : Real) * (horizon : Real) + eps <=
          sampledPredictableMixedSquaredSum arms eta gamma loss horizon sample} := by
    filter_upwards [heq] with sample hsample
    change ((arms.card : Real) * (horizon : Real) + eps <=
        sampledObservedMixedSquaredSum arms eta gamma horizon sample) =
      ((arms.card : Real) * (horizon : Real) + eps <=
        sampledPredictableMixedSquaredSum arms eta gamma loss horizon sample)
    rw [hsample]
  rw [measure_congr hevents]
  simpa [mu] using htail

noncomputable def sampledMixedSquaredConfidenceRadius
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  Real.sqrt
    (2 * ((((horizon : NNReal) *
      sampledMixedSquaredVarianceProxy arms gamma : NNReal)) : Real) *
        Real.log (1 / delta))

theorem sampledMixedSquaredVarianceProxy_pos
    {Action : Type v} (arms : Finset Action) (harms : arms.Nonempty)
    (gamma : Real) (hgamma_pos : 0 < gamma) :
    0 < ((sampledMixedSquaredVarianceProxy arms gamma : NNReal) : Real) := by
  have hfloor : 0 < gamma / (arms.card : Real) :=
    explorationFloor_pos arms harms gamma hgamma_pos
  have hinv : 0 < 1 / (gamma / (arms.card : Real)) := one_div_pos.mpr hfloor
  unfold sampledMixedSquaredVarianceProxy
  unfold Concentration.intervalVarianceProxy
  rw [NNReal.coe_pos]
  apply sq_pos_of_pos
  rw [← NNReal.coe_pos]
  push_cast
  rw [Real.norm_of_nonneg]
  · simpa using div_pos hinv (by norm_num : (0 : Real) < 2)
  · simpa using hinv.le

theorem sampledPredictableObservedMixedSquared_sum_tail_exp_neg_budget
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
    mu {sample |
        (arms.card : Real) * (horizon : Real) + Real.sqrt
          (2 * ((((horizon : NNReal) *
            sampledMixedSquaredVarianceProxy arms gamma : NNReal)) : Real) *
              budget) <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample} <=
      ENNReal.ofReal (Real.exp (-budget)) := by
  dsimp only
  let variance : Real := ((((horizon : NNReal) *
    sampledMixedSquaredVarianceProxy arms gamma : NNReal)) : Real)
  let radius : Real := Real.sqrt (2 * variance * budget)
  have hvariance_pos : 0 < variance := by
    change 0 < (horizon : Real) *
      ((sampledMixedSquaredVarianceProxy arms gamma : NNReal) : Real)
    exact mul_pos (by exact_mod_cast hhorizon)
      (sampledMixedSquaredVarianceProxy_pos arms harms gamma hgamma_pos)
  have htail := sampledPredictableObservedMixedSquared_sum_tail_exponential
    prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
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

/-- Delta-shaped exponential confidence bound for the observed finite-horizon
mixed estimator-square sum. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_delta
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
        (arms.card : Real) * (horizon : Real) +
            sampledMixedSquaredConfidenceRadius arms gamma horizon delta <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample} <=
      ENNReal.ofReal delta := by
  dsimp only
  have htail :=
    sampledPredictableObservedMixedSquared_sum_tail_exp_neg_budget
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon hhorizon
        (Real.log (1 / delta))
  have hscale : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hexp : Real.exp (-(Real.log (1 / delta))) = delta := by
    rw [Real.exp_neg, Real.exp_log hscale]
    field_simp
  rw [hexp] at htail
  simpa only [sampledMixedSquaredConfidenceRadius] using htail

end BanditRLProof.Exp3
