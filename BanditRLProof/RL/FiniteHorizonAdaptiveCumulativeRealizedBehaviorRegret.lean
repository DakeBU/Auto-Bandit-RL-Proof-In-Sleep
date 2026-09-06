import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeDecayingExplorationBehaviorConsistency

/-!
# Adaptive finite-window realized behavior regret

This module transports the compiled adaptive exploratory-policy expected-regret
route to realized rewards on the same infinite episode-batch trajectory law.
Successor coordinates `1` through `rounds` are charged; coordinate zero is the
uncontrolled initial batch and is excluded.

Each batch return is centered by the exact history-kernel integral.  The
bounded-reward contract gives the coarse whole-batch Hoeffding proxy
`(episodes * horizon)^2`; this is sufficient for a finite-window realized
average certificate, but it is not the sharper within-batch episode proxy.
The final decaying-exploration theorem unions the existing cumulative-count bad
event with the return-deviation bad event, so its failure budget is two copies
of the scheduled confidence level.  No common probability space across
schedule indices, anytime statement, almost-sure result, or minimax rate is
claimed here.
-/

open MeasureTheory

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace MDP

def traceStateAtFrom (state : State) {n : Nat}
    (trace : StepTrace Action State n) (stage : Fin n) : State :=
  if hzero : stage.val = 0 then state
  else (trace ⟨stage.val - 1, by omega⟩).2

theorem traceStateAtFrom_tail (state : State) {n : Nat}
    (trace : StepTrace Action State (n + 1)) (stage : Fin n) :
    traceStateAtFrom (trace 0).2 (Fin.tail trace) stage =
      traceStateAtFrom state trace stage.succ := by
  cases n with
  | zero => exact Fin.elim0 stage
  | succ n =>
      refine Fin.cases ?_ (fun i => ?_) stage
      · simp [traceStateAtFrom, Fin.tail]
      · simp [traceStateAtFrom, Fin.tail]

theorem cumulativeRewardFrom_eq_sum_traceReward
    (mdp : MDP State Action) (n : Nat) (state : State)
    (trace : StepTrace Action State n) :
    mdp.cumulativeRewardFrom n state trace =
      ∑ stage : Fin n,
        mdp.reward (traceStateAtFrom state trace stage) (trace stage).1 := by
  induction n generalizing state with
  | zero => simp [cumulativeRewardFrom]
  | succ n ih =>
      rw [cumulativeRewardFrom, Fin.sum_univ_succ]
      congr 1
      rw [ih (trace 0).2 (Fin.tail trace)]
      apply Finset.sum_congr rfl
      intro stage _hstage
      rw [traceStateAtFrom_tail state trace stage]
      rfl

end MDP

namespace EpisodeBatch

def episodeReturn {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (episode : Fin episodes) : Real :=
  ∑ stage : Fin mdp.horizon, (batch episode stage).reward

def totalReturn {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) : Real :=
  ∑ episode : Fin episodes, episodeReturn batch episode

theorem measurable_episodeReturn {mdp : MDP State Action} {episodes : Nat}
    (episode : Fin episodes) :
    Measurable (fun batch : EpisodeBatch mdp episodes =>
      episodeReturn batch episode) := by
  refine Finset.measurable_sum Finset.univ fun stage _ => ?_
  exact EpisodeStep.measurable_reward.comp
    ((measurable_pi_apply stage).comp (measurable_pi_apply episode))

theorem measurable_totalReturn {mdp : MDP State Action} {episodes : Nat} :
    Measurable (totalReturn : EpisodeBatch mdp episodes -> Real) := by
  refine Finset.measurable_sum Finset.univ fun episode _ => ?_
  exact measurable_episodeReturn episode

theorem abs_episodeReturn_le_horizon_of_rewardConsistent
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (hbatch : batch.RewardConsistent)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (episode : Fin episodes) :
    |episodeReturn batch episode| <= (mdp.horizon : Real) := by
  calc
    |episodeReturn batch episode| <=
        ∑ stage : Fin mdp.horizon, |(batch episode stage).reward| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _stage : Fin mdp.horizon, (1 : Real) := by
      apply Finset.sum_le_sum
      intro stage _hstage
      rw [hbatch episode stage]
      exact hrewardBound _ _
    _ = (mdp.horizon : Real) := by simp

theorem abs_totalReturn_le_of_rewardConsistent
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (hbatch : batch.RewardConsistent)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    |totalReturn batch| <= (episodes : Real) * (mdp.horizon : Real) := by
  calc
    |totalReturn batch| <=
        ∑ episode : Fin episodes, |episodeReturn batch episode| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _episode : Fin episodes, (mdp.horizon : Real) := by
      apply Finset.sum_le_sum
      intro episode _hepisode
      exact abs_episodeReturn_le_horizon_of_rewardConsistent
        batch hbatch hrewardBound episode
    _ = (episodes : Real) * (mdp.horizon : Real) := by simp

end EpisodeBatch

namespace MDP

theorem episodeReturn_episodeBatchOfTrajectories
    (mdp : MDP State Action) (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon) (episode : Fin episodes) :
    EpisodeBatch.episodeReturn
        (mdp.episodeBatchOfTrajectories episodes trajectories) episode =
      mdp.cumulativeReward (trajectories episode) := by
  rw [cumulativeReward, cumulativeRewardFrom_eq_sum_traceReward]
  apply Finset.sum_congr rfl
  intro stage _hstage
  rfl

theorem totalReturn_episodeBatchOfTrajectories
    (mdp : MDP State Action) (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon) :
    EpisodeBatch.totalReturn
        (mdp.episodeBatchOfTrajectories episodes trajectories) =
      ∑ episode : Fin episodes, mdp.cumulativeReward (trajectories episode) := by
  apply Finset.sum_congr rfl
  intro episode _hepisode
  exact mdp.episodeReturn_episodeBatchOfTrajectories episodes trajectories episode

end MDP

namespace MarkovPolicy

noncomputable def batchReturnVarianceProxy
    (mdp : MDP State Action) (episodes : Nat) : NNReal :=
  Concentration.intervalVarianceProxy
    (-((episodes : Real) * (mdp.horizon : Real)))
    ((episodes : Real) * (mdp.horizon : Real))

theorem integral_cumulativeReward_eval_iidTrajectoryFamilyMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (episode : Fin episodes) :
    (∫ trajectories, mdp.cumulativeReward (trajectories episode)
        ∂policy.iidTrajectoryFamilyMeasure initialState episodes) =
      ∫ trajectory, mdp.cumulativeReward trajectory
        ∂policy.trajectoryMeasure initialState := by
  calc
    (∫ trajectories, mdp.cumulativeReward (trajectories episode)
        ∂policy.iidTrajectoryFamilyMeasure initialState episodes) =
        ∫ trajectory, mdp.cumulativeReward trajectory
          ∂(policy.iidTrajectoryFamilyMeasure initialState episodes).map
            (Function.eval episode) := by
              rw [integral_map (measurable_pi_apply episode).aemeasurable
                mdp.measurable_cumulativeReward.aestronglyMeasurable]
    _ = _ := by rw [policy.iidTrajectoryFamilyMeasure_map_eval initialState episode]

theorem integral_totalReturn_iidEpisodeBatchMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    integral (policy.iidEpisodeBatchMeasure initialState episodes)
        EpisodeBatch.totalReturn =
      (episodes : Real) *
        integral (policy.trajectoryMeasure initialState) mdp.cumulativeReward := by
  unfold iidEpisodeBatchMeasure
  rw [integral_map
    (mdp.measurable_episodeBatchOfTrajectories episodes).aemeasurable
    EpisodeBatch.measurable_totalReturn.aestronglyMeasurable]
  have hint : forall episode : Fin episodes,
      Integrable
        (fun trajectories : Fin episodes ->
          State × StepTrace Action State mdp.horizon =>
            mdp.cumulativeReward (trajectories episode))
        (policy.iidTrajectoryFamilyMeasure initialState episodes) := by
    intro episode
    exact integrable_of_fintype _ _
      (mdp.measurable_cumulativeReward.comp (measurable_pi_apply episode))
  simp_rw [mdp.totalReturn_episodeBatchOfTrajectories]
  rw [integral_finset_sum Finset.univ (fun episode _ => hint episode)]
  simp_rw [policy.integral_cumulativeReward_eval_iidTrajectoryFamilyMeasure
    initialState]
  simp

theorem totalReturn_centered_hasSubgaussianMGF
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun batch : EpisodeBatch mdp episodes =>
        EpisodeBatch.totalReturn batch -
          integral (policy.iidEpisodeBatchMeasure initialState episodes)
            EpisodeBatch.totalReturn)
      (batchReturnVarianceProxy mdp episodes)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  have hbound : ∀ᵐ batch ∂policy.iidEpisodeBatchMeasure initialState episodes,
      Set.Icc
        (-((episodes : Real) * (mdp.horizon : Real)))
        ((episodes : Real) * (mdp.horizon : Real))
        (EpisodeBatch.totalReturn batch) := by
    filter_upwards [policy.iidEpisodeBatchMeasure_rewardConsistent_ae
      initialState episodes] with batch hbatch
    exact abs_le.mp
      (EpisodeBatch.abs_totalReturn_le_of_rewardConsistent
        batch hbatch hrewardBound)
  simpa [batchReturnVarianceProxy] using
    (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (mu := policy.iidEpisodeBatchMeasure initialState episodes)
      (X := EpisodeBatch.totalReturn)
      (mean := integral (policy.iidEpisodeBatchMeasure initialState episodes)
        EpisodeBatch.totalReturn)
      EpisodeBatch.measurable_totalReturn.aemeasurable hbound rfl)

end MarkovPolicy

namespace AdaptiveEpisodeBatchSource

noncomputable def successorReturnKernelMean
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (history : EpisodeBatchPrefix mdp episodes n) : Real :=
  integral (source.batchKernel n history) EpisodeBatch.totalReturn

theorem measurable_successorReturnKernelMean
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) : Measurable (source.successorReturnKernelMean n) := by
  exact EpisodeBatch.measurable_totalReturn.stronglyMeasurable.integral_kernel.measurable

theorem successorReturnKernelMean_eq_selectedPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (history : EpisodeBatchPrefix mdp episodes n) :
    source.successorReturnKernelMean n history =
      (episodes : Real) *
        integral
          ((source.successorPolicy n history).trajectoryMeasure initialState)
          mdp.cumulativeReward := by
  rw [successorReturnKernelMean,
    source.batchKernel_eq_iidEpisodeBatchMeasure]
  exact (source.successorPolicy n history).integral_totalReturn_iidEpisodeBatchMeasure
    initialState episodes

noncomputable def successorReturnPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes) :
    (round : Nat) -> EpisodeBatchPrefix mdp episodes round -> Real
  | 0, _history => 0
  | n + 1, history =>
      EpisodeBatch.totalReturn
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) -
        source.successorReturnKernelMean n
          (Preorder.frestrictLe₂
            (π := fun _ : Nat => EpisodeBatch mdp episodes)
            (Nat.le_succ n) history)

theorem measurable_successorReturnPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (round : Nat) :
    Measurable (source.successorReturnPrefixIncrement round) := by
  cases round with
  | zero =>
      simpa only [successorReturnPrefixIncrement] using
        (measurable_const : Measurable
          (fun _ : EpisodeBatchPrefix mdp episodes 0 => (0 : Real)))
  | succ n =>
      simpa [successorReturnPrefixIncrement] using
        ((EpisodeBatch.measurable_totalReturn.comp (measurable_pi_apply
          (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1)))).sub
          ((source.measurable_successorReturnKernelMean n).comp
            (Preorder.measurable_frestrictLe₂
              (X := fun _ : Nat => EpisodeBatch mdp episodes)
              (Nat.le_succ n))))

noncomputable def successorReturnIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (round : Nat) (trajectory : EpisodeBatchTrajectory mdp episodes) : Real :=
  source.successorReturnPrefixIncrement round
    (Preorder.frestrictLe round trajectory)

theorem successorReturnIncrement_stronglyAdapted_piLE
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes) :
    StronglyAdapted
      (Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes))
      source.successorReturnIncrement := by
  intro round
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact ((source.measurable_successorReturnPrefixIncrement round).comp
    (Measurable.of_comap_le le_rfl)).stronglyMeasurable

theorem trajectoryMeasure_condDistrib_totalReturn
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
          EpisodeBatch.totalReturn (trajectory (n + 1)))
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      (source.batchKernel n).map EpisodeBatch.totalReturn := by
  letI : ProbabilityTheory.IsMarkovKernel (source.batchKernel n) :=
    source.batchKernel_isMarkov n
  have hcomp :
      ProbabilityTheory.condDistrib
          (EpisodeBatch.totalReturn ∘
            (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
              trajectory (n + 1)))
          (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
            source.trajectoryMeasure.map (Preorder.frestrictLe n)]
        (ProbabilityTheory.condDistrib
          (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
            trajectory (n + 1))
          (Preorder.frestrictLe n) source.trajectoryMeasure).map
            EpisodeBatch.totalReturn :=
    ProbabilityTheory.condDistrib_comp
      (μ := source.trajectoryMeasure)
      (Preorder.frestrictLe n)
      (measurable_pi_apply (n + 1)).aemeasurable
      EpisodeBatch.measurable_totalReturn
  filter_upwards [hcomp, source.trajectoryMeasure_condDistrib n] with history hc hk
  have hmap :
      ((ProbabilityTheory.condDistrib
          (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
            trajectory (n + 1))
          (Preorder.frestrictLe n) source.trajectoryMeasure).map
            EpisodeBatch.totalReturn) history =
        ((source.batchKernel n).map EpisodeBatch.totalReturn) history := by
    rw [ProbabilityTheory.Kernel.map_apply _ EpisodeBatch.measurable_totalReturn,
      ProbabilityTheory.Kernel.map_apply _ EpisodeBatch.measurable_totalReturn, hk]
  simpa only [Function.comp_def] using hc.trans hmap

theorem condExpKernel_map_totalReturn_eq_batchKernel
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    Filter.Eventually
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        Measure.map
            (fun path : EpisodeBatchTrajectory mdp episodes =>
              EpisodeBatch.totalReturn (path (n + 1)))
            (ProbabilityTheory.condExpKernel source.trajectoryMeasure
              ((inferInstance : MeasurableSpace
                (EpisodeBatchPrefix mdp episodes n)).comap
                  (Preorder.frestrictLe n)) trajectory) =
          ((source.batchKernel n).map EpisodeBatch.totalReturn)
            (Preorder.frestrictLe n trajectory))
      (ae (source.trajectoryMeasure.trim
        (Preorder.measurable_frestrictLe n).comap_le)) := by
  letI : Nonempty (EpisodeBatchTrajectory mdp episodes) :=
    MeasureTheory.nonempty_of_isProbabilityMeasure source.trajectoryMeasure
  letI : ProbabilityTheory.IsMarkovKernel (source.batchKernel n) :=
    source.batchKernel_isMarkov n
  letI : ProbabilityTheory.IsMarkovKernel
      ((source.batchKernel n).map EpisodeBatch.totalReturn) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map
      (source.batchKernel n) EpisodeBatch.measurable_totalReturn
  exact
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      source.trajectoryMeasure
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        EpisodeBatch.totalReturn (trajectory (n + 1)))
      (Preorder.frestrictLe n)
      (EpisodeBatch.measurable_totalReturn.comp (measurable_pi_apply (n + 1)))
      (Preorder.measurable_frestrictLe n)
      ((source.batchKernel n).map EpisodeBatch.totalReturn)
      (source.trajectoryMeasure_condDistrib_totalReturn n)

theorem successorReturnIncrement_succ_hasCondSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes) n)
      ((Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes)).le n)
      (source.successorReturnIncrement (n + 1))
      (MarkovPolicy.batchReturnVarianceProxy mdp episodes)
      source.trajectoryMeasure := by
  let prefixMap : EpisodeBatchTrajectory mdp episodes ->
      EpisodeBatchPrefix mdp episodes n := Preorder.frestrictLe n
  let X : EpisodeBatchTrajectory mdp episodes -> Real := fun trajectory =>
    EpisodeBatch.totalReturn (trajectory (n + 1))
  let center : EpisodeBatchTrajectory mdp episodes -> Real := fun trajectory =>
    source.successorReturnKernelMean n (prefixMap trajectory)
  let target : EpisodeBatchTrajectory mdp episodes -> Measure Real := fun trajectory =>
    ((source.batchKernel n).map EpisodeBatch.totalReturn) (prefixMap trajectory)
  have hspace :
      Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes) n =
        (inferInstance : MeasurableSpace (EpisodeBatchPrefix mdp episodes n)).comap
          prefixMap := by
    simpa [prefixMap] using
      (Filtration.piLE_eq_comap_frestrictLe
        (X := fun _ : Nat => EpisodeBatch mdp episodes) n)
  have hX : Measurable X :=
    EpisodeBatch.measurable_totalReturn.comp (measurable_pi_apply (n + 1))
  let mcond : MeasurableSpace (EpisodeBatchTrajectory mdp episodes) :=
    (inferInstance : MeasurableSpace (EpisodeBatchPrefix mdp episodes n)).comap
      prefixMap
  have hmcond : mcond <= MeasurableSpace.pi := by
    simpa [mcond, prefixMap] using
      (Preorder.measurable_frestrictLe
        (X := fun _ : Nat => EpisodeBatch mdp episodes) n).comap_le
  have hcenter : @Measurable (EpisodeBatchTrajectory mdp episodes) Real
      mcond inferInstance center := by
    exact (source.measurable_successorReturnKernelMean n).comp
      (Measurable.of_comap_le le_rfl)
  have hkernel : Filter.Eventually
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        @Measure.map (EpisodeBatchTrajectory mdp episodes) Real
            MeasurableSpace.pi inferInstance X
            ((@ProbabilityTheory.condExpKernel
              (EpisodeBatchTrajectory mdp episodes)
              MeasurableSpace.pi _
              source.trajectoryMeasure _ mcond) trajectory) =
          target trajectory)
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    simpa [X, target, prefixMap, mcond] using
      source.condExpKernel_map_totalReturn_eq_batchKernel n
  have htarget : Filter.Eventually
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        ProbabilityTheory.HasSubgaussianMGF
          (fun z : Real => z - center trajectory)
          (MarkovPolicy.batchReturnVarianceProxy mdp episodes)
          (target trajectory))
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := prefixMap trajectory
      let policy := source.successorPolicy n history
      have hbatch := policy.totalReturn_centered_hasSubgaussianMGF
        initialState episodes hrewardBound
      have hid :=
        (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
          (EpisodeBatch.measurable_totalReturn.sub_const
            (integral (policy.iidEpisodeBatchMeasure initialState episodes)
              EpisodeBatch.totalReturn)).aemeasurable).2 hbatch
      change ProbabilityTheory.HasSubgaussianMGF
        (fun z : Real => z - source.successorReturnKernelMean n history)
        (MarkovPolicy.batchReturnVarianceProxy mdp episodes)
        (((source.batchKernel n).map EpisodeBatch.totalReturn) history)
      rw [ProbabilityTheory.Kernel.map_apply _ EpisodeBatch.measurable_totalReturn,
        source.batchKernel_eq_iidEpisodeBatchMeasure n history]
      change ProbabilityTheory.HasSubgaussianMGF
        (fun z : Real => z - source.successorReturnKernelMean n history)
        (MarkovPolicy.batchReturnVarianceProxy mdp episodes)
        ((policy.iidEpisodeBatchMeasure initialState episodes).map
          EpisodeBatch.totalReturn)
      apply (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
        (measurable_id.sub_const
          (source.successorReturnKernelMean n history)).aemeasurable).1
      rw [Measure.map_map
        (measurable_id.sub_const (source.successorReturnKernelMean n history))
        EpisodeBatch.measurable_totalReturn]
      have hmean : source.successorReturnKernelMean n history =
          integral (policy.iidEpisodeBatchMeasure initialState episodes)
            EpisodeBatch.totalReturn := by
        rw [successorReturnKernelMean,
          source.batchKernel_eq_iidEpisodeBatchMeasure]
      rw [hmean]
      simpa only [Function.comp_def] using hid
  have hcondComap :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure
      mcond hmcond X center (MarkovPolicy.batchReturnVarianceProxy mdp episodes)
      hX hcenter target hkernel htarget
  have hcond :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_congr_measurableSpace
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond
      (Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes) n)
      hmcond
      ((Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes)).le n)
      hspace.symm
      (fun trajectory => X trajectory - center trajectory)
      (MarkovPolicy.batchReturnVarianceProxy mdp episodes) hcondComap
  simpa [successorReturnIncrement, successorReturnPrefixIncrement, X, center,
    prefixMap, Preorder.frestrictLe_apply, Preorder.frestrictLe₂_apply] using hcond

noncomputable def cumulativeSuccessorReturnVarianceProxy
    (mdp : MDP State Action) (episodes rounds : Nat) : NNReal :=
  ∑ t ∈ Finset.range (rounds + 1),
    match t with
    | 0 => 0
    | _ + 1 => MarkovPolicy.batchReturnVarianceProxy mdp episodes

noncomputable def cumulativeSuccessorReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (trajectory : EpisodeBatchTrajectory mdp episodes) : Real :=
  ∑ t ∈ Finset.range (rounds + 1), source.successorReturnIncrement t trajectory

theorem batchReturnVarianceProxy_pos
    (mdp : MDP State Action) (episodes : Nat)
    (hepisodes : 0 < episodes) (hhorizon : 0 < mdp.horizon) :
    0 < MarkovPolicy.batchReturnVarianceProxy mdp episodes := by
  have hbound : 0 < (episodes : Real) * (mdp.horizon : Real) := by
    positivity
  simp only [MarkovPolicy.batchReturnVarianceProxy,
    Concentration.intervalVarianceProxy]
  rw [show -((episodes : Real) * (mdp.horizon : Real)) |>
      fun lo => ((episodes : Real) * (mdp.horizon : Real)) - lo =
        2 * ((episodes : Real) * (mdp.horizon : Real)) by ring]
  have hnorm :
      0 < ‖2 * ((episodes : Real) * (mdp.horizon : Real))‖₊ :=
    nnnorm_pos.mpr (mul_ne_zero (by norm_num) (ne_of_gt hbound))
  exact pow_pos (div_pos hnorm (by norm_num)) 2

theorem trajectoryMeasure_cumulativeSuccessorReturnDeviation_abs_tail_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hhorizon : 0 < mdp.horizon)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    source.trajectoryMeasure
        {trajectory |
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds) delta <=
            |source.cumulativeSuccessorReturnDeviation rounds trajectory|} <=
      ENNReal.ofReal delta := by
  let F := Filtration.piLE
    (X := fun _ : Nat => EpisodeBatch mdp episodes)
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | _ + 1 => MarkovPolicy.batchReturnVarianceProxy mdp episodes
  have hadapted : StronglyAdapted F source.successorReturnIncrement := by
    simpa [F] using source.successorReturnIncrement_stronglyAdapted_piLE
  have hzero : ProbabilityTheory.HasSubgaussianMGF
      (source.successorReturnIncrement 0) (cY 0) source.trajectoryMeasure := by
    change ProbabilityTheory.HasSubgaussianMGF
      (fun _ => 0) 0 source.trajectoryMeasure
    exact ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have hsucc : forall i, i < (rounds + 1) - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (source.successorReturnIncrement (i + 1))
        (cY (i + 1)) source.trajectoryMeasure := by
    intro i _hi
    simpa [F, cY] using
      source.successorReturnIncrement_succ_hasCondSubgaussianMGF i hrewardBound
  have hvariance :
      0 < ((((Finset.range (rounds + 1)).sum cY : NNReal) : Real)) := by
    have hproxy := batchReturnVarianceProxy_pos mdp episodes hepisodes hhorizon
    have hmem : 1 ∈ Finset.range (rounds + 1) := Finset.mem_range.mpr (by omega)
    exact_mod_cast Finset.sum_pos' (fun _ _ => zero_le _)
      ⟨1, hmem, by simpa [cY] using hproxy⟩
  simpa [cumulativeSuccessorReturnVarianceProxy,
    cumulativeSuccessorReturnDeviation, cY] using
    (Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
      hadapted hzero (rounds + 1) hsucc hvariance delta hdelta hdelta_le_one)

noncomputable def optimalInitialExpectedReturn
    (mdp : MDP State Action) (initialState : Measure State) : Real :=
  integral initialState
    (mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon))

noncomputable def successorExpectedCumulativeRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    (source.policyAt trajectory ((round : Nat) + 1)).expectedRegret initialState

noncomputable def successorExpectedAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) : Real :=
  source.successorExpectedCumulativeRegret trajectory rounds / (rounds : Real)

noncomputable def realizedSuccessorCumulativeRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    ((episodes : Real) * optimalInitialExpectedReturn mdp initialState -
      EpisodeBatch.totalReturn (trajectory ((round : Nat) + 1)))

noncomputable def realizedSuccessorAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) : Real :=
  source.realizedSuccessorCumulativeRegret trajectory rounds /
    ((episodes : Real) * (rounds : Real))

noncomputable def successorReturnDeviationBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (delta : Real) :
    Set (EpisodeBatchTrajectory mdp episodes) :=
  {trajectory |
    Concentration.subGaussianSumConfidenceRadius
        (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds) delta <=
      |source.cumulativeSuccessorReturnDeviation rounds trajectory|}

theorem measurable_cumulativeSuccessorReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) :
    Measurable (source.cumulativeSuccessorReturnDeviation rounds) := by
  refine Finset.measurable_sum (Finset.range (rounds + 1)) fun t _ => ?_
  exact (((source.successorReturnIncrement_stronglyAdapted_piLE t).mono
    ((Filtration.piLE
      (X := fun _ : Nat => EpisodeBatch mdp episodes)).le t)).measurable)

theorem measurableSet_successorReturnDeviationBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (delta : Real) :
    MeasurableSet (source.successorReturnDeviationBadEvent rounds delta) := by
  exact measurableSet_le measurable_const
    (source.measurable_cumulativeSuccessorReturnDeviation rounds).abs

theorem successorReturnIncrement_succ_eq_totalReturn_sub_selectedPolicyMean
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (n : Nat) :
    source.successorReturnIncrement (n + 1) trajectory =
      EpisodeBatch.totalReturn (trajectory (n + 1)) -
        (episodes : Real) *
          integral
            ((source.policyAt trajectory (n + 1)).trajectoryMeasure initialState)
            mdp.cumulativeReward := by
  simp only [successorReturnIncrement, successorReturnPrefixIncrement,
    Preorder.frestrictLe_apply, Preorder.frestrictLe₂_apply]
  rw [source.successorReturnKernelMean_eq_selectedPolicy]
  rfl

theorem cumulativeSuccessorReturnDeviation_eq_fin_sum
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    source.cumulativeSuccessorReturnDeviation rounds trajectory =
      ∑ round : Fin rounds,
        source.successorReturnIncrement ((round : Nat) + 1) trajectory := by
  unfold cumulativeSuccessorReturnDeviation
  rw [Finset.sum_range_succ']
  simp only [successorReturnIncrement, successorReturnPrefixIncrement, add_zero]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro round hround
  have hround_lt : round < rounds := Finset.mem_range.mp hround
  rw [dif_pos hround_lt]

theorem realizedSuccessorCumulativeRegret_eq_expected_sub_deviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    source.realizedSuccessorCumulativeRegret trajectory rounds =
      (episodes : Real) * source.successorExpectedCumulativeRegret trajectory rounds -
        source.cumulativeSuccessorReturnDeviation rounds trajectory := by
  rw [cumulativeSuccessorReturnDeviation_eq_fin_sum]
  unfold realizedSuccessorCumulativeRegret successorExpectedCumulativeRegret
  calc
    (∑ round : Fin rounds,
        ((episodes : Real) * optimalInitialExpectedReturn mdp initialState -
          EpisodeBatch.totalReturn (trajectory ((round : Nat) + 1)))) =
        ∑ round : Fin rounds,
          ((episodes : Real) *
              (source.policyAt trajectory ((round : Nat) + 1)).expectedRegret
                initialState -
            source.successorReturnIncrement ((round : Nat) + 1) trajectory) := by
      apply Finset.sum_congr rfl
      intro round _hround
      rw [source.successorReturnIncrement_succ_eq_totalReturn_sub_selectedPolicyMean]
      unfold MarkovPolicy.expectedRegret optimalInitialExpectedReturn
      ring
    _ = (episodes : Real) *
          (∑ round : Fin rounds,
            (source.policyAt trajectory ((round : Nat) + 1)).expectedRegret
              initialState) -
        ∑ round : Fin rounds,
          source.successorReturnIncrement ((round : Nat) + 1) trajectory := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem realizedSuccessorAverageRegret_eq_expected_sub_deviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) :
    source.realizedSuccessorAverageRegret trajectory rounds =
      source.successorExpectedAverageRegret trajectory rounds -
        source.cumulativeSuccessorReturnDeviation rounds trajectory /
          ((episodes : Real) * (rounds : Real)) := by
  have hroundsReal : (rounds : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hrounds)
  have hepisodesReal : (episodes : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hepisodes)
  rw [realizedSuccessorAverageRegret, successorExpectedAverageRegret,
    source.realizedSuccessorCumulativeRegret_eq_expected_sub_deviation]
  field_simp

theorem trajectoryMeasure_successorReturnDeviationBadEvent_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hhorizon : 0 < mdp.horizon)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    source.trajectoryMeasure
        (source.successorReturnDeviationBadEvent rounds delta) <=
      ENNReal.ofReal delta := by
  simpa only [successorReturnDeviationBadEvent] using
    source.trajectoryMeasure_cumulativeSuccessorReturnDeviation_abs_tail_le
      rounds hrounds hepisodes hhorizon hrewardBound delta hdelta hdelta_le_one

theorem trajectoryMeasure_expected_to_realized_successor_average_regret_transport
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hhorizon : 0 < mdp.horizon)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (countBadEvent : Set (EpisodeBatchTrajectory mdp episodes))
    (expectedBound : Real)
    (Good : EpisodeBatchTrajectory mdp episodes -> Prop)
    (hcountMeasurable : MeasurableSet countBadEvent)
    (hcountTail : source.trajectoryMeasure countBadEvent <= ENNReal.ofReal delta)
    (hcountGood : forall trajectory, trajectory ∉ countBadEvent ->
      Good trajectory /\
        source.successorExpectedAverageRegret trajectory rounds <= expectedBound) :
    let returnBadEvent := source.successorReturnDeviationBadEvent rounds delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        ENNReal.ofReal delta + ENNReal.ofReal delta /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        Good trajectory /\
          source.realizedSuccessorAverageRegret trajectory rounds <=
            expectedBound +
              Concentration.subGaussianSumConfidenceRadius
                  (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds) delta /
                ((episodes : Real) * (rounds : Real)) := by
  let returnBadEvent := source.successorReturnDeviationBadEvent rounds delta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  have hreturnMeasurable : MeasurableSet returnBadEvent := by
    simpa [returnBadEvent] using
      source.measurableSet_successorReturnDeviationBadEvent rounds delta
  have hreturnTail : source.trajectoryMeasure returnBadEvent <= ENNReal.ofReal delta := by
    simpa [returnBadEvent] using
      source.trajectoryMeasure_successorReturnDeviationBadEvent_le
        rounds hrounds hepisodes hhorizon hrewardBound delta hdelta hdelta_le_one
  refine ⟨hcountMeasurable.union hreturnMeasurable, ?_, ?_⟩
  · exact (measure_union_le countBadEvent returnBadEvent).trans
      (add_le_add hcountTail hreturnTail)
  · intro trajectory htrajectory
    have hnotCount : trajectory ∉ countBadEvent := by
      exact fun hmem => htrajectory (Set.mem_union_left returnBadEvent hmem)
    have hnotReturn : trajectory ∉ returnBadEvent := by
      exact fun hmem => htrajectory (Set.mem_union_right countBadEvent hmem)
    have hgood := hcountGood trajectory hnotCount
    refine ⟨hgood.1, ?_⟩
    have hdeviation :
        |source.cumulativeSuccessorReturnDeviation rounds trajectory| <
          Concentration.subGaussianSumConfidenceRadius
            (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds) delta := by
      exact lt_of_not_ge (by simpa [returnBadEvent,
        successorReturnDeviationBadEvent] using hnotReturn)
    have hdenom : 0 < (episodes : Real) * (rounds : Real) := by
      positivity
    rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
      trajectory rounds hrounds hepisodes]
    have hnoise :
        -source.cumulativeSuccessorReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) <=
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds) delta /
            ((episodes : Real) * (rounds : Real)) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      exact (neg_le_abs _).trans hdeviation.le
    calc
      source.successorExpectedAverageRegret trajectory rounds -
          source.cumulativeSuccessorReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) =
        source.successorExpectedAverageRegret trajectory rounds +
          (-source.cumulativeSuccessorReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real))) := by ring
      _ <= source.successorExpectedAverageRegret trajectory rounds +
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds) delta /
            ((episodes : Real) * (rounds : Real)) := add_le_add le_rfl hnoise
      _ <= expectedBound +
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds) delta /
            ((episodes : Real) * (rounds : Real)) := add_le_add hgood.2 le_rfl

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

theorem exploratorySource_successorExpectedCumulativeRegret_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    (exploratorySource mdp initialState episodes initialTable defaultState
      countRadius explorationRate hexplorationRate).successorExpectedCumulativeRegret
        trajectory rounds =
      adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
        (initialState := initialState) trajectory defaultState countRadius
        explorationRate hexplorationRate rounds := by
  unfold AdaptiveEpisodeBatchSource.successorExpectedCumulativeRegret
    adaptiveCumulativeEmpiricalOptimisticExploratoryBehaviorExpectedRegret
  apply Finset.sum_congr rfl
  intro round _hround
  rw [exploratorySource_policyAt_succ_eq_cumulativeOptimisticExploratoryPolicy]

theorem exploratorySource_successorExpectedAverageRegret_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    (exploratorySource mdp initialState episodes initialTable defaultState
      countRadius explorationRate hexplorationRate).successorExpectedAverageRegret
        trajectory rounds =
      adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
        (initialState := initialState) trajectory defaultState countRadius
        explorationRate hexplorationRate rounds := by
  unfold AdaptiveEpisodeBatchSource.successorExpectedAverageRegret
    adaptiveCumulativeEmpiricalOptimisticAverageExploratoryBehaviorExpectedRegret
  rw [exploratorySource_successorExpectedCumulativeRegret_eq]

theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real) (n : Nat)
    [StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
    let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
    let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
    let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
      mdp baseVisitFloor n
    let episodes :=
      AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n
    let countRadius :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
        mdp rounds delta visitFloor
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
    let countBadEvent := source.adaptiveCumulativeCountBadEvent rounds delta
    let returnBadEvent := source.successorReturnDeviationBadEvent rounds delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        ENNReal.ofReal delta + ENNReal.ofReal delta /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        source.realizedSuccessorAverageRegret trajectory rounds <=
          AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
              mdp baseVisitFloor n +
            Concentration.subGaussianSumConfidenceRadius
                (AdaptiveEpisodeBatchSource.cumulativeSuccessorReturnVarianceProxy
                  mdp episodes rounds) delta /
              ((episodes : Real) * (rounds : Real)) := by
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
  let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
    mdp baseVisitFloor n
  let episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    mdp baseVisitFloor n
  let countRadius :=
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
      mdp rounds delta visitFloor
  let source := exploratorySource mdp initialState episodes initialTable
    defaultState countRadius explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
  let countBadEvent := source.adaptiveCumulativeCountBadEvent rounds delta
  let returnBadEvent := source.successorReturnDeviationBadEvent rounds delta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  let Good : EpisodeBatchTrajectory mdp episodes -> Prop := fun trajectory =>
    forall round : Fin rounds, forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        (adaptiveCumulativeEmpiricalOptimisticPlanAt
          trajectory defaultState countRadius round).upperValueRemaining
            mdp.horizon le_rfl state
  have hparent :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
      mdp initialState baseVisitFloor n initialTable defaultState support
      hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hparent
  rcases hparent with ⟨hcountMeasurable, hcountTail, _hsubset,
    _hviolationTail, houtside⟩
  have hrounds : 0 < rounds :=
    AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  have hepisodes : 0 < episodes := by
    unfold episodes AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    exact AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes_pos
      mdp (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
        (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor mdp baseVisitFloor n)
  have hcountGood : forall trajectory, trajectory ∉ countBadEvent ->
      Good trajectory /\
        source.successorExpectedAverageRegret trajectory rounds <=
          AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
            mdp baseVisitFloor n := by
    intro trajectory htrajectory
    have hgood := houtside trajectory htrajectory
    refine ⟨hgood.1, ?_⟩
    rw [exploratorySource_successorExpectedAverageRegret_eq]
    exact hgood.2
  have htransport :=
    source.trajectoryMeasure_expected_to_realized_successor_average_regret_transport
      rounds hrounds hepisodes hhorizon hrewardBound delta
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
      countBadEvent
      (AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
        mdp baseVisitFloor n)
      Good hcountMeasurable hcountTail hcountGood
  simpa [returnBadEvent, combinedBadEvent, Good] using htransport

end AdaptiveCumulativeEmpiricalOptimisticSource
end BanditRLProof.FiniteHorizonRL
