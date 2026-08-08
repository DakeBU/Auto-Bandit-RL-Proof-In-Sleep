import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeDecayingExplorationRealizedBehaviorConsistency

/-!
# Episodewise adaptive realized behavior consistency

This module sharpens the finite-window realized-return route by preserving the
iid structure inside each generated batch.  Complete episodes are independent;
stages inside one episode are not.  Centering one bounded full-episode return at
a time gives the batch proxy `episodes * horizon^2`, replacing the coarse
whole-batch proxy `(episodes * horizon)^2`.

The sharper batch MGF is transported through the existing adaptive successor
conditional law and strongly-adapted finite-sum concentration route.  The
terminal theorem remains an indexed family of finite-window certificates over
changing batch and trajectory spaces, not a common-process convergence result.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace EpisodeBatch

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A complete episode row is a measurable coordinate of a finite batch. -/
theorem measurable_episode
    {mdp : MDP State Action} {episodes : Nat} (episode : Fin episodes) :
    Measurable (fun batch : EpisodeBatch mdp episodes => batch episode) := by
  exact measurable_pi_lambda _ fun stage =>
    (measurable_pi_apply stage).comp (measurable_pi_apply episode)

end EpisodeBatch

namespace MarkovPolicy

/-- Complete generated episode rows are independent product coordinates. -/
theorem iIndepFun_episodeRowOfTrajectory
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    ProbabilityTheory.iIndepFun
      (fun episode trajectories => fun stage =>
        mdp.episodeStepOfTrajectory (trajectories episode) stage)
      (policy.iidTrajectoryFamilyMeasure initialState episodes) := by
  unfold iidTrajectoryFamilyMeasure
  exact ProbabilityTheory.iIndepFun_pi fun _episode =>
    (measurable_pi_lambda _ fun stage =>
      mdp.measurable_episodeStepOfTrajectory stage).aemeasurable

/-- Complete episode rows remain independent after mapping trajectories to a batch. -/
theorem iIndepFun_iidEpisodeBatch_episode
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    ProbabilityTheory.iIndepFun
      (fun episode (batch : EpisodeBatch mdp episodes) => batch episode)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  have hbatch : Measurable (mdp.episodeBatchOfTrajectories episodes) :=
    mdp.measurable_episodeBatchOfTrajectories episodes
  have hbatchCoordinates : Measurable
      (fun batch : EpisodeBatch mdp episodes => fun episode => batch episode) :=
    measurable_pi_lambda _ fun episode => EpisodeBatch.measurable_episode episode
  have hbatchCoordinate : forall episode : Fin episodes,
      Measurable (fun batch : EpisodeBatch mdp episodes => batch episode) :=
    EpisodeBatch.measurable_episode
  have hsource := policy.iIndepFun_episodeRowOfTrajectory initialState episodes
  have hsourceEq :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun episode =>
        ((measurable_pi_lambda _ fun stage =>
          mdp.measurable_episodeStepOfTrajectory stage).comp
            (measurable_pi_apply episode)).aemeasurable)).1 hsource
  have hsourceEq' :
      (policy.iidTrajectoryFamilyMeasure initialState episodes).map
          (fun trajectories episode => fun stage =>
            mdp.episodeStepOfTrajectory (trajectories episode) stage) =
        Measure.pi fun episode =>
          (policy.iidTrajectoryFamilyMeasure initialState episodes).map
            (fun trajectories => fun stage =>
              mdp.episodeStepOfTrajectory (trajectories episode) stage) := by
    simpa only [Function.comp_apply] using hsourceEq
  apply
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun episode => (hbatchCoordinate episode).aemeasurable)).2
  unfold iidEpisodeBatchMeasure
  rw [Measure.map_map hbatchCoordinates hbatch]
  rw [show
      (fun batch : EpisodeBatch mdp episodes => fun episode => batch episode) ∘
          mdp.episodeBatchOfTrajectories episodes =
        (fun trajectories episode => fun stage =>
          mdp.episodeStepOfTrajectory (trajectories episode) stage) by rfl]
  rw [hsourceEq']
  congr 1
  funext episode
  rw [Measure.map_map (hbatchCoordinate episode) hbatch]
  rfl

/-- Full episode returns are independent across iid batch coordinates. -/
theorem iIndepFun_iidEpisodeBatch_episodeReturn
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    ProbabilityTheory.iIndepFun
      (fun episode (batch : EpisodeBatch mdp episodes) =>
        EpisodeBatch.episodeReturn batch episode)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  simpa [Function.comp_def, EpisodeBatch.episodeReturn] using
    (policy.iIndepFun_iidEpisodeBatch_episode initialState episodes).comp
      (fun _episode row => ∑ stage : Fin mdp.horizon, (row stage).reward)
      (fun _episode => Finset.measurable_sum Finset.univ fun stage _ =>
        EpisodeStep.measurable_reward.comp (measurable_pi_apply stage))

/-- Every episode return in an iid batch has the common trajectory-return mean. -/
theorem integral_episodeReturn_iidEpisodeBatchMeasure
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (episode : Fin episodes) :
    integral (policy.iidEpisodeBatchMeasure initialState episodes)
        (fun batch => EpisodeBatch.episodeReturn batch episode) =
      integral (policy.trajectoryMeasure initialState) mdp.cumulativeReward := by
  unfold iidEpisodeBatchMeasure
  rw [integral_map
    (mdp.measurable_episodeBatchOfTrajectories episodes).aemeasurable
    (EpisodeBatch.measurable_episodeReturn episode).aestronglyMeasurable]
  simpa only [mdp.episodeReturn_episodeBatchOfTrajectories] using
    policy.integral_cumulativeReward_eval_iidTrajectoryFamilyMeasure
      initialState episode

/-- One full episode's bounded-return Hoeffding proxy. -/
noncomputable def episodeReturnVarianceProxy
    (mdp : MDP State Action) : NNReal :=
  Concentration.intervalVarianceProxy
    (-((mdp.horizon : Nat) : Real)) ((mdp.horizon : Nat) : Real)

/-- Each bounded centered episode return is sub-Gaussian with proxy `horizon^2`. -/
theorem episodeReturn_centered_hasSubgaussianMGF
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (episode : Fin episodes)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun batch : EpisodeBatch mdp episodes =>
        EpisodeBatch.episodeReturn batch episode -
          integral (policy.trajectoryMeasure initialState) mdp.cumulativeReward)
      (episodeReturnVarianceProxy mdp)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  have hbound : ∀ᵐ batch ∂policy.iidEpisodeBatchMeasure initialState episodes,
      Set.Icc (-((mdp.horizon : Nat) : Real)) ((mdp.horizon : Nat) : Real)
        (EpisodeBatch.episodeReturn batch episode) := by
    filter_upwards [policy.iidEpisodeBatchMeasure_rewardConsistent_ae
      initialState episodes] with batch hbatch
    exact abs_le.mp
      (EpisodeBatch.abs_episodeReturn_le_horizon_of_rewardConsistent
        batch hbatch hrewardBound episode)
  have hmean := policy.integral_episodeReturn_iidEpisodeBatchMeasure
    initialState episode
  simpa [episodeReturnVarianceProxy, hmean] using
    (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (mu := policy.iidEpisodeBatchMeasure initialState episodes)
      (X := fun batch => EpisodeBatch.episodeReturn batch episode)
      (mean := integral (policy.trajectoryMeasure initialState)
        mdp.cumulativeReward)
      (EpisodeBatch.measurable_episodeReturn episode).aemeasurable hbound hmean)

/-- Sum of the independent full-episode return proxies in one batch. -/
noncomputable def episodewiseBatchReturnVarianceProxy
    (mdp : MDP State Action) (episodes : Nat) : NNReal :=
  ∑ _episode : Fin episodes, episodeReturnVarianceProxy mdp

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem episodeReturnVarianceProxy_coe (mdp : MDP State Action) :
    ((episodeReturnVarianceProxy mdp : NNReal) : Real) =
      ((mdp.horizon : Nat) : Real) ^ 2 := by
  simp only [episodeReturnVarianceProxy, Concentration.intervalVarianceProxy,
    NNReal.coe_pow, NNReal.coe_div, coe_nnnorm]
  norm_num
  rw [abs_of_nonneg (by positivity)]
  ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem episodewiseBatchReturnVarianceProxy_coe
    (mdp : MDP State Action) (episodes : Nat) :
    ((episodewiseBatchReturnVarianceProxy mdp episodes : NNReal) : Real) =
      (episodes : Real) * ((mdp.horizon : Nat) : Real) ^ 2 := by
  simp [episodewiseBatchReturnVarianceProxy, episodeReturnVarianceProxy_coe]

/-- The centered total batch return has the sharp episodewise proxy. -/
theorem totalReturn_centered_episodewise_hasSubgaussianMGF
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun batch : EpisodeBatch mdp episodes =>
        EpisodeBatch.totalReturn batch -
          integral (policy.iidEpisodeBatchMeasure initialState episodes)
            EpisodeBatch.totalReturn)
      (episodewiseBatchReturnVarianceProxy mdp episodes)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  let mean := integral (policy.trajectoryMeasure initialState) mdp.cumulativeReward
  let X : Fin episodes -> EpisodeBatch mdp episodes -> Real := fun episode batch =>
    EpisodeBatch.episodeReturn batch episode - mean
  have hindep : ProbabilityTheory.iIndepFun X
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
    exact (policy.iIndepFun_iidEpisodeBatch_episodeReturn initialState episodes).comp
      (fun _episode value => value - mean)
      (fun _episode => measurable_id.sub_const mean)
  have hsubG : forall episode : Fin episodes,
      ProbabilityTheory.HasSubgaussianMGF (X episode)
        (episodeReturnVarianceProxy mdp)
        (policy.iidEpisodeBatchMeasure initialState episodes) := by
    intro episode
    simpa [X, mean] using
      policy.episodeReturn_centered_hasSubgaussianMGF
        initialState episode hrewardBound
  have hsum :=
    ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
      (s := (Finset.univ : Finset (Fin episodes))) hindep
      (c := fun _episode => episodeReturnVarianceProxy mdp)
      (fun episode _ => hsubG episode)
  have hmean :
      integral (policy.iidEpisodeBatchMeasure initialState episodes)
          EpisodeBatch.totalReturn =
        (episodes : Real) * mean := by
    simpa [mean] using
      policy.integral_totalReturn_iidEpisodeBatchMeasure initialState episodes
  rw [hmean]
  simpa [X, mean, EpisodeBatch.totalReturn,
    episodewiseBatchReturnVarianceProxy,
    Finset.sum_sub_distrib] using hsum

end MarkovPolicy

namespace AdaptiveEpisodeBatchSource

/-- The successor batch increment inherits the sharp episodewise batch proxy. -/
theorem successorReturnIncrement_succ_episodewise_hasCondSubgaussianMGF
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
      (MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes)
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
          (MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes)
          (target trajectory))
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := prefixMap trajectory
      let policy := source.successorPolicy n history
      have hbatch := policy.totalReturn_centered_episodewise_hasSubgaussianMGF
        initialState episodes hrewardBound
      have hid :=
        (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
          (EpisodeBatch.measurable_totalReturn.sub_const
            (integral (policy.iidEpisodeBatchMeasure initialState episodes)
              EpisodeBatch.totalReturn)).aemeasurable).2 hbatch
      change ProbabilityTheory.HasSubgaussianMGF
        (fun z : Real => z - source.successorReturnKernelMean n history)
        (MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes)
        (((source.batchKernel n).map EpisodeBatch.totalReturn) history)
      rw [ProbabilityTheory.Kernel.map_apply _ EpisodeBatch.measurable_totalReturn,
        source.batchKernel_eq_iidEpisodeBatchMeasure n history]
      change ProbabilityTheory.HasSubgaussianMGF
        (fun z : Real => z - source.successorReturnKernelMean n history)
        (MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes)
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
      mcond hmcond X center
      (MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes)
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
      (MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes) hcondComap
  simpa [successorReturnIncrement, successorReturnPrefixIncrement, X, center,
    prefixMap, Preorder.frestrictLe_apply, Preorder.frestrictLe₂_apply] using hcond

/-- Sum of the sharp batch proxies over the successor rounds. -/
noncomputable def episodewiseCumulativeSuccessorReturnVarianceProxy
    (mdp : MDP State Action) (episodes rounds : Nat) : NNReal :=
  ∑ t ∈ Finset.range (rounds + 1),
    match t with
    | 0 => 0
    | _ + 1 => MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The sharp cumulative proxy is `rounds * episodes * horizon^2`. -/
theorem episodewiseCumulativeSuccessorReturnVarianceProxy_coe
    (mdp : MDP State Action) (episodes rounds : Nat) :
    ((episodewiseCumulativeSuccessorReturnVarianceProxy
        mdp episodes rounds : NNReal) : Real) =
      (rounds : Real) * (episodes : Real) * (mdp.horizon : Real) ^ 2 := by
  rw [episodewiseCumulativeSuccessorReturnVarianceProxy]
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      rw [Nat.cast_succ]
      rw [Finset.sum_range_succ, NNReal.coe_add, ih]
      rw [MarkovPolicy.episodewiseBatchReturnVarianceProxy_coe]
      ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem episodewiseBatchReturnVarianceProxy_pos
    (mdp : MDP State Action) (episodes : Nat)
    (hepisodes : 0 < episodes) (hhorizon : 0 < mdp.horizon) :
    0 < MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes := by
  have hreal :
      0 < ((MarkovPolicy.episodewiseBatchReturnVarianceProxy
        mdp episodes : NNReal) : Real) := by
    rw [MarkovPolicy.episodewiseBatchReturnVarianceProxy_coe]
    positivity
  exact_mod_cast hreal

/-- Two-sided adaptive return tail with the sharp episodewise proxy. -/
theorem trajectoryMeasure_episodewiseCumulativeSuccessorReturnDeviation_abs_tail_le
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
              (episodewiseCumulativeSuccessorReturnVarianceProxy
                mdp episodes rounds) delta <=
            |source.cumulativeSuccessorReturnDeviation rounds trajectory|} <=
      ENNReal.ofReal delta := by
  let F := Filtration.piLE
    (X := fun _ : Nat => EpisodeBatch mdp episodes)
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | _ + 1 => MarkovPolicy.episodewiseBatchReturnVarianceProxy mdp episodes
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
      source.successorReturnIncrement_succ_episodewise_hasCondSubgaussianMGF
        i hrewardBound
  have hvariance :
      0 < ((((Finset.range (rounds + 1)).sum cY : NNReal) : Real)) := by
    have hproxy := episodewiseBatchReturnVarianceProxy_pos
      mdp episodes hepisodes hhorizon
    have hmem : 1 ∈ Finset.range (rounds + 1) := Finset.mem_range.mpr (by omega)
    exact_mod_cast Finset.sum_pos' (fun _ _ => zero_le _)
      ⟨1, hmem, by simpa [cY] using hproxy⟩
  simpa [episodewiseCumulativeSuccessorReturnVarianceProxy,
    cumulativeSuccessorReturnDeviation, cY] using
    (Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
      hadapted hzero (rounds + 1) hsucc hvariance delta hdelta hdelta_le_one)

/-- Sharp successor-return deviation event. -/
noncomputable def episodewiseSuccessorReturnDeviationBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (delta : Real) :
    Set (EpisodeBatchTrajectory mdp episodes) :=
  {trajectory |
    Concentration.subGaussianSumConfidenceRadius
        (episodewiseCumulativeSuccessorReturnVarianceProxy mdp episodes rounds)
        delta <=
      |source.cumulativeSuccessorReturnDeviation rounds trajectory|}

theorem measurableSet_episodewiseSuccessorReturnDeviationBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (delta : Real) :
    MeasurableSet
      (source.episodewiseSuccessorReturnDeviationBadEvent rounds delta) := by
  exact measurableSet_le measurable_const
    (source.measurable_cumulativeSuccessorReturnDeviation rounds).abs

theorem trajectoryMeasure_episodewiseSuccessorReturnDeviationBadEvent_le
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
        (source.episodewiseSuccessorReturnDeviationBadEvent rounds delta) <=
      ENNReal.ofReal delta := by
  simpa only [episodewiseSuccessorReturnDeviationBadEvent] using
    source.trajectoryMeasure_episodewiseCumulativeSuccessorReturnDeviation_abs_tail_le
      rounds hrounds hepisodes hhorizon hrewardBound delta hdelta hdelta_le_one

/-- Transport an expected-regret certificate through the sharp return event. -/
theorem trajectoryMeasure_expected_to_realized_successor_average_regret_episodewise_transport
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
    let returnBadEvent :=
      source.episodewiseSuccessorReturnDeviationBadEvent rounds delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        ENNReal.ofReal delta + ENNReal.ofReal delta /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        Good trajectory /\
          source.realizedSuccessorAverageRegret trajectory rounds <=
            expectedBound +
              Concentration.subGaussianSumConfidenceRadius
                  (episodewiseCumulativeSuccessorReturnVarianceProxy
                    mdp episodes rounds) delta /
                ((episodes : Real) * (rounds : Real)) := by
  let returnBadEvent :=
    source.episodewiseSuccessorReturnDeviationBadEvent rounds delta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  have hreturnMeasurable : MeasurableSet returnBadEvent := by
    simpa [returnBadEvent] using
      source.measurableSet_episodewiseSuccessorReturnDeviationBadEvent rounds delta
  have hreturnTail : source.trajectoryMeasure returnBadEvent <= ENNReal.ofReal delta := by
    simpa [returnBadEvent] using
      source.trajectoryMeasure_episodewiseSuccessorReturnDeviationBadEvent_le
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
            (episodewiseCumulativeSuccessorReturnVarianceProxy
              mdp episodes rounds) delta := by
      exact lt_of_not_ge (by simpa [returnBadEvent,
        episodewiseSuccessorReturnDeviationBadEvent] using hnotReturn)
    have hdenom : 0 < (episodes : Real) * (rounds : Real) := by
      positivity
    rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
      trajectory rounds hrounds hepisodes]
    have hnoise :
        -source.cumulativeSuccessorReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) <=
          Concentration.subGaussianSumConfidenceRadius
              (episodewiseCumulativeSuccessorReturnVarianceProxy
                mdp episodes rounds) delta /
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
              (episodewiseCumulativeSuccessorReturnVarianceProxy
                mdp episodes rounds) delta /
            ((episodes : Real) * (rounds : Real)) := add_le_add le_rfl hnoise
      _ <= expectedBound +
          Concentration.subGaussianSumConfidenceRadius
              (episodewiseCumulativeSuccessorReturnVarianceProxy
                mdp episodes rounds) delta /
            ((episodes : Real) * (rounds : Real)) := add_le_add hgood.2 le_rfl

/-- Sharp return-deviation radius after normalization by all sampled episodes. -/
noncomputable def episodewiseNormalizedSuccessorReturnConfidenceRadius
    (mdp : MDP State Action) (episodes rounds : Nat) (delta : Real) : Real :=
  Concentration.subGaussianSumConfidenceRadius
      (episodewiseCumulativeSuccessorReturnVarianceProxy mdp episodes rounds)
      delta /
    ((episodes : Real) * (rounds : Real))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem episodewiseNormalizedSuccessorReturnConfidenceRadius_nonneg
    (mdp : MDP State Action) (episodes rounds : Nat) (delta : Real) :
    0 <= episodewiseNormalizedSuccessorReturnConfidenceRadius
      mdp episodes rounds delta := by
  unfold episodewiseNormalizedSuccessorReturnConfidenceRadius
  exact div_nonneg
    (Concentration.subGaussianSumConfidenceRadius_nonneg _ _)
    (mul_nonneg (by positivity) (by positivity))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Exact normalized radius: episode count now improves concentration. -/
theorem episodewiseNormalizedSuccessorReturnConfidenceRadius_eq
    (mdp : MDP State Action) (episodes rounds : Nat) (delta : Real)
    (hepisodes : 0 < episodes) (hrounds : 0 < rounds)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    episodewiseNormalizedSuccessorReturnConfidenceRadius
        mdp episodes rounds delta =
      (mdp.horizon : Real) *
        Real.sqrt
          (2 * Real.log (2 / delta) /
            ((episodes : Real) * (rounds : Real))) := by
  have hepisodesReal : 0 < (episodes : Real) := by exact_mod_cast hepisodes
  have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
  have hlog : 0 <= Real.log (2 / delta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    linarith
  have hradiusSq :=
    Concentration.subGaussianSumConfidenceRadius_sq
      (episodewiseCumulativeSuccessorReturnVarianceProxy mdp episodes rounds)
      delta hdelta hdelta_le_one
  rw [episodewiseCumulativeSuccessorReturnVarianceProxy_coe] at hradiusSq
  have hsqrtSq :
      (Real.sqrt
        (2 * Real.log (2 / delta) /
          ((episodes : Real) * (rounds : Real)))) ^ 2 =
        2 * Real.log (2 / delta) /
          ((episodes : Real) * (rounds : Real)) := by
    rw [Real.sq_sqrt]
    positivity
  have hlhsNonneg :
      0 <= episodewiseNormalizedSuccessorReturnConfidenceRadius
        mdp episodes rounds delta :=
    episodewiseNormalizedSuccessorReturnConfidenceRadius_nonneg _ _ _ _
  have hrhsNonneg :
      0 <= (mdp.horizon : Real) *
        Real.sqrt
          (2 * Real.log (2 / delta) /
            ((episodes : Real) * (rounds : Real))) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hsq :
      (episodewiseNormalizedSuccessorReturnConfidenceRadius
          mdp episodes rounds delta) ^ 2 =
        ((mdp.horizon : Real) *
          Real.sqrt
            (2 * Real.log (2 / delta) /
              ((episodes : Real) * (rounds : Real)))) ^ 2 := by
    unfold episodewiseNormalizedSuccessorReturnConfidenceRadius
    rw [div_pow, hradiusSq]
    simp only [mul_pow]
    rw [hsqrtSq]
    field_simp [ne_of_gt hepisodesReal, ne_of_gt hroundsReal]
  nlinarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The sharp radius is no larger than the compiled whole-batch radius. -/
theorem episodewiseNormalizedSuccessorReturnConfidenceRadius_le_normalized
    (mdp : MDP State Action) (episodes rounds : Nat) (delta : Real)
    (hepisodes : 0 < episodes) (hrounds : 0 < rounds)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    episodewiseNormalizedSuccessorReturnConfidenceRadius
        mdp episodes rounds delta <=
      normalizedSuccessorReturnConfidenceRadius mdp episodes rounds delta := by
  rw [episodewiseNormalizedSuccessorReturnConfidenceRadius_eq
    mdp episodes rounds delta hepisodes hrounds hdelta hdelta_le_one]
  rw [normalizedSuccessorReturnConfidenceRadius_eq
    mdp episodes rounds delta hepisodes hrounds hdelta hdelta_le_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  have hepisodesReal : 1 <= (episodes : Real) := by exact_mod_cast hepisodes
  have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
  have hlog : 0 <= 2 * Real.log (2 / delta) := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    linarith
  apply (div_le_iff₀ (mul_pos (by positivity) hroundsReal)).2
  field_simp [ne_of_gt hroundsReal]
  nlinarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem episodewiseNormalizedSuccessorReturnConfidenceRadius_le_decayingEnvelope
    (mdp : MDP State Action) (episodes : Nat) (n : Nat)
    (hepisodes : 0 < episodes) :
    episodewiseNormalizedSuccessorReturnConfidenceRadius mdp episodes
        (decayingExplorationRounds mdp n) (vanishingAverageConfidenceDelta n) <=
      decayingExplorationReturnRadiusEnvelope mdp n := by
  exact
    (episodewiseNormalizedSuccessorReturnConfidenceRadius_le_normalized
      mdp episodes (decayingExplorationRounds mdp n)
      (vanishingAverageConfidenceDelta n) hepisodes
      (decayingExplorationRounds_pos mdp n)
      (vanishingAverageConfidenceDelta_pos n)
      (vanishingAverageConfidenceDelta_le_one n)).trans
      (normalizedSuccessorReturnConfidenceRadius_le_decayingEnvelope
        mdp episodes n hepisodes)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationEpisodewiseNormalizedReturnRadius_tendsto_zero
    (mdp : MDP State Action) (baseVisitFloor : Real) :
    Tendsto
      (fun n =>
        episodewiseNormalizedSuccessorReturnConfidenceRadius mdp
          (decayingExplorationScheduledEpisodes mdp baseVisitFloor n)
          (decayingExplorationRounds mdp n)
          (vanishingAverageConfidenceDelta n))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact episodewiseNormalizedSuccessorReturnConfidenceRadius_nonneg _ _ _ _
  · intro n
    exact episodewiseNormalizedSuccessorReturnConfidenceRadius_le_decayingEnvelope
      mdp (decayingExplorationScheduledEpisodes mdp baseVisitFloor n) n
      (decayingExplorationScheduledEpisodes_pos mdp baseVisitFloor n)
  · exact decayingExplorationReturnRadiusEnvelope_tendsto_zero mdp

/-- Expected behavior bound plus the sharp episodewise return radius. -/
noncomputable def decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) : Real :=
  decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      mdp baseVisitFloor n +
    episodewiseNormalizedSuccessorReturnConfidenceRadius mdp
      (decayingExplorationScheduledEpisodes mdp baseVisitFloor n)
      (decayingExplorationRounds mdp n)
      (vanishingAverageConfidenceDelta n)

theorem decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound_nonneg
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    0 <= decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
      mdp baseVisitFloor n := by
  unfold decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
  exact add_nonneg
    (by
      unfold decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
        decayingExplorationAverageRecommendedExpectedRegretBound
        decayingExplorationScheduledEpisodes
      exact add_nonneg
        (normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg mdp
          hhorizon (decayingExplorationRounds_pos mdp n)
          (vanishingAverageConfidenceDelta_pos n)
          (vanishingAverageConfidenceDelta_le_one n)
          (decayingExplorationVisitFloor_pos mdp hbaseVisitFloor n))
        (by unfold exploratoryBehaviorRegretCharge; positivity))
    (episodewiseNormalizedSuccessorReturnConfidenceRadius_nonneg _ _ _ _)

theorem decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
        mdp baseVisitFloor) atTop (nhds 0) := by
  simpa [decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound] using
    (decayingExplorationAverageExploratoryBehaviorBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor).add
      (decayingExplorationEpisodewiseNormalizedReturnRadius_tendsto_zero
        mdp baseVisitFloor)

theorem decayingExplorationEpisodewiseRealizedFailureAndRegretBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (fun n =>
        (decayingExplorationRealizedFailureBudget n,
          decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor n))
      atTop (nhds (0, 0)) := by
  rw [nhds_prod_eq]
  exact decayingExplorationRealizedFailureBudget_tendsto_zero.prodMk
    (decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor)

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/-- Realized-regret violation set for the sharp episodewise return certificate. -/
noncomputable def decayingExplorationEpisodewiseAverageRealizedBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Set
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)) := by
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
  exact {trajectory |
    AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
        mdp baseVisitFloor n <
      source.realizedSuccessorAverageRegret trajectory rounds}

/--
One scheduled finite window with episodewise return concentration.  The
realized violation set is covered by the measurable count/return union while
the good side retains optimism and the sharp normalized return radius.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationEpisodewiseAverageRealizedBehaviorConsistency
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
    let returnBadEvent :=
      source.episodewiseSuccessorReturnDeviationBadEvent rounds delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    let violationSet :=
      decayingExplorationEpisodewiseAverageRealizedBehaviorRegretViolationSet
        mdp initialState initialTable defaultState baseVisitFloor n
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
      violationSet ⊆ combinedBadEvent /\
      source.trajectoryMeasure violationSet <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        source.realizedSuccessorAverageRegret trajectory rounds <=
          AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor n := by
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
  let returnBadEvent :=
    source.episodewiseSuccessorReturnDeviationBadEvent rounds delta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  let violationSet :=
    decayingExplorationEpisodewiseAverageRealizedBehaviorRegretViolationSet
      mdp initialState initialTable defaultState baseVisitFloor n
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
    source.trajectoryMeasure_expected_to_realized_successor_average_regret_episodewise_transport
      rounds hrounds hepisodes hhorizon hrewardBound delta
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
      countBadEvent
      (AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
        mdp baseVisitFloor n)
      Good hcountMeasurable hcountTail hcountGood
  dsimp only at htransport
  rcases htransport with ⟨hmeasurable, htail, houtsideSharp⟩
  have htail' :
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n := by
    simpa [combinedBadEvent, countBadEvent, returnBadEvent,
      AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget]
      using htail
  have houtside' : forall trajectory, trajectory ∉ combinedBadEvent ->
      Good trajectory /\
        source.realizedSuccessorAverageRegret trajectory rounds <=
          AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor n := by
    intro trajectory htrajectory
    have h := houtsideSharp trajectory (by
      simpa [combinedBadEvent, countBadEvent, returnBadEvent] using htrajectory)
    exact ⟨h.1, by
      simpa [AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound,
        AdaptiveEpisodeBatchSource.episodewiseNormalizedSuccessorReturnConfidenceRadius]
        using h.2⟩
  have hsubset : violationSet ⊆ combinedBadEvent := by
    intro trajectory hviolation
    by_contra htrajectory
    have hbound := (houtside' trajectory htrajectory).2
    have hviolation' :
        AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor n <
          source.realizedSuccessorAverageRegret trajectory rounds := by
      simpa [violationSet,
        decayingExplorationEpisodewiseAverageRealizedBehaviorRegretViolationSet,
        rounds, delta, explorationRate, visitFloor, episodes, countRadius,
        source] using hviolation
    exact (not_lt_of_ge hbound) hviolation'
  have hviolationTail :
      source.trajectoryMeasure violationSet <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n :=
    (measure_mono hsubset).trans htail'
  exact ⟨by simpa [combinedBadEvent, countBadEvent, returnBadEvent] using hmeasurable,
    htail', hsubset, hviolationTail, houtside'⟩

/--
All scheduled finite windows with their indexed Borel witnesses, together with
the joint scalar limit.  The sample spaces may vary with the schedule index.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_decayingExplorationEpisodewiseAverageRealizedBehaviorConsistency_allWindows
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
        (fun n =>
          (AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n,
            AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
              mdp baseVisitFloor n))
        atTop (nhds (0, 0)) /\
      forall n,
        letI : StandardBorelSpace
            (EpisodeBatch mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
                mdp baseVisitFloor n)) := hbatchBorel n
        letI : StandardBorelSpace
            (EpisodeBatchTrajectory mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
                mdp baseVisitFloor n)) := htrajectoryBorel n
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
        let returnBadEvent :=
          source.episodewiseSuccessorReturnDeviationBadEvent rounds delta
        let combinedBadEvent := countBadEvent ∪ returnBadEvent
        let violationSet :=
          decayingExplorationEpisodewiseAverageRealizedBehaviorRegretViolationSet
            mdp initialState initialTable defaultState baseVisitFloor n
        MeasurableSet combinedBadEvent /\
          source.trajectoryMeasure combinedBadEvent <=
            AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
          violationSet ⊆ combinedBadEvent /\
          source.trajectoryMeasure violationSet <=
            AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
          forall trajectory, trajectory ∉ combinedBadEvent ->
            (forall round : Fin rounds, forall state,
              mdp.optimalValueRemaining mdp.horizon le_rfl state <=
                (adaptiveCumulativeEmpiricalOptimisticPlanAt
                  trajectory defaultState countRadius round).upperValueRemaining
                    mdp.horizon le_rfl state) /\
            source.realizedSuccessorAverageRegret trajectory rounds <=
              AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
                mdp baseVisitFloor n := by
  constructor
  · exact
      AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseRealizedFailureAndRegretBound_tendsto_zero
        mdp hhorizon baseVisitFloor hbaseVisitFloor
  · intro n
    letI := hbatchBorel n
    letI := htrajectoryBorel n
    exact
      exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationEpisodewiseAverageRealizedBehaviorConsistency
        mdp initialState baseVisitFloor n initialTable defaultState support
        hbaseFloor hrewardBound hhorizon hbaseVisitFloor

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
