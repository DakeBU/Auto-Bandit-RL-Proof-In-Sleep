import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeEmpiricalOptimisticRegret
import BanditRLProof.ConditionalExpectationReward

/-!
# Adaptive cumulative count martingale confidence

This module supplies the statistical producer required by the cumulative
count-radius planner.  Each raw episode-batch count is centered by its
history-kernel integral.  The exact adaptive iid batch law then gives a
conditionally sub-Gaussian increment with the within-batch Bernoulli proxy,
rather than the weaker whole-batch bounded-range proxy.

The final route unions cumulative prefix tails over the finite round/count
coordinate family and feeds the resulting empirical-transition coordinate
confidence into the compiled optimism and recommended-policy expected-regret
terminal.  It does not identify behavior or realized regret.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace CountCoordinate

/-- The uncentered real count selected by a visit or transition coordinate. -/
def rawCount
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    {episodes : Nat} (batch : EpisodeBatch mdp episodes) : Real :=
  match coordinate with
  | .visit stage state action => batch.visitCount stage state action
  | .transition stage state action nextState =>
      batch.transitionCount stage state action nextState

/-- The iid batch mean of the selected raw count. -/
noncomputable def policyMean
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) : Real :=
  match coordinate with
  | .visit stage state action =>
      (episodes : Real) *
        policy.stageVisitProbability initialState stage state action
  | .transition stage state action nextState =>
      (episodes : Real) *
        policy.stageTransitionJointProbability initialState stage state action nextState

omit [Nonempty State] [Nonempty Action] in
/-- Every selected raw count is measurable on the batch space. -/
theorem measurable_rawCount
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    {episodes : Nat} :
    Measurable (coordinate.rawCount : EpisodeBatch mdp episodes -> Real) := by
  cases coordinate with
  | visit stage state action =>
      exact MarkovPolicy.measurable_cast_visitCount stage state action
  | transition stage state action nextState =>
      exact MarkovPolicy.measurable_cast_transitionCount
        stage state action nextState

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The existing coordinate deviation is raw count minus policy mean. -/
theorem deviation_eq_rawCount_sub_policyMean
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} (batch : EpisodeBatch mdp episodes) :
    coordinate.deviation policy initialState batch =
      coordinate.rawCount batch -
        coordinate.policyMean policy initialState episodes := by
  cases coordinate <;> rfl

omit [Nonempty State] [Nonempty Action] in
/-- The kernel integral of a selected raw count is its policy mean. -/
theorem integral_rawCount_iidEpisodeBatchMeasure
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    integral (policy.iidEpisodeBatchMeasure initialState episodes)
        coordinate.rawCount =
      coordinate.policyMean policy initialState episodes := by
  cases coordinate with
  | visit stage state action =>
      let mu := policy.iidEpisodeBatchMeasure initialState episodes
      have hint : forall episode : Fin episodes,
          Integrable
            (fun batch : EpisodeBatch mdp episodes =>
              EpisodeStep.visitIndicator state action (batch episode stage)) mu := by
        intro episode
        have hmeas : Measurable
            (fun batch : EpisodeBatch mdp episodes =>
              EpisodeStep.visitIndicator state action (batch episode stage)) :=
          (EpisodeStep.measurable_visitIndicator state action).comp
            ((measurable_pi_apply stage).comp (measurable_pi_apply episode))
        refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
        exact Filter.Eventually.of_forall fun batch => by
          rw [Real.norm_eq_abs]
          have hmem :=
            EpisodeStep.visitIndicator_mem_Icc state action (batch episode stage)
          exact abs_le.2 ⟨by linarith [hmem.1], hmem.2⟩
      calc
        integral mu (rawCount (.visit stage state action)) =
            integral mu (fun batch : EpisodeBatch mdp episodes =>
              ∑ episode : Fin episodes,
                EpisodeStep.visitIndicator state action (batch episode stage)) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun batch => by
                simpa [rawCount] using
                  (MarkovPolicy.sum_visitIndicator_eq_cast_visitCount
                    batch stage state action).symm
        _ = ∑ episode : Fin episodes,
              integral mu (fun batch : EpisodeBatch mdp episodes =>
                EpisodeStep.visitIndicator state action (batch episode stage)) := by
              exact integral_finset_sum Finset.univ (fun episode _ => hint episode)
        _ = policyMean (.visit stage state action) policy initialState episodes := by
              simp [mu, policyMean,
                policy.integral_visitIndicator_iidEpisodeBatchMeasure_eval
                  initialState]
  | transition stage state action nextState =>
      let mu := policy.iidEpisodeBatchMeasure initialState episodes
      have hint : forall episode : Fin episodes,
          Integrable
            (fun batch : EpisodeBatch mdp episodes =>
              EpisodeStep.transitionIndicator state action nextState
                (batch episode stage)) mu := by
        intro episode
        have hmeas : Measurable
            (fun batch : EpisodeBatch mdp episodes =>
              EpisodeStep.transitionIndicator state action nextState
                (batch episode stage)) :=
          (EpisodeStep.measurable_transitionIndicator state action nextState).comp
            ((measurable_pi_apply stage).comp (measurable_pi_apply episode))
        refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
        exact Filter.Eventually.of_forall fun batch => by
          rw [Real.norm_eq_abs]
          have hmem := EpisodeStep.transitionIndicator_mem_Icc
            state action nextState (batch episode stage)
          exact abs_le.2 ⟨by linarith [hmem.1], hmem.2⟩
      calc
        integral mu (rawCount (.transition stage state action nextState)) =
            integral mu (fun batch : EpisodeBatch mdp episodes =>
              ∑ episode : Fin episodes,
                EpisodeStep.transitionIndicator state action nextState
                  (batch episode stage)) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun batch => by
                simpa [rawCount] using
                  (MarkovPolicy.sum_transitionIndicator_eq_cast_transitionCount
                    batch stage state action nextState).symm
        _ = ∑ episode : Fin episodes,
              integral mu (fun batch : EpisodeBatch mdp episodes =>
                EpisodeStep.transitionIndicator state action nextState
                  (batch episode stage)) := by
              exact integral_finset_sum Finset.univ (fun episode _ => hint episode)
        _ = policyMean (.transition stage state action nextState)
              policy initialState episodes := by
              simp [mu, policyMean,
                policy.integral_transitionIndicator_iidEpisodeBatchMeasure_eval
                  initialState]

omit [Nonempty State] [Nonempty Action] in
/--
The selected batch-count deviation has the sharp within-batch Bernoulli proxy.
-/
theorem deviation_hasSubgaussianMGF
    {mdp : MDP State Action} (coordinate : CountCoordinate mdp)
    (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    ProbabilityTheory.HasSubgaussianMGF
      (coordinate.deviation policy initialState)
      (MarkovPolicy.iidBernoulliVarianceProxy episodes)
      (policy.iidEpisodeBatchMeasure initialState episodes) := by
  cases coordinate with
  | visit stage state action =>
      have hsum :=
        ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
          (policy.iIndepFun_centeredVisitIndicator
            initialState episodes stage state action)
          (s := Finset.univ)
          (c := fun _episode : Fin episodes =>
            Concentration.intervalVarianceProxy 0 1)
          (fun episode _ =>
            policy.centeredVisitIndicator_hasSubgaussianMGF
              initialState stage state action episode)
      simpa [CountCoordinate.deviation,
        MarkovPolicy.iidBernoulliVarianceProxy,
        policy.sum_centeredVisitIndicator_eq_cast_visitCount_sub] using hsum
  | transition stage state action nextState =>
      have hsum :=
        ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
          (policy.iIndepFun_centeredTransitionIndicator
            initialState episodes stage state action nextState)
          (s := Finset.univ)
          (c := fun _episode : Fin episodes =>
            Concentration.intervalVarianceProxy 0 1)
          (fun episode _ =>
            policy.centeredTransitionIndicator_hasSubgaussianMGF
              initialState stage state action nextState episode)
      simpa [CountCoordinate.deviation,
        MarkovPolicy.iidBernoulliVarianceProxy,
        policy.sum_centeredTransitionIndicator_eq_cast_transitionCount_sub] using hsum

end CountCoordinate

namespace AdaptiveEpisodeBatchSource

/-- Predictable mean of the next selected raw count under the history kernel. -/
noncomputable def coordinateKernelMean
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (coordinate : CountCoordinate mdp)
    (history : EpisodeBatchPrefix mdp episodes n) : Real :=
  integral (source.batchKernel n history) coordinate.rawCount

omit [Nonempty State] [Nonempty Action] in
/-- The history-kernel raw-count mean is measurable in the finite prefix. -/
theorem measurable_coordinateKernelMean
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (coordinate : CountCoordinate mdp) :
    Measurable (source.coordinateKernelMean n coordinate) := by
  exact coordinate.measurable_rawCount.stronglyMeasurable.integral_kernel.measurable

omit [Nonempty State] [Nonempty Action] in
/-- The predictable kernel mean equals the selected-policy iid batch mean. -/
theorem coordinateKernelMean_eq_policyMean
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (coordinate : CountCoordinate mdp)
    (history : EpisodeBatchPrefix mdp episodes n) :
    source.coordinateKernelMean n coordinate history =
      coordinate.policyMean (source.successorPolicy n history)
        initialState episodes := by
  rw [coordinateKernelMean, source.batchKernel_eq_iidEpisodeBatchMeasure]
  exact coordinate.integral_rawCount_iidEpisodeBatchMeasure
    (source.successorPolicy n history) initialState episodes

/--
Count increment at a finite prefix.  At successor rounds the center is the
measurable history-kernel integral, not the potentially nonmeasurable policy
selector exposed by the source structure.
-/
noncomputable def coordinatePrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) :
    (round : Nat) -> EpisodeBatchPrefix mdp episodes round -> Real
  | 0, history =>
      coordinate.rawCount (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩) -
        coordinate.policyMean source.initialPolicy initialState episodes
  | n + 1, history =>
      coordinate.rawCount
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) -
        source.coordinateKernelMean n coordinate
          (Preorder.frestrictLe₂
            (π := fun _ : Nat => EpisodeBatch mdp episodes)
            (Nat.le_succ n) history)

omit [Nonempty State] [Nonempty Action] in
/-- Every finite-prefix increment is measurable. -/
theorem measurable_coordinatePrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) (round : Nat) :
    Measurable (source.coordinatePrefixIncrement coordinate round) := by
  cases round with
  | zero =>
      simpa [coordinatePrefixIncrement] using
        ((coordinate.measurable_rawCount.comp (measurable_pi_apply
          (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0))).sub
          measurable_const)
  | succ n =>
      simpa [coordinatePrefixIncrement] using
        ((coordinate.measurable_rawCount.comp (measurable_pi_apply
          (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1)))).sub
          ((source.measurable_coordinateKernelMean n coordinate).comp
            (Preorder.measurable_frestrictLe₂
              (X := fun _ : Nat => EpisodeBatch mdp episodes)
              (Nat.le_succ n))))

/-- The adaptive kernel-centered coordinate increment process. -/
noncomputable def coordinateIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) (round : Nat)
    (trajectory : EpisodeBatchTrajectory mdp episodes) : Real :=
  source.coordinatePrefixIncrement coordinate round
    (Preorder.frestrictLe round trajectory)

omit [Nonempty State] [Nonempty Action] in
/-- The coordinate increment process is adapted to the canonical prefix filtration. -/
theorem coordinateIncrement_stronglyAdapted_piLE
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) :
    StronglyAdapted
      (Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes))
      (source.coordinateIncrement coordinate) := by
  intro round
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact ((source.measurable_coordinatePrefixIncrement coordinate round).comp
    (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- The next raw-count conditional distribution is the mapped batch kernel. -/
theorem trajectoryMeasure_condDistrib_rawCount
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (coordinate : CountCoordinate mdp) :
    ProbabilityTheory.condDistrib
        (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
          coordinate.rawCount (trajectory (n + 1)))
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      (source.batchKernel n).map coordinate.rawCount := by
  letI : ProbabilityTheory.IsMarkovKernel (source.batchKernel n) :=
    source.batchKernel_isMarkov n
  have hcomp :
      ProbabilityTheory.condDistrib
          (coordinate.rawCount ∘
            (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
              trajectory (n + 1)))
          (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
            source.trajectoryMeasure.map (Preorder.frestrictLe n)]
        (ProbabilityTheory.condDistrib
          (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
            trajectory (n + 1))
          (Preorder.frestrictLe n) source.trajectoryMeasure).map
            coordinate.rawCount :=
    ProbabilityTheory.condDistrib_comp
      (μ := source.trajectoryMeasure)
      (Preorder.frestrictLe n)
      (measurable_pi_apply (n + 1)).aemeasurable
      coordinate.measurable_rawCount
  filter_upwards [hcomp, source.trajectoryMeasure_condDistrib n] with history hc hk
  have hmap :
      ((ProbabilityTheory.condDistrib
          (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
            trajectory (n + 1))
          (Preorder.frestrictLe n) source.trajectoryMeasure).map
            coordinate.rawCount) history =
        ((source.batchKernel n).map coordinate.rawCount) history := by
    rw [ProbabilityTheory.Kernel.map_apply _ coordinate.measurable_rawCount,
      ProbabilityTheory.Kernel.map_apply _ coordinate.measurable_rawCount, hk]
  simpa only [Function.comp_def] using hc.trans hmap

/--
Trimmed conditional-expectation-kernel law for the next adaptive raw count.
-/
theorem condExpKernel_map_rawCount_eq_batchKernel
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (coordinate : CountCoordinate mdp) :
    Filter.Eventually
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        Measure.map
            (fun path : EpisodeBatchTrajectory mdp episodes =>
              coordinate.rawCount (path (n + 1)))
            (ProbabilityTheory.condExpKernel source.trajectoryMeasure
              ((inferInstance : MeasurableSpace
                (EpisodeBatchPrefix mdp episodes n)).comap
                  (Preorder.frestrictLe n)) trajectory) =
          ((source.batchKernel n).map coordinate.rawCount)
            (Preorder.frestrictLe n trajectory))
      (ae (source.trajectoryMeasure.trim
        (Preorder.measurable_frestrictLe n).comap_le)) := by
  letI : ProbabilityTheory.IsMarkovKernel (source.batchKernel n) :=
    source.batchKernel_isMarkov n
  letI : ProbabilityTheory.IsMarkovKernel
      ((source.batchKernel n).map coordinate.rawCount) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map
      (source.batchKernel n) coordinate.measurable_rawCount
  exact
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      source.trajectoryMeasure
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        coordinate.rawCount (trajectory (n + 1)))
      (Preorder.frestrictLe n)
      (coordinate.measurable_rawCount.comp (measurable_pi_apply (n + 1)))
      (Preorder.measurable_frestrictLe n)
      ((source.batchKernel n).map coordinate.rawCount)
      (source.trajectoryMeasure_condDistrib_rawCount n coordinate)

/-- Initial adaptive batch-count increment has the iid Bernoulli sum proxy. -/
theorem coordinateIncrement_zero_hasSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) :
    ProbabilityTheory.HasSubgaussianMGF
      (source.coordinateIncrement coordinate 0)
      (MarkovPolicy.iidBernoulliVarianceProxy episodes)
      source.trajectoryMeasure := by
  have hbatch := coordinate.deviation_hasSubgaussianMGF
    source.initialPolicy initialState episodes
  rw [← source.trajectoryMeasure_map_eval_zero] at hbatch
  have hlift := ProbabilityTheory.HasSubgaussianMGF.of_map
    (Y := fun trajectory : EpisodeBatchTrajectory mdp episodes => trajectory 0)
    (X := coordinate.deviation source.initialPolicy initialState)
    (measurable_pi_apply 0).aemeasurable hbatch
  simpa only [coordinateIncrement, coordinatePrefixIncrement,
    Preorder.frestrictLe_apply,
    CountCoordinate.deviation_eq_rawCount_sub_policyMean,
    Function.comp_def] using hlift

/-- Every successor adaptive count increment is conditionally sub-Gaussian. -/
theorem coordinateIncrement_succ_hasCondSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (coordinate : CountCoordinate mdp) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes) n)
      ((Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes)).le n)
      (source.coordinateIncrement coordinate (n + 1))
      (MarkovPolicy.iidBernoulliVarianceProxy episodes)
      source.trajectoryMeasure := by
  let prefixMap : EpisodeBatchTrajectory mdp episodes ->
      EpisodeBatchPrefix mdp episodes n := Preorder.frestrictLe n
  let X : EpisodeBatchTrajectory mdp episodes -> Real := fun trajectory =>
    coordinate.rawCount (trajectory (n + 1))
  let center : EpisodeBatchTrajectory mdp episodes -> Real := fun trajectory =>
    source.coordinateKernelMean n coordinate (prefixMap trajectory)
  let target : EpisodeBatchTrajectory mdp episodes -> Measure Real := fun trajectory =>
    ((source.batchKernel n).map coordinate.rawCount) (prefixMap trajectory)
  have hspace :
      Filtration.piLE (X := fun _ : Nat => EpisodeBatch mdp episodes) n =
        (inferInstance : MeasurableSpace (EpisodeBatchPrefix mdp episodes n)).comap
          prefixMap := by
    simpa [prefixMap] using
      (Filtration.piLE_eq_comap_frestrictLe
        (X := fun _ : Nat => EpisodeBatch mdp episodes) n)
  have hX : Measurable X :=
    coordinate.measurable_rawCount.comp (measurable_pi_apply (n + 1))
  let mcond : MeasurableSpace (EpisodeBatchTrajectory mdp episodes) :=
    (inferInstance : MeasurableSpace (EpisodeBatchPrefix mdp episodes n)).comap
      prefixMap
  have hmcond : mcond <= MeasurableSpace.pi := by
    simpa [mcond, prefixMap] using
      (Preorder.measurable_frestrictLe
        (X := fun _ : Nat => EpisodeBatch mdp episodes) n).comap_le
  have hcenter : @Measurable (EpisodeBatchTrajectory mdp episodes) Real
      mcond inferInstance center := by
    exact (source.measurable_coordinateKernelMean n coordinate).comp
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
      (ae (source.trajectoryMeasure.trim
        hmcond)) := by
    simpa [X, target, prefixMap, mcond] using
      source.condExpKernel_map_rawCount_eq_batchKernel n coordinate
  have htarget : Filter.Eventually
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        ProbabilityTheory.HasSubgaussianMGF
          (fun z : Real => z - center trajectory)
          (MarkovPolicy.iidBernoulliVarianceProxy episodes)
          (target trajectory))
      (ae (source.trajectoryMeasure.trim
        hmcond)) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := prefixMap trajectory
      let policy := source.successorPolicy n history
      have hbatch := coordinate.deviation_hasSubgaussianMGF
        policy initialState episodes
      have hresidual : ProbabilityTheory.HasSubgaussianMGF
          (fun batch : EpisodeBatch mdp episodes =>
            coordinate.rawCount batch -
              coordinate.policyMean policy initialState episodes)
          (MarkovPolicy.iidBernoulliVarianceProxy episodes)
          (policy.iidEpisodeBatchMeasure initialState episodes) := by
        exact hbatch.congr (Filter.Eventually.of_forall fun batch =>
          coordinate.deviation_eq_rawCount_sub_policyMean
            policy initialState batch)
      have hid :=
        (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
          (coordinate.measurable_rawCount.sub_const
            (coordinate.policyMean policy initialState episodes)).aemeasurable).2
          hresidual
      change ProbabilityTheory.HasSubgaussianMGF
        (fun z : Real =>
          z - source.coordinateKernelMean n coordinate history)
        (MarkovPolicy.iidBernoulliVarianceProxy episodes)
        (((source.batchKernel n).map coordinate.rawCount) history)
      rw [ProbabilityTheory.Kernel.map_apply _ coordinate.measurable_rawCount,
        source.batchKernel_eq_iidEpisodeBatchMeasure n history]
      have hmean : source.coordinateKernelMean n coordinate history =
          coordinate.policyMean policy initialState episodes :=
        source.coordinateKernelMean_eq_policyMean n coordinate history
      rw [← hmean] at hid
      apply (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
        (measurable_id.sub_const
          (source.coordinateKernelMean n coordinate history)).aemeasurable).1
      rw [Measure.map_map
        (measurable_id.sub_const
          (source.coordinateKernelMean n coordinate history))
        coordinate.measurable_rawCount]
      simpa [Function.comp_def] using hid
  have hcondComap :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure
      mcond hmcond
      X center (MarkovPolicy.iidBernoulliVarianceProxy episodes)
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
      (MarkovPolicy.iidBernoulliVarianceProxy episodes) hcondComap
  simpa [coordinateIncrement, coordinatePrefixIncrement, X, center, prefixMap,
    Preorder.frestrictLe_apply,
    Preorder.frestrictLe₂_apply] using hcond

/-- Total within-batch variance proxy for a finite adaptive prefix. -/
noncomputable def cumulativeCoordinateVarianceProxy (episodes rounds : Nat) : NNReal :=
  ∑ _round ∈ Finset.range rounds,
    MarkovPolicy.iidBernoulliVarianceProxy episodes

/-- Delta-calibrated radius for one adaptive cumulative count coordinate. -/
noncomputable def cumulativeCoordinateConfidenceRadius
    (episodes rounds : Nat) (delta : Real) : Real :=
  Concentration.subGaussianSumConfidenceRadius
    (cumulativeCoordinateVarianceProxy episodes rounds) delta

/-- Sum of kernel-centered increments over the first `rounds` batches. -/
noncomputable def cumulativeCoordinateDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) (rounds : Nat)
    (trajectory : EpisodeBatchTrajectory mdp episodes) : Real :=
  ∑ round ∈ Finset.range rounds,
    source.coordinateIncrement coordinate round trajectory

omit [Nonempty State] [Nonempty Action] in
/-- Every fixed cumulative coordinate deviation is measurable. -/
theorem measurable_cumulativeCoordinateDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) (rounds : Nat) :
    Measurable (source.cumulativeCoordinateDeviation coordinate rounds) := by
  refine Finset.measurable_sum (Finset.range rounds) fun round _ => ?_
  exact (((source.coordinateIncrement_stronglyAdapted_piLE coordinate) round).mono
    ((Filtration.piLE
      (X := fun _ : Nat => EpisodeBatch mdp episodes)).le round)).measurable

/--
Two-sided square-root prefix tail for one adaptive cumulative count coordinate.
-/
theorem trajectoryMeasure_cumulativeCoordinateDeviation_abs_tail_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    source.trajectoryMeasure
        {trajectory |
          cumulativeCoordinateConfidenceRadius episodes rounds delta <=
            |source.cumulativeCoordinateDeviation coordinate rounds trajectory|} <=
      ENNReal.ofReal delta := by
  let F := Filtration.piLE
    (X := fun _ : Nat => EpisodeBatch mdp episodes)
  let cY : Nat -> NNReal := fun _ =>
    MarkovPolicy.iidBernoulliVarianceProxy episodes
  have hadapted : StronglyAdapted F (source.coordinateIncrement coordinate) := by
    simpa [F] using source.coordinateIncrement_stronglyAdapted_piLE coordinate
  have hzero := source.coordinateIncrement_zero_hasSubgaussianMGF coordinate
  have hsucc : forall i, i < rounds - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (source.coordinateIncrement coordinate (i + 1))
        (cY (i + 1)) source.trajectoryMeasure := by
    intro i _hi
    simpa [F, cY] using
      source.coordinateIncrement_succ_hasCondSubgaussianMGF i coordinate
  have hvariance :
      0 < ((((Finset.range rounds).sum cY : NNReal) : Real)) := by
    have hproxy := MarkovPolicy.iidBernoulliVarianceProxy_pos hepisodes
    have hmem : 0 ∈ Finset.range rounds := Finset.mem_range.mpr hrounds
    exact_mod_cast Finset.sum_pos' (fun _ _ => zero_le _) ⟨0, hmem, by
      exact_mod_cast hproxy⟩
  simpa [cumulativeCoordinateConfidenceRadius,
    cumulativeCoordinateVarianceProxy, cumulativeCoordinateDeviation, cY] using
    (Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
      hadapted hzero rounds hsucc hvariance delta hdelta hdelta_le_one)

/-- Equal confidence share for every queried prefix/coordinate pair. -/
noncomputable def cumulativeCountLocalDelta
    (mdp : MDP State Action) (rounds : Nat) (delta : Real) : Real :=
  delta /
    (Fintype.card (Fin rounds × CountCoordinate mdp) : Real)

/-- One global bad event covering every cumulative prefix and count coordinate. -/
noncomputable def adaptiveCumulativeCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (delta : Real) :
    Set (EpisodeBatchTrajectory mdp episodes) :=
  ⋃ index : Fin rounds × CountCoordinate mdp,
    {trajectory |
      cumulativeCoordinateConfidenceRadius episodes (index.1 + 1)
          (cumulativeCountLocalDelta mdp rounds delta) <=
        |source.cumulativeCoordinateDeviation index.2 (index.1 + 1) trajectory|}

omit [Nonempty State] [Nonempty Action] in
/-- The finite round-coordinate cumulative bad event is measurable. -/
theorem measurableSet_adaptiveCumulativeCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (delta : Real) :
    MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) := by
  unfold adaptiveCumulativeCountBadEvent
  exact MeasurableSet.iUnion fun index =>
    measurableSet_le measurable_const
      (source.measurable_cumulativeCoordinateDeviation index.2 (index.1 + 1)).abs

/-- The finite round-coordinate family is nonempty at positive horizon/rounds. -/
theorem cumulativeCountIndex_nonempty
    {mdp : MDP State Action} {rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds) :
    Nonempty (Fin rounds × CountCoordinate mdp) := by
  exact ⟨⟨⟨0, hrounds⟩,
    CountCoordinate.visit ⟨0, hhorizon⟩
      (Classical.choice inferInstance) (Classical.choice inferInstance)⟩⟩

/-- A positive global delta gives a positive local round-coordinate share. -/
theorem cumulativeCountLocalDelta_pos
    {mdp : MDP State Action} {rounds : Nat}
    (hindex : Nonempty (Fin rounds × CountCoordinate mdp))
    {delta : Real} (hdelta : 0 < delta) :
    0 < cumulativeCountLocalDelta mdp rounds delta := by
  unfold cumulativeCountLocalDelta
  exact div_pos hdelta (by
    exact_mod_cast Fintype.card_pos_iff.mpr hindex)

/-- A valid global delta gives every nonempty-family local share at most one. -/
theorem cumulativeCountLocalDelta_le_one
    {mdp : MDP State Action} {rounds : Nat}
    (hindex : Nonempty (Fin rounds × CountCoordinate mdp))
    {delta : Real} (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    cumulativeCountLocalDelta mdp rounds delta <= 1 := by
  have hcard : (1 : Real) <=
      Fintype.card (Fin rounds × CountCoordinate mdp) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hindex
  exact (div_le_self (le_of_lt hdelta) hcard).trans hdelta_le_one

/-- The global adaptive cumulative count event has the requested delta budget. -/
theorem trajectoryMeasure_adaptiveCumulativeCountBadEvent_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    source.trajectoryMeasure
        (source.adaptiveCumulativeCountBadEvent rounds delta) <=
      ENNReal.ofReal delta := by
  letI : Nonempty (Fin rounds × CountCoordinate mdp) :=
    cumulativeCountIndex_nonempty hhorizon hrounds
  simpa [adaptiveCumulativeCountBadEvent, cumulativeCountLocalDelta] using
    (ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
      source.trajectoryMeasure
      (Finset.univ : Finset (Fin rounds × CountCoordinate mdp))
      Finset.univ_nonempty delta
      (fun index =>
        {trajectory |
          cumulativeCoordinateConfidenceRadius episodes (index.1 + 1)
              (cumulativeCountLocalDelta mdp rounds delta) <=
            |source.cumulativeCoordinateDeviation
              index.2 (index.1 + 1) trajectory|})
      (fun index _ => by
        simpa [cumulativeCountLocalDelta] using
          source.trajectoryMeasure_cumulativeCoordinateDeviation_abs_tail_le
            index.2 (index.1 + 1) (Nat.succ_pos index.1) hepisodes
            (cumulativeCountLocalDelta mdp rounds delta)
            (cumulativeCountLocalDelta_pos inferInstance hdelta)
            (cumulativeCountLocalDelta_le_one
              inferInstance hdelta hdelta_le_one)))

omit [Nonempty State] [Nonempty Action] in
/-- Outside the union, every queried cumulative deviation is strictly small. -/
theorem cumulativeCoordinateDeviation_abs_lt_of_not_mem_badEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    {delta : Real} {trajectory : EpisodeBatchTrajectory mdp episodes}
    (htrajectory : trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta)
    (round : Fin rounds) (coordinate : CountCoordinate mdp) :
    |source.cumulativeCoordinateDeviation coordinate (round + 1) trajectory| <
      cumulativeCoordinateConfidenceRadius episodes (round + 1)
        (cumulativeCountLocalDelta mdp rounds delta) := by
  apply lt_of_not_ge
  intro hge
  apply htrajectory
  exact Set.mem_iUnion.2 ⟨(round, coordinate), hge⟩

/-- Predictable center used at one adaptive batch coordinate. -/
noncomputable def coordinateMeanAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) :
    Nat -> EpisodeBatchTrajectory mdp episodes -> Real
  | 0, _trajectory =>
      coordinate.policyMean source.initialPolicy initialState episodes
  | n + 1, trajectory =>
      source.coordinateKernelMean n coordinate
        (Preorder.frestrictLe n trajectory)

/-- Sum of predictable coordinate means over a finite prefix. -/
noncomputable def cumulativeCoordinateMean
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) (rounds : Nat)
    (trajectory : EpisodeBatchTrajectory mdp episodes) : Real :=
  ∑ round ∈ Finset.range rounds,
    source.coordinateMeanAt coordinate round trajectory

/-- Sum of uncentered coordinate counts over a finite prefix. -/
def cumulativeCoordinateRawCount
    {mdp : MDP State Action} {episodes : Nat}
    (coordinate : CountCoordinate mdp) (rounds : Nat)
    (trajectory : EpisodeBatchTrajectory mdp episodes) : Real :=
  ∑ round ∈ Finset.range rounds,
    coordinate.rawCount (trajectory round)

/-- Each adaptive increment is raw count minus its predictable mean. -/
theorem coordinateIncrement_eq_rawCount_sub_meanAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) (round : Nat)
    (trajectory : EpisodeBatchTrajectory mdp episodes) :
    source.coordinateIncrement coordinate round trajectory =
      coordinate.rawCount (trajectory round) -
        source.coordinateMeanAt coordinate round trajectory := by
  cases round with
  | zero =>
      simp [coordinateIncrement, coordinatePrefixIncrement, coordinateMeanAt]
  | succ n =>
      rfl

/-- The cumulative martingale deviation is raw count minus cumulative mean. -/
theorem cumulativeCoordinateDeviation_eq_rawCount_sub_mean
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (coordinate : CountCoordinate mdp) (rounds : Nat)
    (trajectory : EpisodeBatchTrajectory mdp episodes) :
    source.cumulativeCoordinateDeviation coordinate rounds trajectory =
      cumulativeCoordinateRawCount coordinate rounds trajectory -
        source.cumulativeCoordinateMean coordinate rounds trajectory := by
  unfold cumulativeCoordinateDeviation cumulativeCoordinateRawCount
    cumulativeCoordinateMean
  calc
    (∑ round ∈ Finset.range rounds,
        source.coordinateIncrement coordinate round trajectory) =
        ∑ round ∈ Finset.range rounds,
          (coordinate.rawCount (trajectory round) -
            source.coordinateMeanAt coordinate round trajectory) := by
          apply Finset.sum_congr rfl
          intro round _hround
          rw [source.coordinateIncrement_eq_rawCount_sub_meanAt]
    _ = (∑ round ∈ Finset.range rounds,
          coordinate.rawCount (trajectory round)) -
        ∑ round ∈ Finset.range rounds,
          source.coordinateMeanAt coordinate round trajectory := by
          rw [Finset.sum_sub_distrib]

/-- Cumulative visit raw counts are exactly the summary's visit count. -/
theorem cumulativeCoordinateRawCount_visit
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    cumulativeCoordinateRawCount (.visit stage state action) (round + 1) trajectory =
      ((cumulativeTransitionCountSummaryAt trajectory round).visitCount
        stage state action : Real) := by
  unfold cumulativeCoordinateRawCount
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [CountCoordinate.rawCount]
  norm_cast
  simpa [cumulativeTransitionCountSummaryAt] using
    (EpisodeBatchPrefix.cumulativeTransitionCountSummary_visitCount
      (Preorder.frestrictLe round trajectory) stage state action).symm

/-- Cumulative transition raw counts are exactly the summary coordinate. -/
theorem cumulativeCoordinateRawCount_transition
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    cumulativeCoordinateRawCount
        (.transition stage state action nextState) (round + 1) trajectory =
      (cumulativeTransitionCountSummaryAt trajectory round
        stage state action nextState : Real) := by
  unfold cumulativeCoordinateRawCount
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [CountCoordinate.rawCount]
  norm_cast

/-- Each transition-count predictable mean factors through its visit mean. -/
theorem coordinateMeanAt_transition_eq_visit_mul_transition
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (round : Nat) (trajectory : EpisodeBatchTrajectory mdp episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    source.coordinateMeanAt (.transition stage state action nextState)
        round trajectory =
      source.coordinateMeanAt (.visit stage state action) round trajectory *
        (mdp.transition (state, action)).real {nextState} := by
  cases round with
  | zero =>
      simp only [coordinateMeanAt, CountCoordinate.policyMean]
      rw [source.initialPolicy.stageTransitionJointProbability_eq_stageVisitProbability_mul_transition]
      simp only [Measure.real]
      ring
  | succ n =>
      rw [coordinateMeanAt, coordinateMeanAt,
        source.coordinateKernelMean_eq_policyMean,
        source.coordinateKernelMean_eq_policyMean]
      simp only [CountCoordinate.policyMean]
      rw [(source.successorPolicy n
        (Preorder.frestrictLe n trajectory)).stageTransitionJointProbability_eq_stageVisitProbability_mul_transition]
      simp only [Measure.real]
      ring

/-- Cumulative transition centers factor through the cumulative visit center. -/
theorem cumulativeCoordinateMean_transition_eq_visit_mul_transition
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (trajectory : EpisodeBatchTrajectory mdp episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    source.cumulativeCoordinateMean (.transition stage state action nextState)
        rounds trajectory =
      source.cumulativeCoordinateMean (.visit stage state action)
          rounds trajectory *
        (mdp.transition (state, action)).real {nextState} := by
  unfold cumulativeCoordinateMean
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro round _hround
  exact source.coordinateMeanAt_transition_eq_visit_mul_transition
    round trajectory stage state action nextState

/--
Positive cumulative visits convert the two martingale deviations into a
random-denominator empirical-transition singleton bound.
-/
theorem cumulativeEmpiricalTransitionMass_abs_sub_transition_lt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (round : Fin rounds)
    (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) (radius : Real)
    (hvisitPos : 0 <
      (cumulativeTransitionCountSummaryAt trajectory round).visitCount
        stage state action)
    (hvisitDeviation :
      |((cumulativeTransitionCountSummaryAt trajectory round).visitCount
          stage state action : Real) -
        source.cumulativeCoordinateMean (.visit stage state action)
          (round + 1) trajectory| < radius)
    (htransitionDeviation :
      |(cumulativeTransitionCountSummaryAt trajectory round
          stage state action nextState : Real) -
        source.cumulativeCoordinateMean (.transition stage state action nextState)
          (round + 1) trajectory| < radius) :
    |((cumulativeTransitionCountSummaryAt trajectory round).empiricalTransitionKernel
          defaultState stage (state, action)).real {nextState} -
        (mdp.transition (state, action)).real {nextState}| <
      2 * radius /
        ((cumulativeTransitionCountSummaryAt trajectory round).visitCount
          stage state action : Real) := by
  let summary := cumulativeTransitionCountSummaryAt trajectory round
  let visit : Real := summary.visitCount stage state action
  let joint : Real := summary stage state action nextState
  let expectedVisit : Real :=
    source.cumulativeCoordinateMean (.visit stage state action)
      (round + 1) trajectory
  let trueMass : Real := (mdp.transition (state, action)).real {nextState}
  have hvisit : 0 < visit := by
    dsimp [visit, summary]
    exact_mod_cast hvisitPos
  have hvisitNe : summary.visitCount stage state action ≠ 0 :=
    Nat.ne_of_gt hvisitPos
  have hmassNonneg : 0 <= trueMass := measureReal_nonneg
  have hmassLeOne : trueMass <= 1 := measureReal_le_one
  have hjointDeviation : |joint - expectedVisit * trueMass| < radius := by
    rw [← source.cumulativeCoordinateMean_transition_eq_visit_mul_transition
      (round + 1) trajectory stage state action nextState]
    simpa [joint, summary, expectedVisit] using htransitionDeviation
  have hnumerator : |joint - visit * trueMass| < 2 * radius := by
    calc
      |joint - visit * trueMass| =
          |(joint - expectedVisit * trueMass) -
            trueMass * (visit - expectedVisit)| := by
              congr 1
              ring
      _ <= |joint - expectedVisit * trueMass| +
          |trueMass * (visit - expectedVisit)| := abs_sub _ _
      _ = |joint - expectedVisit * trueMass| +
          trueMass * |visit - expectedVisit| := by
            rw [abs_mul, abs_of_nonneg hmassNonneg]
      _ < radius + trueMass * radius :=
        add_lt_add_of_lt_of_le hjointDeviation
          (mul_le_mul_of_nonneg_left
            (le_of_lt (by simpa [visit, summary, expectedVisit] using hvisitDeviation))
            hmassNonneg)
      _ <= 2 * radius := by
        have hradius : 0 <= radius :=
          (abs_nonneg (joint - expectedVisit * trueMass)).trans
            (le_of_lt hjointDeviation)
        nlinarith
  change
    |(summary.empiricalTransitionPMF defaultState stage state action).toMeasure.real
          {nextState} - trueMass| < 2 * radius / visit
  rw [Measure.real,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton nextState)]
  simp only [TransitionCountSummary.empiricalTransitionPMF, dif_neg hvisitNe,
    PMF.ofFintype_apply, ENNReal.toReal_div, ENNReal.toReal_natCast]
  change |joint / visit - trueMass| < 2 * radius / visit
  rw [show joint / visit - trueMass =
      (joint - visit * trueMass) / visit by field_simp]
  rw [abs_div, abs_of_pos hvisit]
  exact (div_lt_div_iff_of_pos_right hvisit).2 hnumerator

/--
Coordinate radius obtained from the cumulative visit denominator.  The zero
visit branch uses the trivial probability-mass bound; the positive branch
uses the paired visit and transition martingale deviations.
-/
noncomputable def adaptiveCumulativeTransitionCoordinateRadius
    {mdp : MDP State Action} {episodes rounds : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (round : Fin rounds) (delta : Real)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (_nextState : State) : Real :=
  let visits :=
    (cumulativeTransitionCountSummaryAt trajectory round).visitCount
      stage state action
  if visits = 0 then 1
  else
    2 * cumulativeCoordinateConfidenceRadius episodes (round + 1)
        (cumulativeCountLocalDelta mdp rounds delta) /
      (visits : Real)

/--
Regularity contract connecting the statistical coordinate radius to the
planner's count radius after multiplication by the recursive value envelope.
-/
def AdaptiveCumulativeCountMartingaleCover
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (countRadius : TransitionCountRadius) (delta rewardBound : Real) : Prop :=
  forall trajectory,
    trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
    forall (round : Fin rounds) (remaining : Nat)
      (hremaining : remaining + 1 <= mdp.horizon)
      (state : State) (action : Action),
      (∑ nextState,
        adaptiveCumulativeTransitionCoordinateRadius trajectory round delta
            (mdp.decisionStageRemaining remaining hremaining)
            state action nextState *
          empiricalFiniteBatchValueEnvelope
            rewardBound (countRadius.radius 0) remaining) <=
        countRadius.radius
          ((cumulativeTransitionCountSummaryAt trajectory round).visitCount
            (mdp.decisionStageRemaining remaining hremaining) state action)

/--
Outside the cumulative count-martingale event, the cumulative empirical plan
has the finite-coordinate confidence required by the optimistic Bellman route.
-/
noncomputable def coordinateConfidence_of_not_mem_adaptiveCumulativeCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    {delta : Real} {trajectory : EpisodeBatchTrajectory mdp episodes}
    (htrajectory :
      trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta)
    (round : Fin rounds) (defaultState : State)
    (countRadius : TransitionCountRadius) (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hcover : forall (remaining : Nat)
      (hremaining : remaining + 1 <= mdp.horizon)
      (state : State) (action : Action),
      (∑ nextState,
        adaptiveCumulativeTransitionCoordinateRadius trajectory round delta
            (mdp.decisionStageRemaining remaining hremaining)
            state action nextState *
          empiricalFiniteBatchValueEnvelope
            rewardBound (countRadius.radius 0) remaining) <=
        countRadius.radius
          ((cumulativeTransitionCountSummaryAt trajectory round).visitCount
            (mdp.decisionStageRemaining remaining hremaining) state action)) :
    (adaptiveCumulativeEmpiricalOptimisticPlanAt
      trajectory defaultState countRadius round).CoordinateConfidence where
  transitionCoordinateRadius :=
    adaptiveCumulativeTransitionCoordinateRadius trajectory round delta
  valueEnvelope :=
    empiricalFiniteBatchValueEnvelope rewardBound (countRadius.radius 0)
  rewardError_le_radius := by
    intro stage state action
    simp [adaptiveCumulativeEmpiricalOptimisticPlanAt,
      TransitionCountSummary.countRadiusOptimisticPlan]
  transitionCoordinateError_le_radius := by
    intro remaining hremaining state action nextState
    let stage := mdp.decisionStageRemaining remaining hremaining
    let summary := cumulativeTransitionCountSummaryAt trajectory round
    change
      |(summary.empiricalTransitionKernel defaultState stage
            (state, action)).real {nextState} -
          (mdp.transition (state, action)).real {nextState}| <=
        adaptiveCumulativeTransitionCoordinateRadius trajectory round delta
          stage state action nextState
    by_cases hzero : summary.visitCount stage state action = 0
    · letI := summary.empiricalTransitionKernel_isMarkov defaultState stage
      have hestimatedNonneg :
          0 <= (summary.empiricalTransitionKernel defaultState stage
            (state, action)).real {nextState} := measureReal_nonneg
      have hestimatedLeOne :
          (summary.empiricalTransitionKernel defaultState stage
            (state, action)).real {nextState} <= 1 := measureReal_le_one
      have htrueNonneg :
          0 <= (mdp.transition (state, action)).real {nextState} :=
        measureReal_nonneg
      have htrueLeOne :
          (mdp.transition (state, action)).real {nextState} <= 1 :=
        measureReal_le_one
      rw [adaptiveCumulativeTransitionCoordinateRadius, if_pos hzero]
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · have hvisitPos : 0 < summary.visitCount stage state action :=
        Nat.pos_of_ne_zero hzero
      have hvisitDeviation :=
        source.cumulativeCoordinateDeviation_abs_lt_of_not_mem_badEvent
          htrajectory round (.visit stage state action)
      rw [source.cumulativeCoordinateDeviation_eq_rawCount_sub_mean,
        cumulativeCoordinateRawCount_visit] at hvisitDeviation
      have htransitionDeviation :=
        source.cumulativeCoordinateDeviation_abs_lt_of_not_mem_badEvent
          htrajectory round (.transition stage state action nextState)
      rw [source.cumulativeCoordinateDeviation_eq_rawCount_sub_mean,
        cumulativeCoordinateRawCount_transition] at htransitionDeviation
      have hbound :=
        source.cumulativeEmpiricalTransitionMass_abs_sub_transition_lt
          trajectory round defaultState stage state action nextState
          (cumulativeCoordinateConfidenceRadius episodes (round + 1)
            (cumulativeCountLocalDelta mdp rounds delta))
          hvisitPos hvisitDeviation htransitionDeviation
      simpa [adaptiveCumulativeTransitionCoordinateRadius, summary, stage,
        hzero] using le_of_lt hbound
  upperValue_abs_le_envelope := by
    intro remaining hremaining state
    exact
      (cumulativeTransitionCountSummaryAt trajectory round).countRadiusOptimisticPlan_upperValueRemaining_abs_le
        mdp defaultState countRadius rewardBound hrewardBound remaining
          (by omega) state
  transitionRadius_cover := by
    intro remaining hremaining state action
    simpa [adaptiveCumulativeEmpiricalOptimisticPlanAt,
      TransitionCountSummary.countRadiusOptimisticPlan] using
        hcover remaining hremaining state action

/--
The cumulative count martingale event and cover produce the reusable global
coordinate-confidence contract for cumulative optimistic recommendations.
-/
noncomputable def adaptiveCumulativeCoordinateConfidenceContract_of_martingale
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hcover : AdaptiveCumulativeCountMartingaleCover
      (rounds := rounds) source countRadius delta rewardBound) :
    AdaptiveCumulativeCoordinateConfidenceContract
      source defaultState countRadius rounds delta where
  badEvent := source.adaptiveCumulativeCountBadEvent rounds delta
  measurable_badEvent :=
    source.measurableSet_adaptiveCumulativeCountBadEvent rounds delta
  measure_badEvent_le :=
    source.trajectoryMeasure_adaptiveCumulativeCountBadEvent_le
      hhorizon hrounds hepisodes delta hdelta hdelta_le_one
  coordinateConfidence_of_not_mem := by
    intro trajectory htrajectory round
    exact source.coordinateConfidence_of_not_mem_adaptiveCumulativeCountBadEvent
      htrajectory round defaultState countRadius rewardBound hrewardBound
        (hcover trajectory htrajectory round)

/--
Generic route endpoint: cumulative count martingales supply the probability
producer for optimism and explicit recommended-policy expected regret.
-/
theorem trajectoryMeasure_adaptiveCumulativeCountMartingale_optimism_and_explicitRecommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hcover : AdaptiveCumulativeCountMartingaleCover
      (rounds := rounds) source countRadius delta rewardBound)
    (radiusEnvelope : Fin rounds -> Real)
    (hradius : forall trajectory,
      trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
      forall (round : Fin rounds) (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon) (state : State),
        (adaptiveCumulativeEmpiricalOptimisticPlanAt
          trajectory defaultState countRadius round).selectedRadiusRemaining
            remaining hremaining state <= radiusEnvelope round) :
    MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent rounds delta) <=
        ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          ∑ round : Fin rounds,
            (mdp.horizon : Real) * (2 * radiusEnvelope round) := by
  let contract :=
    source.adaptiveCumulativeCoordinateConfidenceContract_of_martingale
      defaultState countRadius rewardBound hrewardBound hhorizon hrounds
        hepisodes delta hdelta hdelta_le_one hcover
  simpa [contract,
    adaptiveCumulativeCoordinateConfidenceContract_of_martingale] using
    (AdaptiveCumulativeCoordinateConfidenceContract.trajectoryMeasure_optimism_and_explicitRecommendedExpectedRegret
      source defaultState countRadius delta contract radiusEnvelope
        (by
          intro trajectory htrajectory round remaining hremaining state
          exact hradius trajectory htrajectory round remaining hremaining state))

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/--
Concrete exploratory-source endpoint for the cumulative count-martingale
confidence route.  The conclusion concerns recommended policies, not behavior
or realized regret.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeCountMartingale_optimism_and_explicitRecommendedExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes rounds : Nat)
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hcover : AdaptiveEpisodeBatchSource.AdaptiveCumulativeCountMartingaleCover
      (rounds := rounds)
      (exploratorySource mdp initialState episodes initialTable defaultState
        countRadius explorationRate hexplorationRate)
      countRadius delta rewardBound)
    (radiusEnvelope : Fin rounds -> Real)
    (hradius : forall trajectory,
      trajectory ∉
        (exploratorySource mdp initialState episodes initialTable defaultState
          countRadius explorationRate hexplorationRate).adaptiveCumulativeCountBadEvent
            rounds delta ->
      forall (round : Fin rounds) (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon) (state : State),
        (adaptiveCumulativeEmpiricalOptimisticPlanAt
          trajectory defaultState countRadius round).selectedRadiusRemaining
            remaining hremaining state <= radiusEnvelope round) :
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate hexplorationRate
    MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent rounds delta) <=
        ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          ∑ round : Fin rounds,
            (mdp.horizon : Real) * (2 * radiusEnvelope round) := by
  exact
    (exploratorySource mdp initialState episodes initialTable defaultState
      countRadius explorationRate hexplorationRate).trajectoryMeasure_adaptiveCumulativeCountMartingale_optimism_and_explicitRecommendedExpectedRegret
        defaultState countRadius rewardBound hrewardBound hhorizon hrounds
          hepisodes delta hdelta hdelta_le_one hcover radiusEnvelope hradius

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
