import BanditRLProof.RL.FiniteHorizonStochasticRewardErasureLaw
import BanditRLProof.RL.FiniteHorizonStochasticRewardInitialLawTotalReturnConcentration
import BanditRLProof.RL.FiniteHorizonIIDAllCoordinateFiniteBatchConfidence

/-!
# IID empirical reward confidence for finite-horizon stochastic rewards

This module retains the sampled reward in every generated episode record.  It
proves that a fixed stage/state/action reward sum, centered by its stored MDP
mean and masked by the visit event, is sub-Gaussian across iid complete
trajectories.  The total proxy is the conservative episode-linear proxy
`episodes * varianceProxy`; no bounded sampled-reward or exact-count claim is
used.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof

namespace Concentration

/-- A uniform fiberwise sub-Gaussian proxy survives an arbitrary probability mixture. -/
theorem hasSubgaussianMGF_compProd_of_forall
    {Index : Type u} {Omega : Type v}
    [MeasurableSpace Index] [MeasurableSpace Omega]
    (mu : Measure Index) [IsProbabilityMeasure mu]
    (kappa : ProbabilityTheory.Kernel Index Omega)
    [ProbabilityTheory.IsMarkovKernel kappa]
    (X : Index × Omega -> Real) (hX : Measurable X) (c : NNReal)
    (hfiber : forall index,
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega => X (index, omega)) c (kappa index)) :
    ProbabilityTheory.HasSubgaussianMGF X c (mu.compProd kappa) := by
  constructor
  · intro t
    have hfullMeas : Measurable (fun p => Real.exp (t * X p)) :=
      Real.measurable_exp.comp (measurable_const.mul hX)
    have hfullAE : AEStronglyMeasurable
        (fun p => Real.exp (t * X p)) (mu.compProd kappa) :=
      hfullMeas.aestronglyMeasurable
    apply (Measure.integrable_compProd_iff hfullAE).2
    constructor
    · exact Filter.Eventually.of_forall fun index =>
        (hfiber index).integrable_exp_mul t
    · have hinnerAE : AEStronglyMeasurable
          (fun index => integral (kappa index)
            (fun omega => ‖Real.exp (t * X (index, omega))‖)) mu :=
        hfullAE.norm.integral_kernel_compProd
      refine Integrable.of_bound hinnerAE
        (Real.exp ((c : Real) * t ^ 2 / 2)) ?_
      exact Filter.Eventually.of_forall fun index => by
        have heq :
            (integral (kappa index)
                (fun omega => ‖Real.exp (t * X (index, omega))‖)) =
              ProbabilityTheory.mgf
                (fun omega => X (index, omega)) (kappa index) t := by
          simp [ProbabilityTheory.mgf, Real.norm_eq_abs]
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), heq]
        exact (hfiber index).mgf_le t
  · intro t
    have hfullMeas : Measurable (fun p => Real.exp (t * X p)) :=
      Real.measurable_exp.comp (measurable_const.mul hX)
    have hfullAE : AEStronglyMeasurable
        (fun p => Real.exp (t * X p)) (mu.compProd kappa) :=
      hfullMeas.aestronglyMeasurable
    have hfullInt : Integrable (fun p => Real.exp (t * X p))
        (mu.compProd kappa) := by
      apply (Measure.integrable_compProd_iff hfullAE).2
      constructor
      · exact Filter.Eventually.of_forall fun index =>
          (hfiber index).integrable_exp_mul t
      · have hinnerAE : AEStronglyMeasurable
            (fun index => integral (kappa index)
              (fun omega => ‖Real.exp (t * X (index, omega))‖)) mu :=
          hfullAE.norm.integral_kernel_compProd
        refine Integrable.of_bound hinnerAE
          (Real.exp ((c : Real) * t ^ 2 / 2)) ?_
        exact Filter.Eventually.of_forall fun index => by
          have heq :
              (integral (kappa index)
                  (fun omega => ‖Real.exp (t * X (index, omega))‖)) =
                ProbabilityTheory.mgf
                  (fun omega => X (index, omega)) (kappa index) t := by
            simp [ProbabilityTheory.mgf, Real.norm_eq_abs]
          rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), heq]
          exact (hfiber index).mgf_le t
    rw [ProbabilityTheory.mgf, Measure.integral_compProd hfullInt]
    have hinnerAE : AEStronglyMeasurable
        (fun index => integral (kappa index)
          (fun omega => Real.exp (t * X (index, omega)))) mu :=
      hfullAE.integral_kernel_compProd
    have hinnerInt : Integrable
        (fun index => integral (kappa index)
          (fun omega => Real.exp (t * X (index, omega)))) mu := by
      refine Integrable.of_bound hinnerAE
        (Real.exp ((c : Real) * t ^ 2 / 2)) ?_
      exact Filter.Eventually.of_forall fun index => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => Real.exp_nonneg _)]
        exact (hfiber index).mgf_le t
    have hmono := integral_mono_ae hinnerInt (integrable_const _)
      (Filter.Eventually.of_forall fun index => (hfiber index).mgf_le t)
    simpa [ProbabilityTheory.mgf] using hmono

/-- The zero random variable admits every nonnegative sub-Gaussian proxy. -/
theorem hasSubgaussianMGF_zero_of_proxy
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (c : NNReal) :
    ProbabilityTheory.HasSubgaussianMGF (fun _ : Omega => 0) c mu := by
  constructor
  · intro t
    simp
  · intro t
    have hnonneg : 0 <= (c : Real) * t ^ 2 / 2 := by positivity
    simpa [ProbabilityTheory.mgf] using Real.one_le_exp hnonneg

end Concentration

namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace RewardStepTrace

/-- State immediately before a reward-bearing trajectory coordinate. -/
def stateAt (initialState : State) {remaining : Nat}
    (trace : RewardStepTrace Action State remaining)
    (coordinate : Fin remaining) : State :=
  if hzero : coordinate.val = 0 then initialState
  else (trace ⟨coordinate.val - 1, by omega⟩).2.2

omit [Fintype State] [Fintype Action] [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The pre-coordinate state is measurable as a function of the full trace. -/
theorem measurable_stateAt (initialState : State) {remaining : Nat}
    (coordinate : Fin remaining) :
    Measurable (fun trace : RewardStepTrace Action State remaining =>
      stateAt initialState trace coordinate) := by
  unfold stateAt
  split_ifs
  · exact measurable_const
  · exact measurable_snd.snd.comp (measurable_pi_apply _)

omit [Fintype State] [Fintype Action] [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
@[simp]
theorem stateAt_cons_zero (initialState : State) (remaining : Nat)
    (head : Action × (Real × State))
    (tail : RewardStepTrace Action State remaining) :
    stateAt initialState
        (@Fin.cons remaining (fun _ => Action × (Real × State)) head tail) 0 =
      initialState := by
  simp [stateAt]

omit [Fintype State] [Fintype Action] [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
@[simp]
theorem stateAt_cons_succ (initialState : State) (remaining : Nat)
    (head : Action × (Real × State))
    (tail : RewardStepTrace Action State remaining)
    (coordinate : Fin remaining) :
    stateAt initialState
        (@Fin.cons remaining (fun _ => Action × (Real × State)) head tail)
        coordinate.succ =
      stateAt head.2.2 tail coordinate := by
  unfold stateAt
  rw [dif_neg (by simp)]
  have hindex :
      (⟨coordinate.succ.val - 1, by omega⟩ : Fin (remaining + 1)) =
        coordinate.castSucc := by
    apply Fin.ext
    simp
  rw [hindex]
  by_cases hzero : coordinate.val = 0
  · let zeroCoordinate : Fin remaining := ⟨0, by omega⟩
    have hcoordinate : coordinate = zeroCoordinate := by
      apply Fin.ext
      simpa [zeroCoordinate] using hzero
    rw [hcoordinate]
    simp [zeroCoordinate]
  · rw [dif_neg hzero]
    let previous : Fin remaining := ⟨coordinate.val - 1, by omega⟩
    have hcoordinate : coordinate.castSucc = previous.succ := by
      apply Fin.ext
      simp [previous]
      omega
    rw [hcoordinate, Fin.cons_succ]

omit [Fintype State] [Fintype Action] [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The pre-coordinate state is measurable when the initial state is also an input. -/
theorem measurable_stateAt_prod {remaining : Nat} (coordinate : Fin remaining) :
    Measurable (fun p : State × RewardStepTrace Action State remaining =>
      stateAt p.1 p.2 coordinate) := by
  unfold stateAt
  split_ifs
  · exact measurable_fst
  · exact measurable_snd.snd.comp
      ((measurable_pi_apply _).comp measurable_snd)

end RewardStepTrace

namespace MDP

/-- A sampled reward centered at one target coordinate and masked by its visit event. -/
def maskedRewardDeviationAt (mdp : MDP State Action)
    (initialState : State) {remaining : Nat}
    (trace : RewardStepTrace Action State remaining)
    (coordinate : Fin remaining) (state : State) (action : Action) : Real :=
  if RewardStepTrace.stateAt initialState trace coordinate = state /\
      (trace coordinate).1 = action then
    (trace coordinate).2.1 - mdp.reward state action
  else 0

/-- A fixed visit-masked reward deviation is measurable on reward-bearing traces. -/
theorem measurable_maskedRewardDeviationAt (mdp : MDP State Action)
    (initialState : State) {remaining : Nat} (coordinate : Fin remaining)
    (state : State) (action : Action) :
    Measurable (fun trace =>
      mdp.maskedRewardDeviationAt initialState trace coordinate state action) := by
  unfold maskedRewardDeviationAt
  refine Measurable.ite ?_ ?_ measurable_const
  · exact
      ((RewardStepTrace.measurable_stateAt initialState coordinate)
        (measurableSet_singleton state)).inter
        (((measurable_fst.comp (measurable_pi_apply coordinate)))
          (measurableSet_singleton action))
  · exact (measurable_snd.fst.comp (measurable_pi_apply coordinate)).sub
      measurable_const

/-- The masked deviation is measurable when the initial state is part of the input. -/
theorem measurable_maskedRewardDeviationAt_trajectory (mdp : MDP State Action)
    {remaining : Nat} (coordinate : Fin remaining)
    (state : State) (action : Action) :
    Measurable (fun trajectory : State × RewardStepTrace Action State remaining =>
      mdp.maskedRewardDeviationAt trajectory.1 trajectory.2 coordinate state action) := by
  unfold maskedRewardDeviationAt
  have hcoordinate : Measurable
      (fun trajectory : State × RewardStepTrace Action State remaining =>
        trajectory.2 coordinate) :=
    (measurable_pi_apply coordinate).comp measurable_snd
  refine Measurable.ite ?_ ?_ measurable_const
  · exact
      (RewardStepTrace.measurable_stateAt_prod coordinate
        (measurableSet_singleton state)).inter
        (hcoordinate.fst (measurableSet_singleton action))
  · exact
      (hcoordinate.snd.fst.sub measurable_const)

/-- One sampled reward-bearing trajectory converted to an empirical record. -/
def sampledEpisodeStepOfStochasticTrajectory (mdp : MDP State Action)
    (trajectory : State × RewardStepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) : EpisodeStep State Action where
  state := RewardStepTrace.stateAt trajectory.1 trajectory.2 stage
  action := (trajectory.2 stage).1
  reward := (trajectory.2 stage).2.1
  nextState := (trajectory.2 stage).2.2

/-- Extracting a sampled empirical record from a stochastic trajectory is measurable. -/
theorem measurable_sampledEpisodeStepOfStochasticTrajectory
    (mdp : MDP State Action) (stage : Fin mdp.horizon) :
    Measurable (fun trajectory =>
      mdp.sampledEpisodeStepOfStochasticTrajectory trajectory stage) := by
  rw [measurable_comap_iff]
  change Measurable (fun trajectory :
      State × RewardStepTrace Action State mdp.horizon =>
    (RewardStepTrace.stateAt trajectory.1 trajectory.2 stage,
      (trajectory.2 stage).1, (trajectory.2 stage).2.1,
      (trajectory.2 stage).2.2))
  have hstate : Measurable
      (fun trajectory : State × RewardStepTrace Action State mdp.horizon =>
        RewardStepTrace.stateAt trajectory.1 trajectory.2 stage) :=
    RewardStepTrace.measurable_stateAt_prod stage
  have hcoordinate : Measurable
      (fun trajectory : State × RewardStepTrace Action State mdp.horizon =>
        trajectory.2 stage) :=
    (measurable_pi_apply stage).comp measurable_snd
  exact hstate.prodMk
    (hcoordinate.fst.prodMk (hcoordinate.snd.fst.prodMk hcoordinate.snd.snd))

/-- A finite iid family of stochastic trajectories mapped to sampled-reward records. -/
def sampledEpisodeBatchOfStochasticTrajectories (mdp : MDP State Action)
    (episodes : Nat)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon) :
    EpisodeBatch mdp episodes :=
  fun episode stage =>
    mdp.sampledEpisodeStepOfStochasticTrajectory (trajectories episode) stage

/-- Mapping a finite stochastic trajectory family to sampled episode records is measurable. -/
theorem measurable_sampledEpisodeBatchOfStochasticTrajectories
    (mdp : MDP State Action) (episodes : Nat) :
    Measurable (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes) := by
  apply measurable_pi_lambda
  intro episode
  apply measurable_pi_lambda
  intro stage
  exact (mdp.measurable_sampledEpisodeStepOfStochasticTrajectory stage).comp
    (measurable_pi_apply episode)

end MDP

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- A visit-masked one-step reward deviation retains the common reward proxy. -/
theorem actionRewardStateKernel_maskedRewardDeviation_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon)
    (initialState state : State) (action : Action) (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun head : Action × (Real × State) =>
        if initialState = state /\ head.1 = action then
          head.2.1 - mdp.reward state action
        else 0)
      varianceProxy
      (source.actionRewardStateKernel policy stage initialState) := by
  by_cases hinitial : initialState = state
  · subst initialState
    let X : Action × (Real × State) -> Real := fun head =>
      if head.1 = action then head.2.1 - mdp.reward state action else 0
    let rewardNextKernel : ProbabilityTheory.Kernel Action (Real × State) :=
      ProbabilityTheory.Kernel.sectR source.rewardNextStateKernel state
    have hX : Measurable X := by
      refine Measurable.ite
        (measurable_fst (measurableSet_singleton action)) ?_ measurable_const
      exact measurable_snd.fst.sub measurable_const
    have hmix := Concentration.hasSubgaussianMGF_compProd_of_forall
      (policy.actionKernel stage state) rewardNextKernel X hX
      varianceProxy (fun candidate => by
        by_cases hcandidate : candidate = action
        · subst candidate
          have hbase := law.hasSubgaussianMGF state action
          have hlift := ProbabilityTheory.HasSubgaussianMGF.of_map
            (μ := source.rewardNextStateKernel (state, action))
            (Y := Prod.fst)
            (X := fun reward : Real => reward - mdp.reward state action)
            measurable_fst.aemeasurable (by
              rw [rewardNextStateKernel,
                ProbabilityTheory.Kernel.prod_apply,
                Measure.map_fst_prod, measure_univ, one_smul]
              exact hbase)
          simpa [X, rewardNextKernel, ProbabilityTheory.Kernel.sectR_apply,
            Function.comp_def] using hlift
        · simpa [X, hcandidate, rewardNextKernel,
            ProbabilityTheory.Kernel.sectR_apply] using
            (Concentration.hasSubgaussianMGF_zero_of_proxy
              (source.rewardNextStateKernel (state, candidate)) varianceProxy))
    rw [actionRewardStateKernel,
      ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
    simpa [rewardNextKernel, X] using hmix
  · simpa [hinitial] using
      (Concentration.hasSubgaussianMGF_zero_of_proxy
        (source.actionRewardStateKernel policy stage initialState) varianceProxy)

/-- Every coordinate of a generated reward-bearing trace has the masked reward MGF. -/
theorem stochasticTrajectoryKernelRemaining_maskedRewardDeviationAt_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (initialState : State) (coordinate : Fin remaining)
    (state : State) (action : Action) (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun trace => mdp.maskedRewardDeviationAt initialState trace
        coordinate state action)
      varianceProxy
      (source.stochasticTrajectoryKernelRemaining policy
        remaining hremaining initialState) := by
  induction remaining generalizing initialState with
  | zero => exact Fin.elim0 coordinate
  | succ remaining ih =>
      refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate
      · have hhead :=
          source.actionRewardStateKernel_maskedRewardDeviation_hasSubgaussianMGF
            policy ⟨mdp.horizon - (remaining + 1), by omega⟩
              initialState state action varianceProxy law
        rw [← source.stochasticTrajectoryKernelRemaining_map_head
          policy remaining hremaining initialState] at hhead
        have hlift := ProbabilityTheory.HasSubgaussianMGF.of_map
          (Y := RewardStepTrace.head
            (Action := Action) (State := State) remaining)
          (X := fun head : Action × (Real × State) =>
            if initialState = state /\ head.1 = action then
              head.2.1 - mdp.reward state action
            else 0)
          (RewardStepTrace.measurable_head remaining).aemeasurable hhead
        simpa [MDP.maskedRewardDeviationAt, RewardStepTrace.head,
          Function.comp_def] using hlift
      · let headKernel := source.actionRewardStateKernel policy
          ⟨mdp.horizon - (remaining + 1), by omega⟩
        let tailKernelGlobal : ProbabilityTheory.Kernel
            (State × (Action × (Real × State)))
            (RewardStepTrace Action State remaining) :=
          (source.stochasticTrajectoryKernelRemaining policy remaining (by omega)).comap
            (fun p : State × (Action × (Real × State)) => p.2.2.2)
            measurable_snd.snd.snd
        let tailKernel : ProbabilityTheory.Kernel
            (Action × (Real × State))
            (RewardStepTrace Action State remaining) :=
          ProbabilityTheory.Kernel.sectR tailKernelGlobal initialState
        let X : (Action × (Real × State)) ×
            RewardStepTrace Action State remaining -> Real := fun p =>
          mdp.maskedRewardDeviationAt p.1.2.2 p.2 tailCoordinate state action
        have hX : Measurable X :=
          (MDP.measurable_maskedRewardDeviationAt_trajectory mdp
            tailCoordinate state action).comp
              (measurable_fst.snd.snd.prodMk measurable_snd)
        have hpair := Concentration.hasSubgaussianMGF_compProd_of_forall
          (headKernel initialState) tailKernel X hX varianceProxy
          (fun head => by
            simpa [tailKernel, tailKernelGlobal, X,
              ProbabilityTheory.Kernel.sectR_apply,
              ProbabilityTheory.Kernel.comap_apply] using
              ih (by omega) head.2.2 tailCoordinate)
        let consStep : (Action × (Real × State)) ×
            RewardStepTrace Action State remaining ->
            RewardStepTrace Action State (remaining + 1) := fun p =>
          @Fin.cons remaining (fun _ => Action × (Real × State)) p.1 p.2
        have hcons : Measurable consStep := RewardStepTrace.measurable_cons remaining
        have htarget := hpair.congr_identDistrib
          { aemeasurable_fst := hX.aemeasurable
            aemeasurable_snd :=
              (MDP.measurable_maskedRewardDeviationAt mdp initialState
                tailCoordinate.succ state action).aemeasurable
            map_eq := by
              rw [Measure.map_map
                (MDP.measurable_maskedRewardDeviationAt mdp initialState
                  tailCoordinate.succ state action) hcons]
              congr 1
              funext p
              simp [X, consStep, MDP.maskedRewardDeviationAt] }
        rw [stochasticTrajectoryKernelRemaining]
        rw [ProbabilityTheory.Kernel.map_apply _ hcons]
        rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
        simpa [headKernel, tailKernel, tailKernelGlobal, consStep] using htarget

/-- The same fixed coordinate MGF holds after mixing over the initial-state law. -/
theorem stochasticTrajectoryMeasure_maskedRewardDeviationAt_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun trajectory : State × RewardStepTrace Action State mdp.horizon =>
        mdp.maskedRewardDeviationAt trajectory.1 trajectory.2 stage state action)
      varianceProxy
      (source.stochasticTrajectoryMeasure policy initialState) := by
  unfold stochasticTrajectoryMeasure
  apply Concentration.hasSubgaussianMGF_compProd_of_forall_fintype
    initialState
    (source.stochasticTrajectoryKernelRemaining policy mdp.horizon le_rfl)
  · exact MDP.measurable_maskedRewardDeviationAt_trajectory mdp
      stage state action
  · intro initial
    exact source.stochasticTrajectoryKernelRemaining_maskedRewardDeviationAt_hasSubgaussianMGF
      policy mdp.horizon le_rfl initial stage state action varianceProxy law

/--
One iid episode's fixed-coordinate masked reward deviation. The receiver keeps
this structural coordinate on the same source-indexed API as its law theorems;
the pointwise value itself depends only on the sampled trajectory and the MDP.
-/
def maskedRewardDeviationAtEpisode (source : MeanCompatibleRewardKernel mdp)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    {episodes : Nat} (episode : Fin episodes)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon) : Real :=
  mdp.maskedRewardDeviationAt (trajectories episode).1
    (trajectories episode).2 stage state action

/-- Fixed-coordinate masked reward deviations are independent across iid episodes. -/
theorem iIndepFun_maskedRewardDeviationAtEpisode
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    ProbabilityTheory.iIndepFun
      (source.maskedRewardDeviationAtEpisode stage state action)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  unfold iidStochasticTrajectoryFamilyMeasure
  simpa [maskedRewardDeviationAtEpisode] using
    (ProbabilityTheory.iIndepFun_pi fun _episode : Fin episodes =>
      (MDP.measurable_maskedRewardDeviationAt_trajectory mdp
        stage state action).aemeasurable)

/-- Every iid episode coordinate inherits the complete-trajectory masked reward MGF. -/
theorem maskedRewardDeviationAtEpisode_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy)
    {episodes : Nat} (episode : Fin episodes) :
    ProbabilityTheory.HasSubgaussianMGF
      (source.maskedRewardDeviationAtEpisode stage state action episode)
      varianceProxy
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  have hbase :=
    source.stochasticTrajectoryMeasure_maskedRewardDeviationAt_hasSubgaussianMGF
      policy initialState stage state action varianceProxy law
  rw [← source.iidStochasticTrajectoryFamilyMeasure_map_eval
    policy initialState episode] at hbase
  have hlift := ProbabilityTheory.HasSubgaussianMGF.of_map
    (μ := source.iidStochasticTrajectoryFamilyMeasure
      policy initialState episodes)
    (Y := Function.eval episode)
    (X := fun trajectory : State × RewardStepTrace Action State mdp.horizon =>
      mdp.maskedRewardDeviationAt trajectory.1 trajectory.2 stage state action)
    (measurable_pi_apply episode).aemeasurable hbase
  simpa [maskedRewardDeviationAtEpisode, Function.comp_def] using hlift

/-- The iid fixed-coordinate reward-deviation sum has the episode-linear proxy. -/
theorem iidStochasticTrajectoryFamilyMeasure_maskedRewardDeviation_sum_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun trajectories => ∑ episode : Fin episodes,
        source.maskedRewardDeviationAtEpisode stage state action episode trajectories)
      ((episodes : NNReal) * varianceProxy)
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes) := by
  have hsum := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
    (source.iIndepFun_maskedRewardDeviationAtEpisode
      policy initialState episodes stage state action)
    (s := Finset.univ)
    (c := fun _episode : Fin episodes => varianceProxy)
    (fun episode _ => source.maskedRewardDeviationAtEpisode_hasSubgaussianMGF
      policy initialState stage state action varianceProxy law episode)
  simpa using hsum

/-- Fixed-coordinate two-sided reward-sum tail under the iid stochastic family law. -/
theorem iidStochasticTrajectoryFamilyMeasure_maskedRewardDeviation_sum_abs_tail_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (episodes : Nat) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (source.iidStochasticTrajectoryFamilyMeasure policy initialState episodes)
        {trajectories |
          Concentration.subGaussianSumConfidenceRadius
              ((episodes : NNReal) * varianceProxy) delta <=
            |∑ episode : Fin episodes,
              source.maskedRewardDeviationAtEpisode
                stage state action episode trajectories|} <=
      ENNReal.ofReal delta := by
  simpa using
    (Concentration.subGaussian_sum_abs_tail_ennreal_delta_of_iIndepFun
      (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes)
      (source.iIndepFun_maskedRewardDeviationAtEpisode
        policy initialState episodes stage state action)
      (s := Finset.univ)
      (c := fun _episode : Fin episodes => varianceProxy)
      (fun episode _ => source.maskedRewardDeviationAtEpisode_hasSubgaussianMGF
        policy initialState stage state action varianceProxy law episode)
      (by simpa using htotal) delta hdelta hdelta_le_one)

end MDP.MeanCompatibleRewardKernel

end FiniteHorizonRL
end BanditRLProof
