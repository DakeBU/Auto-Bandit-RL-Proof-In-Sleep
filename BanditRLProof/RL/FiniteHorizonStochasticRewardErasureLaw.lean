import BanditRLProof.RL.FiniteHorizonIIDTrajectoryBatch
import BanditRLProof.RL.FiniteHorizonStochasticRewardIIDTotalReturnConcentration
import BanditRLProof.RL.FiniteHorizonStochasticRewardBellmanInnovationConcentration

/-!
# Finite-horizon stochastic reward erasure laws

This module discards sampled Real rewards from generated stochastic-reward
trajectories while retaining every action and next state.  The resulting law is
exactly the ordinary finite-horizon policy trajectory law.  The equality is
then lifted through the initial-state mixture, a finite iid episode family, and
the existing known-reward `EpisodeBatch` conversion.

The projected batch deliberately reinstates the deterministic mean reward
`mdp.reward`.  This is a law transport for transition-learning algorithms with
known mean rewards, not a stochastic reward-estimation theorem.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace RewardStepTrace

/-- Discard sampled rewards while retaining every action and next state. -/
def eraseRewards (remaining : Nat) :
    RewardStepTrace Action State remaining -> StepTrace Action State remaining :=
  fun trace coordinate => ((trace coordinate).1, (trace coordinate).2.2)

omit [Fintype State] [Fintype Action] in
/-- Coordinatewise reward erasure is measurable on the finite Pi-space. -/
theorem measurable_eraseRewards (remaining : Nat) :
    Measurable (eraseRewards (Action := Action) (State := State) remaining) := by
  apply measurable_pi_lambda
  intro coordinate
  exact (measurable_fst.prodMk measurable_snd.snd).comp
    (measurable_pi_apply coordinate)

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action] in
/-- Reward erasure commutes with prepending one generated coordinate. -/
@[simp]
theorem eraseRewards_cons (remaining : Nat)
    (head : Action × (Real × State))
    (tail : RewardStepTrace Action State remaining) :
    eraseRewards (Action := Action) (State := State) (remaining + 1)
        (@Fin.cons remaining (fun _ => Action × (Real × State)) head tail) =
      @Fin.cons remaining (fun _ => Action × State)
        (head.1, head.2.2)
        (eraseRewards (Action := Action) (State := State) remaining tail) := by
  funext coordinate
  refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate <;> simp [eraseRewards]

end RewardStepTrace

namespace ProbabilityTheory

/--
Map both outputs of a composition-product kernel when the mapped head kernel and
every mapped tail fiber agree with prescribed target kernels.
-/
theorem compProd_map_prodMap_of_map_eq
    {Alpha Beta Beta' Gamma Gamma' : Type*}
    [MeasurableSpace Alpha] [MeasurableSpace Beta] [MeasurableSpace Beta']
    [MeasurableSpace Gamma] [MeasurableSpace Gamma']
    (kappa : ProbabilityTheory.Kernel Alpha Beta)
      [ProbabilityTheory.IsMarkovKernel kappa]
    (eta : ProbabilityTheory.Kernel (Alpha × Beta) Gamma)
      [ProbabilityTheory.IsMarkovKernel eta]
    (kappa' : ProbabilityTheory.Kernel Alpha Beta')
      [ProbabilityTheory.IsMarkovKernel kappa']
    (eta' : ProbabilityTheory.Kernel (Alpha × Beta') Gamma')
      [ProbabilityTheory.IsMarkovKernel eta']
    (f : Beta -> Beta') (hf : Measurable f)
    (g : Gamma -> Gamma') (hg : Measurable g)
    (hkappa : kappa.map f = kappa')
    (heta : forall alpha beta,
      (eta (alpha, beta)).map g = eta' (alpha, f beta)) :
    (kappa.compProd eta).map (Prod.map f g) =
      kappa'.compProd eta' := by
  apply ProbabilityTheory.Kernel.ext
  intro alpha
  apply Measure.ext_prod
  intro betaSet gammaSet hbetaSet hgammaSet
  have hprodMap : Measurable (Prod.map f g) := hf.prodMap hg
  rw [ProbabilityTheory.Kernel.map_apply _ hprodMap]
  rw [Measure.map_apply hprodMap (hbetaSet.prod hgammaSet)]
  have hpreimage :
      Prod.map f g ⁻¹' (betaSet ×ˢ gammaSet) =
        (f ⁻¹' betaSet) ×ˢ (g ⁻¹' gammaSet) := by
    ext pair
    simp
  rw [hpreimage, ProbabilityTheory.Kernel.compProd_apply_prod (hbetaSet.preimage hf)
    (hgammaSet.preimage hg)]
  rw [ProbabilityTheory.Kernel.compProd_apply_prod hbetaSet hgammaSet]
  have htail (beta : Beta) :
      eta (alpha, beta) (g ⁻¹' gammaSet) =
        eta' (alpha, f beta) gammaSet := by
    have h := congrArg (fun mu : Measure Gamma' => mu gammaSet) (heta alpha beta)
    simpa [Measure.map_apply hg hgammaSet] using h
  simp_rw [htail]
  let q : Beta' -> ENNReal := fun beta => eta' (alpha, beta) gammaSet
  have hq : Measurable q :=
    (eta'.measurable_coe hgammaSet).comp
      (measurable_const.prodMk measurable_id)
  change
    (∫⁻ beta in f ⁻¹' betaSet, q (f beta) ∂kappa alpha) =
      ∫⁻ beta in betaSet, q beta ∂kappa' alpha
  rw [← MeasureTheory.setLIntegral_map hbetaSet hq hf]
  rw [← ProbabilityTheory.Kernel.map_apply kappa hf alpha, hkappa]

end ProbabilityTheory

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/--
Dropping all sampled rewards from a generated finite stochastic trajectory
recovers the ordinary action/next-state trajectory kernel exactly.
-/
theorem stochasticTrajectoryKernelRemaining_map_eraseRewards
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    (source.stochasticTrajectoryKernelRemaining policy remaining hremaining).map
        (RewardStepTrace.eraseRewards
          (Action := Action) (State := State) remaining) =
      policy.trajectoryKernelRemaining remaining hremaining := by
  induction remaining with
  | zero =>
      rw [stochasticTrajectoryKernelRemaining, MarkovPolicy.trajectoryKernelRemaining]
      apply ProbabilityTheory.Kernel.ext
      intro state
      rw [ProbabilityTheory.Kernel.map_apply _
        (RewardStepTrace.measurable_eraseRewards 0)]
      rw [ProbabilityTheory.Kernel.deterministic_apply,
        ProbabilityTheory.Kernel.deterministic_apply]
      rw [Measure.map_dirac]
      congr 1
      funext coordinate
      exact Fin.elim0 coordinate
  | succ remaining ih =>
      let dropReward : Action × (Real × State) -> Action × State :=
        fun head => (head.1, head.2.2)
      let eraseTail : RewardStepTrace Action State remaining ->
          StepTrace Action State remaining :=
        RewardStepTrace.eraseRewards remaining
      let stochasticTail : ProbabilityTheory.Kernel
          (State × (Action × (Real × State)))
          (RewardStepTrace Action State remaining) :=
        (source.stochasticTrajectoryKernelRemaining policy remaining (by omega)).comap
          (fun pair : State × (Action × (Real × State)) => pair.2.2.2)
          measurable_snd.snd.snd
      let deterministicTail : ProbabilityTheory.Kernel
          (State × (Action × State)) (StepTrace Action State remaining) :=
        (policy.trajectoryKernelRemaining remaining (by omega)).comap
          (fun pair : State × (Action × State) => pair.2.2)
          measurable_snd.snd
      let stochasticCons :
          (Action × (Real × State)) × RewardStepTrace Action State remaining ->
            RewardStepTrace Action State (remaining + 1) :=
        fun pair => @Fin.cons remaining
          (fun _ => Action × (Real × State)) pair.1 pair.2
      let deterministicCons :
          (Action × State) × StepTrace Action State remaining ->
            StepTrace Action State (remaining + 1) :=
        fun pair => @Fin.cons remaining (fun _ => Action × State) pair.1 pair.2
      have hdropReward : Measurable dropReward :=
        measurable_fst.prodMk measurable_snd.snd
      have heraseTail : Measurable eraseTail :=
        RewardStepTrace.measurable_eraseRewards remaining
      have hstochasticCons : Measurable stochasticCons :=
        RewardStepTrace.measurable_cons remaining
      have hdeterministicCons : Measurable deterministicCons :=
        StepTrace.measurable_cons remaining
      have htail : forall state head,
          (stochasticTail (state, head)).map eraseTail =
            deterministicTail (state, dropReward head) := by
        intro state head
        simp only [stochasticTail, deterministicTail,
          ProbabilityTheory.Kernel.comap_apply]
        change
          Measure.map eraseTail
              ((source.stochasticTrajectoryKernelRemaining policy remaining
                (by omega)) head.2.2) =
            (policy.trajectoryKernelRemaining remaining (by omega)) head.2.2
        rw [← ProbabilityTheory.Kernel.map_apply _ heraseTail]
        exact congrArg
          (fun kernel : ProbabilityTheory.Kernel State
              (StepTrace Action State remaining) => kernel head.2.2)
          (ih (by omega))
      have hpairMap :
          ((source.actionRewardStateKernel policy
              ⟨mdp.horizon - (remaining + 1), by omega⟩).compProd
            stochasticTail).map (Prod.map dropReward eraseTail) =
          (policy.actionStateKernel
              ⟨mdp.horizon - (remaining + 1), by omega⟩).compProd
            deterministicTail := by
        apply ProbabilityTheory.compProd_map_prodMap_of_map_eq
          _ _ _ _ dropReward hdropReward eraseTail heraseTail
        · exact source.actionRewardStateKernel_map_dropReward policy _
        · exact htail
      rw [stochasticTrajectoryKernelRemaining,
        MarkovPolicy.trajectoryKernelRemaining]
      change
        (((source.actionRewardStateKernel policy
            ⟨mdp.horizon - (remaining + 1), by omega⟩).compProd
          stochasticTail).map stochasticCons).map
            (RewardStepTrace.eraseRewards (remaining + 1)) =
          ((policy.actionStateKernel
            ⟨mdp.horizon - (remaining + 1), by omega⟩).compProd
          deterministicTail).map deterministicCons
      rw [← ProbabilityTheory.Kernel.map_comp_right _ hstochasticCons
        (RewardStepTrace.measurable_eraseRewards (remaining + 1))]
      have hcommute :
          RewardStepTrace.eraseRewards (remaining + 1) ∘ stochasticCons =
            deterministicCons ∘ Prod.map dropReward eraseTail := by
        funext pair
        exact RewardStepTrace.eraseRewards_cons remaining pair.1 pair.2
      rw [hcommute]
      rw [ProbabilityTheory.Kernel.map_comp_right _
        (hdropReward.prodMap heraseTail) hdeterministicCons]
      rw [hpairMap]

/-- Erase sampled rewards from a full stochastic trajectory, retaining its initial state. -/
def eraseTrajectory
    (trajectory : State × RewardStepTrace Action State mdp.horizon) :
    State × StepTrace Action State mdp.horizon :=
  (trajectory.1, RewardStepTrace.eraseRewards mdp.horizon trajectory.2)

/-- Full-trajectory reward erasure is measurable. -/
theorem measurable_eraseTrajectory :
    Measurable (eraseTrajectory (mdp := mdp) (Action := Action)) :=
  measurable_fst.prodMk
    ((RewardStepTrace.measurable_eraseRewards mdp.horizon).comp measurable_snd)

/-- The full stochastic trajectory law maps exactly to the ordinary trajectory law. -/
theorem stochasticTrajectoryMeasure_map_eraseTrajectory
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    (source.stochasticTrajectoryMeasure policy initialState).map
        (eraseTrajectory (mdp := mdp) (Action := Action)) =
      policy.trajectoryMeasure initialState := by
  unfold stochasticTrajectoryMeasure MarkovPolicy.trajectoryMeasure
  have hkernel := source.stochasticTrajectoryKernelRemaining_map_eraseRewards
    policy mdp.horizon le_rfl
  rw [← hkernel]
  simpa only [eraseTrajectory] using
    (Measure.compProd_map
      (μ := initialState)
      (κ := source.stochasticTrajectoryKernelRemaining
        policy mdp.horizon le_rfl)
      (f := RewardStepTrace.eraseRewards mdp.horizon)
      (RewardStepTrace.measurable_eraseRewards mdp.horizon)).symm

/-- Erase sampled rewards coordinatewise from a finite iid trajectory family. -/
def eraseTrajectoryFamily (episodes : Nat)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon) :
    Fin episodes -> State × StepTrace Action State mdp.horizon :=
  fun episode => eraseTrajectory (mdp := mdp) (trajectories episode)

/-- Finite-family reward erasure is measurable. -/
theorem measurable_eraseTrajectoryFamily (episodes : Nat) :
    Measurable (eraseTrajectoryFamily
      (mdp := mdp) (Action := Action) episodes) := by
  apply measurable_pi_lambda
  intro episode
  exact measurable_eraseTrajectory.comp (measurable_pi_apply episode)

/-- Finite iid stochastic trajectories map to the deterministic iid family law. -/
theorem iidStochasticTrajectoryFamilyMeasure_map_eraseTrajectoryFamily
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) :
    (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes).map
        (eraseTrajectoryFamily (mdp := mdp) (Action := Action) episodes) =
      policy.iidTrajectoryFamilyMeasure initialState episodes := by
  unfold iidStochasticTrajectoryFamilyMeasure
    MarkovPolicy.iidTrajectoryFamilyMeasure eraseTrajectoryFamily
  rw [Measure.pi_map_pi (fun _ => measurable_eraseTrajectory.aemeasurable)]
  congr 1
  funext episode
  exact source.stochasticTrajectoryMeasure_map_eraseTrajectory
    policy initialState

end MDP.MeanCompatibleRewardKernel

namespace MDP
namespace MeanCompatibleRewardKernel

variable {mdp : MDP State Action}
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

/--
Convert a stochastic trajectory family to the existing empirical batch after
erasing rewards.  Batch rewards are the known means `mdp.reward`.
-/
def knownRewardEpisodeBatchOfStochasticTrajectories (episodes : Nat)
    (trajectories : Fin episodes ->
      State × RewardStepTrace Action State mdp.horizon) :
    EpisodeBatch mdp episodes :=
  mdp.episodeBatchOfTrajectories episodes
    (eraseTrajectoryFamily (mdp := mdp) episodes trajectories)

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- The known-reward stochastic-family batch projection is measurable. -/
theorem measurable_knownRewardEpisodeBatchOfStochasticTrajectories
    (episodes : Nat) :
    Measurable (knownRewardEpisodeBatchOfStochasticTrajectories
      (mdp := mdp) episodes) :=
  (mdp.measurable_episodeBatchOfTrajectories episodes).comp
    (measurable_eraseTrajectoryFamily episodes)

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/--
The known-reward batch extracted from iid stochastic trajectories has exactly
the existing deterministic iid episode-batch law.
-/
theorem iidStochasticTrajectoryFamilyMeasure_map_knownRewardEpisodeBatch_eq_iidEpisodeBatchMeasure
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) :
    (source.iidStochasticTrajectoryFamilyMeasure
        policy initialState episodes).map
        (knownRewardEpisodeBatchOfStochasticTrajectories
          (mdp := mdp) episodes) =
      policy.iidEpisodeBatchMeasure initialState episodes := by
  unfold knownRewardEpisodeBatchOfStochasticTrajectories
    MarkovPolicy.iidEpisodeBatchMeasure
  change
    (source.iidStochasticTrajectoryFamilyMeasure
      policy initialState episodes).map
        (mdp.episodeBatchOfTrajectories episodes ∘
          eraseTrajectoryFamily (mdp := mdp) episodes) = _
  rw [← Measure.map_map
    (mdp.measurable_episodeBatchOfTrajectories episodes)
    (measurable_eraseTrajectoryFamily episodes)]
  rw [source.iidStochasticTrajectoryFamilyMeasure_map_eraseTrajectoryFamily]

end MeanCompatibleRewardKernel
end MDP

end FiniteHorizonRL
end BanditRLProof
