import BanditRLProof.Algorithms.ThompsonClippedUCBScore
import BanditRLProof.Algorithms.UCBArmStreamTail
import Mathlib.Probability.Kernel.Representation

/-!
# Stationary reward kernels for the Thompson concentration route

This module isolates the stationary feedback adapter and the algorithm-independent
latent-arm-stream tail used by the Thompson Bayesian-regret route.  The tail
theorems deliberately quantify over an arbitrary action trace: only the
next-unused-coordinate reward rule and the product arm-stream law matter.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

namespace Thompson

universe u

/-- Uniform random table used to represent all stationary reward-kernel draws. -/
abbrev UnitArmStream (K : Nat) :=
  Nat -> Fin K -> Set.Icc (0 : Real) 1

/-- Independent uniform coordinates indexed by pull number and arm. -/
noncomputable def uniformUnitArmStreamMeasure (K : Nat) :
    Measure (UnitArmStream K) :=
  Measure.infinitePi fun _ : Nat =>
    Measure.infinitePi fun _ : Fin K => volume

instance instUniformUnitArmStreamMeasureIsProbability (K : Nat) :
    IsProbabilityMeasure (uniformUnitArmStreamMeasure K) := by
  unfold uniformUnitArmStreamMeasure
  infer_instance

/-- A fixed measurable uniform-randomness representation of a reward kernel. -/
noncomputable def stationaryRewardSampler
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel] :
    (Env × Fin K) -> Set.Icc (0 : Real) 1 -> Real :=
  Classical.choose rewardKernel.exists_measurable_map_eq_unitInterval

theorem measurable_uncurry_stationaryRewardSampler
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel] :
    Measurable (Function.uncurry (stationaryRewardSampler rewardKernel)) :=
  (Classical.choose_spec rewardKernel.exists_measurable_map_eq_unitInterval).1

theorem stationaryRewardSampler_map_volume
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel]
    (input : Env × Fin K) :
    Measure.map (stationaryRewardSampler rewardKernel input) volume =
      rewardKernel input :=
  (Classical.choose_spec rewardKernel.exists_measurable_map_eq_unitInterval).2 input

/-- Turn one environment and one uniform table into its latent reward table. -/
noncomputable def rewardStreamOfUnitArmStream
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel] :
    Env × UnitArmStream K -> UCB.ArmRewardStream K :=
  fun input i arm =>
    stationaryRewardSampler rewardKernel (input.1, arm) (input.2 i arm)

theorem measurable_rewardStreamOfUnitArmStream
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel] :
    Measurable (rewardStreamOfUnitArmStream rewardKernel) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun arm => ?_
  exact (measurable_uncurry_stationaryRewardSampler rewardKernel).comp
    ((measurable_fst.prodMk measurable_const).prodMk
      ((measurable_pi_apply arm).comp
        ((measurable_pi_apply i).comp measurable_snd)))

/-- The arm-indexed reward kernel obtained by freezing the environment. -/
noncomputable def stationaryRewardKernelAt
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel]
    (env : Env) : Kernel (Fin K) Real :=
  rewardKernel.comap (Prod.mk env) (measurable_const.prodMk measurable_id)

instance instStationaryRewardKernelAtIsMarkov
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel]
    (env : Env) : IsMarkovKernel (stationaryRewardKernelAt rewardKernel env) := by
  unfold stationaryRewardKernelAt
  infer_instance

@[simp]
theorem stationaryRewardKernelAt_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel]
    (env : Env) (arm : Fin K) :
    stationaryRewardKernelAt rewardKernel env arm = rewardKernel (env, arm) := by
  rw [stationaryRewardKernelAt, Kernel.comap_apply]

/-- Markov kernel that samples an independent latent reward stream at each environment. -/
noncomputable def stationaryArmStreamKernel
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel] :
    Kernel Env (UCB.ArmRewardStream K) :=
  (Kernel.id ×ₖ Kernel.const Env (uniformUnitArmStreamMeasure K)).map
    (rewardStreamOfUnitArmStream rewardKernel)

instance instStationaryArmStreamKernelIsMarkov
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel] :
    IsMarkovKernel (stationaryArmStreamKernel rewardKernel) := by
  unfold stationaryArmStreamKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_rewardStreamOfUnitArmStream rewardKernel)

/-- At a fixed environment, the sampled latent table has the canonical product arm-stream law. -/
theorem stationaryArmStreamKernel_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel]
    (env : Env) :
    stationaryArmStreamKernel rewardKernel env =
      UCB.armStreamMeasure (stationaryRewardKernelAt rewardKernel env) := by
  rw [stationaryArmStreamKernel, Kernel.map_apply _
    (measurable_rewardStreamOfUnitArmStream rewardKernel)]
  have hbase :
      (Kernel.id ×ₖ Kernel.const Env (uniformUnitArmStreamMeasure K)) env =
        Measure.map (Prod.mk env) (uniformUnitArmStreamMeasure K) := by
    ext s hs
    rw [Kernel.id_prod_apply' _ _ hs, Kernel.const_apply]
    exact (Measure.map_apply
      (measurable_const.prodMk measurable_id) hs).symm
  rw [hbase, Measure.map_map]
  · change Measure.map
        (fun stream : UnitArmStream K =>
          fun i arm => stationaryRewardSampler rewardKernel (env, arm) (stream i arm))
        (uniformUnitArmStreamMeasure K) = _
    have hcoord (arm : Fin K) : Measurable
        (fun u : Set.Icc (0 : Real) 1 =>
          stationaryRewardSampler rewardKernel (env, arm) u) :=
      (measurable_uncurry_stationaryRewardSampler rewardKernel).comp
        (measurable_const.prodMk measurable_id)
    have hrow : Measurable
        (fun row : Fin K -> Set.Icc (0 : Real) 1 =>
          fun arm => stationaryRewardSampler rewardKernel (env, arm) (row arm)) :=
      measurable_pi_lambda _ fun arm =>
        (hcoord arm).comp (measurable_pi_apply arm)
    calc
      _ = Measure.infinitePi (fun _ : Nat =>
          (Measure.infinitePi fun _ : Fin K => volume).map
            (fun row arm =>
              stationaryRewardSampler rewardKernel (env, arm) (row arm))) := by
        exact Measure.infinitePi_map_pi
          (fun _ : Nat => Measure.infinitePi fun _ : Fin K => volume)
          (f := fun _ row arm =>
            stationaryRewardSampler rewardKernel (env, arm) (row arm))
          (fun _ => hrow)
      _ = Measure.infinitePi (fun _ : Nat =>
          Measure.infinitePi fun arm : Fin K => rewardKernel (env, arm)) := by
        congr 1
        funext i
        calc
          _ = Measure.infinitePi (fun arm : Fin K =>
                volume.map (stationaryRewardSampler rewardKernel (env, arm))) := by
              exact Measure.infinitePi_map_pi
                (fun _ : Fin K => volume)
                (f := fun arm u =>
                  stationaryRewardSampler rewardKernel (env, arm) u)
                hcoord
          _ = _ := by
            simp_rw [stationaryRewardSampler_map_volume rewardKernel]
      _ = UCB.armStreamMeasure
          (stationaryRewardKernelAt rewardKernel env) := by
        simp [UCB.armStreamMeasure, stationaryRewardKernelAt_apply]
  · exact measurable_rewardStreamOfUnitArmStream rewardKernel
  · exact measurable_const.prodMk measurable_id

/-- A stationary reward kernel is a measurable history environment that ignores history. -/
noncomputable def stationaryMeasurableHistoryEnvironment
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel] :
    MeasurableHistoryEnvironment Env (Fin K) Real where
  initialFeedback := rewardKernel
  feedback _ := rewardKernel.comap
    (fun input => (input.1, input.2.2)) (by fun_prop)

@[simp]
theorem stationaryMeasurableHistoryEnvironment_initialFeedback
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel] :
    (stationaryMeasurableHistoryEnvironment rewardKernel).initialFeedback =
      rewardKernel := rfl

@[simp]
theorem stationaryMeasurableHistoryEnvironment_feedback_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel]
    (n : Nat) (env : Env)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    (stationaryMeasurableHistoryEnvironment rewardKernel).feedback n
        (env, (history, arm)) =
      rewardKernel (env, arm) := by
  rw [stationaryMeasurableHistoryEnvironment, Kernel.comap_apply]

@[simp]
theorem stationaryMeasurableHistoryEnvironment_at_initialFeedback_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel]
    (env : Env) (arm : Fin K) :
    ((stationaryMeasurableHistoryEnvironment rewardKernel).at env).initialFeedback arm =
      rewardKernel (env, arm) := by
  rw [MeasurableHistoryEnvironment.at, Kernel.comap_apply]
  rfl

@[simp]
theorem stationaryMeasurableHistoryEnvironment_at_feedback_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (rewardKernel : Kernel (Env × Fin K) Real) [IsMarkovKernel rewardKernel]
    (env : Env) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    ((stationaryMeasurableHistoryEnvironment rewardKernel).at env).feedback n
        (history, arm) =
      rewardKernel (env, arm) := by
  rw [MeasurableHistoryEnvironment.at, Kernel.comap_apply,
    stationaryMeasurableHistoryEnvironment_feedback_apply]

/-- Initial reward read from coordinate zero of the selected latent arm. -/
def latentArmStreamInitialReward
    {Env : Type u} {K : Nat} :
    ((Env × UCB.ArmRewardStream K) × Fin K) → Real :=
  fun input => input.1.2 0 input.2

theorem measurable_latentArmStreamInitialReward
    {Env : Type u} {K : Nat} [MeasurableSpace Env] :
    Measurable (latentArmStreamInitialReward (Env := Env) (K := K)) := by
  exact UCB.measurable_armRewardStream_apply.comp
    ((measurable_snd.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))

/-- Next unused reward coordinate determined by the visible finite history. -/
noncomputable def latentArmStreamNextReward
    {Env : Type u} {K : Nat} (n : Nat) :
    ((Env × UCB.ArmRewardStream K) ×
      (History.FinitePairHistory (Fin K) Real n × Fin K)) → Real :=
  fun input =>
    input.1.2 (ETC.realHistoryPullCount n input.2.1 input.2.2) input.2.2

theorem measurable_latentArmStreamNextReward
    {Env : Type u} {K : Nat} [MeasurableSpace Env] (n : Nat) :
    Measurable (latentArmStreamNextReward (Env := Env) (K := K) n) := by
  have hcountEval : Measurable
      (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
        ETC.realHistoryPullCount n input.1 input.2) := by
    apply measurable_from_prod_countable_left
    intro arm
    exact UCB.measurable_realHistoryPullCount n arm
  have hcountArm : Measurable
      (fun input : ((Env × UCB.ArmRewardStream K) ×
          (History.FinitePairHistory (Fin K) Real n × Fin K)) =>
        (ETC.realHistoryPullCount n input.2.1 input.2.2, input.2.2)) :=
    (hcountEval.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)
  exact UCB.measurable_armRewardStream_apply.comp
    ((measurable_snd.comp measurable_fst).prodMk hcountArm)

/--
Measurable deterministic feedback environment that exposes a latent reward
table through the next-unused-coordinate rule.  The first environment
component is retained for the Bayesian model but does not affect feedback.
-/
noncomputable def latentArmStreamMeasurableHistoryEnvironment
    {Env : Type u} {K : Nat} [MeasurableSpace Env] :
    MeasurableHistoryEnvironment
      (Env × UCB.ArmRewardStream K) (Fin K) Real where
  initialFeedback := Kernel.deterministic latentArmStreamInitialReward
    measurable_latentArmStreamInitialReward
  feedback n := Kernel.deterministic (latentArmStreamNextReward n)
    (measurable_latentArmStreamNextReward n)

@[simp]
theorem latentArmStreamMeasurableHistoryEnvironment_initialFeedback_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (env : Env) (stream : UCB.ArmRewardStream K) (arm : Fin K) :
    (latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K)).initialFeedback
        ((env, stream), arm) = Measure.dirac (stream 0 arm) := by
  rw [latentArmStreamMeasurableHistoryEnvironment, Kernel.deterministic_apply]
  rfl

@[simp]
theorem latentArmStreamMeasurableHistoryEnvironment_feedback_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (n : Nat) (env : Env) (stream : UCB.ArmRewardStream K)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    (latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K)).feedback n
        ((env, stream), (history, arm)) =
      Measure.dirac (stream (ETC.realHistoryPullCount n history arm) arm) := by
  rw [latentArmStreamMeasurableHistoryEnvironment, Kernel.deterministic_apply]
  rfl

theorem measurable_latentArmStreamNextReward_fixed
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (n : Nat) (env : Env) (stream : UCB.ArmRewardStream K) :
    Measurable
      (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
        stream (ETC.realHistoryPullCount n input.1 input.2) input.2) := by
  have hinput : Measurable
      (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
        ((env, stream), input)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_apply, latentArmStreamNextReward] using
    (measurable_latentArmStreamNextReward (Env := Env) (K := K) n).comp
      hinput

@[simp]
theorem latentArmStreamMeasurableHistoryEnvironment_at_initialFeedback_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (env : Env) (stream : UCB.ArmRewardStream K) (arm : Fin K) :
    ((latentArmStreamMeasurableHistoryEnvironment
        (Env := Env) (K := K)).at (env, stream)).initialFeedback arm =
      Measure.dirac (stream 0 arm) := by
  rw [MeasurableHistoryEnvironment.at, Kernel.comap_apply,
    latentArmStreamMeasurableHistoryEnvironment_initialFeedback_apply]

@[simp]
theorem latentArmStreamMeasurableHistoryEnvironment_at_feedback_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (n : Nat) (env : Env) (stream : UCB.ArmRewardStream K)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    ((latentArmStreamMeasurableHistoryEnvironment
        (Env := Env) (K := K)).at (env, stream)).feedback n (history, arm) =
      Measure.dirac (stream (ETC.realHistoryPullCount n history arm) arm) := by
  rw [MeasurableHistoryEnvironment.at, Kernel.comap_apply,
    latentArmStreamMeasurableHistoryEnvironment_feedback_apply]

/-- The initial canonical reward reads coordinate zero of the selected arm. -/
theorem canonicalLatentArmStreamTrajectory_reward_zero_ae
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (env : Env) (stream : UCB.ArmRewardStream K) :
    ∀ᵐ trajectory ∂
        canonicalMeasurableEnvironmentTrajectoryKernel algorithm
          (latentArmStreamMeasurableHistoryEnvironment
            (Env := Env) (K := K)) (env, stream),
      (trajectory 0).2 = stream 0 (trajectory 0).1 := by
  let environment := latentArmStreamMeasurableHistoryEnvironment
    (Env := Env) (K := K)
  let trajectoryKernel :=
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  let mu := trajectoryKernel (env, stream)
  have hzero :
      mu.map (fun trajectory => trajectory 0) =
        algorithm.initialAction ⊗ₘ
          (environment.at (env, stream)).initialFeedback := by
    have hkernel := congrArg
      (fun kernel : Kernel (Env × UCB.ArmRewardStream K) (Fin K × Real) =>
        kernel (env, stream))
      (canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero
        algorithm environment)
    dsimp only at hkernel
    rw [Kernel.map_apply _ (measurable_pi_apply 0),
      measurableEnvironmentInitialPairKernel_apply] at hkernel
    simpa [mu, trajectoryKernel] using hkernel
  have hp : MeasurableSet
      {pair : Fin K × Real | pair.2 = stream 0 pair.1} :=
    measurableSet_eq_fun measurable_snd
      ((measurable_of_countable (fun arm : Fin K => stream 0 arm)).comp
        measurable_fst)
  have hpair : ∀ᵐ pair ∂
      algorithm.initialAction ⊗ₘ
        (environment.at (env, stream)).initialFeedback,
      pair.2 = stream 0 pair.1 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with arm
    rw [latentArmStreamMeasurableHistoryEnvironment_at_initialFeedback_apply]
    simp
  rw [← hzero] at hpair
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable hp).mp hpair

/-- Every shifted canonical reward reads the selected arm's next unused coordinate. -/
theorem canonicalLatentArmStreamTrajectory_reward_succ_ae
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (env : Env) (stream : UCB.ArmRewardStream K) (n : Nat) :
    ∀ᵐ trajectory ∂
        canonicalMeasurableEnvironmentTrajectoryKernel algorithm
          (latentArmStreamMeasurableHistoryEnvironment
            (Env := Env) (K := K)) (env, stream),
      (trajectory (n + 1)).2 =
        stream
          (pullCount
            (canonicalHistoryTrajectoryAction (Reward := Real) trajectory)
            (trajectory (n + 1)).1 (n + 1))
          (trajectory (n + 1)).1 := by
  let environment := latentArmStreamMeasurableHistoryEnvironment
    (Env := Env) (K := K)
  let trajectoryKernel :=
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  let mu := trajectoryKernel (env, stream)
  let joinPrefixNext := fun trajectory : (k : Nat) → Fin K × Real =>
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))
  have hnextFixed :=
    measurable_latentArmStreamNextReward_fixed n env stream
  have hp : MeasurableSet
      {sample : History.FinitePairHistory (Fin K) Real n × (Fin K × Real) |
        sample.2.2 =
          stream (ETC.realHistoryPullCount n sample.1 sample.2.1)
            sample.2.1} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd)
      (hnextFixed.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  have hkernel :
      mu.map joinPrefixNext =
        mu.map (Preorder.frestrictLe n) ⊗ₘ
          historyStepKernel algorithm (environment.at (env, stream)) n := by
    simpa [mu, trajectoryKernel, joinPrefixNext] using
      (canonicalMeasurableEnvironmentTrajectoryKernel_map_prefix_next_eq_compProd
        algorithm environment (env, stream) n)
  have hjoint : ∀ᵐ sample ∂
      mu.map (Preorder.frestrictLe n) ⊗ₘ
        historyStepKernel algorithm (environment.at (env, stream)) n,
      sample.2.2 =
        stream (ETC.realHistoryPullCount n sample.1 sample.2.1)
          sample.2.1 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with history
    have hpPair : MeasurableSet
        {pair : Fin K × Real |
          pair.2 = stream (ETC.realHistoryPullCount n history pair.1) pair.1} :=
      measurableSet_eq_fun measurable_snd
        (hnextFixed.comp (measurable_const.prodMk measurable_fst))
    rw [historyStepKernel,
      Kernel.compProd_apply_eq_compProd_sectR]
    apply Measure.ae_compProd_of_ae_ae hpPair
    filter_upwards [] with arm
    rw [Kernel.sectR_apply,
      latentArmStreamMeasurableHistoryEnvironment_at_feedback_apply]
    simp
  rw [← hkernel] at hjoint
  have hsource :=
    (ae_map_iff
      ((Preorder.measurable_frestrictLe n).prodMk
        (measurable_pi_apply (n + 1))).aemeasurable hp).mp hjoint
  filter_upwards [hsource] with trajectory htrajectory
  have hpref :
      Preorder.frestrictLe n trajectory =
        History.finitePairHistoryOfTrace
          (canonicalHistoryTrajectoryAction (Reward := Real) trajectory)
          (canonicalHistoryTrajectoryReward (Action := Fin K) trajectory) n :=
    rfl
  rw [hpref,
    ETC.realHistoryPullCount_finitePairHistoryOfTrace] at htrajectory
  simpa [mu, trajectoryKernel, canonicalHistoryTrajectoryAction] using htrajectory

/--
The canonical trajectory under deterministic latent-stream feedback has the
same reward trace as the pathwise next-unused-coordinate construction.
-/
theorem canonicalLatentArmStreamTrajectory_reward_eq_rewardFromArmStream_ae
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (env : Env) (stream : UCB.ArmRewardStream K) :
    canonicalHistoryTrajectoryReward =ᵐ[
        canonicalMeasurableEnvironmentTrajectoryKernel algorithm
          (latentArmStreamMeasurableHistoryEnvironment
            (Env := Env) (K := K)) (env, stream)]
      UCB.rewardFromArmStream canonicalHistoryTrajectoryAction
        (fun _ => stream) := by
  have hcoord : ∀ t, ∀ᵐ trajectory ∂
      canonicalMeasurableEnvironmentTrajectoryKernel algorithm
        (latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)) (env, stream),
      canonicalHistoryTrajectoryReward trajectory t =
        UCB.rewardFromArmStream canonicalHistoryTrajectoryAction
          (fun _ => stream) trajectory t := by
    intro t
    cases t with
    | zero =>
        simpa [canonicalHistoryTrajectoryReward,
          UCB.rewardFromArmStream, canonicalHistoryTrajectoryAction] using
          canonicalLatentArmStreamTrajectory_reward_zero_ae algorithm env stream
    | succ n =>
        simpa [canonicalHistoryTrajectoryReward,
          UCB.rewardFromArmStream, canonicalHistoryTrajectoryAction] using
          canonicalLatentArmStreamTrajectory_reward_succ_ae
            algorithm env stream n
  filter_upwards [ae_all_iff.2 hcoord] with trajectory htrajectory
  funext t
  exact htrajectory t

end Thompson

namespace UCB

/-- A next-unused arm-stream reward coordinate is measurable at each time. -/
theorem measurable_rewardFromArmStream_apply
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t, Measurable (fun omega => action omega t))
    (armStream : Omega -> ArmRewardStream K)
    (hmeasurable : forall i arm,
      Measurable (fun omega => armStream omega i arm))
    (t : Nat) :
    Measurable (fun omega => rewardFromArmStream action armStream omega t) := by
  have hstream : Measurable armStream :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun arm =>
      hmeasurable i arm
  have hcountEval : Measurable
      (fun input : Omega × Fin K =>
        pullCount (action input.1) input.2 t) := by
    apply measurable_from_prod_countable_left
    intro arm
    exact measurable_pullCount action haction arm t
  have hselected : Measurable (fun omega => action omega t) := haction t
  have hcount : Measurable
      (fun omega => pullCount (action omega) (action omega t) t) := by
    simpa only [Function.comp_apply] using
      hcountEval.comp (measurable_id.prodMk hselected)
  exact measurable_armRewardStream_apply.comp
    (hstream.prodMk (hcount.prodMk hselected))

/--
Adaptive-count upper tail on any sample space whose latent-stream projection
has the canonical stationary product law.  The action trace may use additional
algorithmic randomness carried by the sample space.
-/
theorem measure_sumRewards_sub_pullCount_mul_ge_le_of_armStream_identDistrib
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (armStream : Omega -> ArmRewardStream K)
    (hmeasurable : forall i arm,
      Measurable (fun omega => armStream omega i arm))
    (hstreamLaw : IdentDistrib armStream id mu (armStreamMeasure nu))
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    mu {omega : Omega |
        threshold (pullCount (action omega) arm n) <=
          sumRewards (action omega)
              (rewardFromArmStream action armStream omega) arm n -
            (pullCount (action omega) arm n : Real) * mean} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hs : MeasurableSet (upperDeviationPairs mean threshold) :=
    measurableSet_le
      ((measurable_of_countable threshold).comp measurable_fst)
      (measurable_snd.sub
        (((measurable_of_countable fun k : Nat => (k : Real)).comp
          measurable_fst).mul measurable_const))
  have hpeel :=
    measure_pullCount_prod_sumRewards_rewardFromArmStream_mem_le_identDistrib
      mu (armStreamMeasure nu) action armStream hmeasurable id hstreamLaw
      arm n (upperDeviationPairs mean threshold) hs
  have hprojected : forall k : Nat,
      exists value : Real,
        threshold k <= value - (k : Real) * mean := by
    intro k
    refine ⟨threshold k + (k : Real) * mean, ?_⟩
    linarith
  have hpeel' :
      mu {omega : Omega |
          threshold (pullCount (action omega) arm n) <=
            sumRewards (action omega)
                (rewardFromArmStream action armStream omega) arm n -
              (pullCount (action omega) arm n : Real) * mean} <=
        (Finset.range (n + 1)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            threshold k <=
              armPrefixSum arm k stream - (k : Real) * mean}) := by
    simpa [upperDeviationPairs, hprojected] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  exact measure_armPrefixSum_sub_mul_ge_le
    nu arm mean sigma2 hsubG k
      (hthreshold k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/-- Lower-tail counterpart of the arbitrary-sample latent-stream transport. -/
theorem measure_pullCount_mul_sub_sumRewards_ge_le_of_armStream_identDistrib
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (armStream : Omega -> ArmRewardStream K)
    (hmeasurable : forall i arm,
      Measurable (fun omega => armStream omega i arm))
    (hstreamLaw : IdentDistrib armStream id mu (armStreamMeasure nu))
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    mu {omega : Omega |
        threshold (pullCount (action omega) arm n) <=
          (pullCount (action omega) arm n : Real) * mean -
            sumRewards (action omega)
              (rewardFromArmStream action armStream omega) arm n} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hs : MeasurableSet (lowerDeviationPairs mean threshold) :=
    measurableSet_le
      ((measurable_of_countable threshold).comp measurable_fst)
      ((((measurable_of_countable fun k : Nat => (k : Real)).comp
          measurable_fst).mul measurable_const).sub
        measurable_snd)
  have hpeel :=
    measure_pullCount_prod_sumRewards_rewardFromArmStream_mem_le_identDistrib
      mu (armStreamMeasure nu) action armStream hmeasurable id hstreamLaw
      arm n (lowerDeviationPairs mean threshold) hs
  have hprojected : forall k : Nat,
      exists value : Real,
        threshold k <= (k : Real) * mean - value := by
    intro k
    refine ⟨(k : Real) * mean - threshold k, ?_⟩
    linarith
  have hpeel' :
      mu {omega : Omega |
          threshold (pullCount (action omega) arm n) <=
            (pullCount (action omega) arm n : Real) * mean -
              sumRewards (action omega)
                (rewardFromArmStream action armStream omega) arm n} <=
        (Finset.range (n + 1)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            threshold k <=
              (k : Real) * mean - armPrefixSum arm k stream}) := by
    simpa [lowerDeviationPairs, hprojected] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  exact measure_mul_sub_armPrefixSum_ge_le
    nu arm mean sigma2 hsubG k
      (hthreshold k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/-- Positive-count upper tail under an arbitrary algorithmic-randomness coupling. -/
theorem measure_pos_and_sumRewards_sub_pullCount_mul_ge_le_of_armStream_identDistrib
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (armStream : Omega -> ArmRewardStream K)
    (hmeasurable : forall i arm,
      Measurable (fun omega => armStream omega i arm))
    (hstreamLaw : IdentDistrib armStream id mu (armStreamMeasure nu))
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    mu {omega : Omega |
        0 < pullCount (action omega) arm n ∧
        threshold (pullCount (action omega) arm n) <=
          sumRewards (action omega)
              (rewardFromArmStream action armStream omega) arm n -
            (pullCount (action omega) arm n : Real) * mean} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hs : MeasurableSet (positiveUpperDeviationPairs mean threshold) :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le
        ((measurable_of_countable threshold).comp measurable_fst)
        (measurable_snd.sub
          (((measurable_of_countable fun k : Nat => (k : Real)).comp
            measurable_fst).mul measurable_const)))
  have hpeel :=
    measure_pullCount_prod_sumRewards_rewardFromArmStream_mem_le_identDistrib
      mu (armStreamMeasure nu) action armStream hmeasurable id hstreamLaw
      arm n (positiveUpperDeviationPairs mean threshold) hs
  have hprojected : forall k : Nat,
      0 < k -> exists value : Real,
        threshold k <= value - (k : Real) * mean := by
    intro k _hk
    refine ⟨threshold k + (k : Real) * mean, ?_⟩
    linarith
  have hprojection_iff : forall k : Nat,
      (0 < k ∧ exists value : Real,
        threshold k <= value - (k : Real) * mean) ↔ 0 < k := by
    intro k
    constructor
    · exact And.left
    · intro hk
      exact ⟨hk, hprojected k hk⟩
  have hpeel' :
      mu {omega : Omega |
          0 < pullCount (action omega) arm n ∧
          threshold (pullCount (action omega) arm n) <=
            sumRewards (action omega)
                (rewardFromArmStream action armStream omega) arm n -
              (pullCount (action omega) arm n : Real) * mean} <=
        ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            0 < k ∧ threshold k <=
              armPrefixSum arm k stream - (k : Real) * mean}) := by
    simpa [positiveUpperDeviationPairs, hprojection_iff] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  simpa [hk'.2] using
    (measure_armPrefixSum_sub_mul_ge_le
      nu arm mean sigma2 hsubG k
        (hthreshold k hk'.2
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk'.1))))

/-- Positive-count lower tail under an arbitrary algorithmic-randomness coupling. -/
theorem measure_pos_and_pullCount_mul_sub_sumRewards_ge_le_of_armStream_identDistrib
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (armStream : Omega -> ArmRewardStream K)
    (hmeasurable : forall i arm,
      Measurable (fun omega => armStream omega i arm))
    (hstreamLaw : IdentDistrib armStream id mu (armStreamMeasure nu))
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    mu {omega : Omega |
        0 < pullCount (action omega) arm n ∧
        threshold (pullCount (action omega) arm n) <=
          (pullCount (action omega) arm n : Real) * mean -
            sumRewards (action omega)
              (rewardFromArmStream action armStream omega) arm n} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hs : MeasurableSet (positiveLowerDeviationPairs mean threshold) :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le
        ((measurable_of_countable threshold).comp measurable_fst)
        ((((measurable_of_countable fun k : Nat => (k : Real)).comp
            measurable_fst).mul measurable_const).sub measurable_snd))
  have hpeel :=
    measure_pullCount_prod_sumRewards_rewardFromArmStream_mem_le_identDistrib
      mu (armStreamMeasure nu) action armStream hmeasurable id hstreamLaw
      arm n (positiveLowerDeviationPairs mean threshold) hs
  have hprojected : forall k : Nat,
      0 < k -> exists value : Real,
        threshold k <= (k : Real) * mean - value := by
    intro k _hk
    refine ⟨(k : Real) * mean - threshold k, ?_⟩
    linarith
  have hprojection_iff : forall k : Nat,
      (0 < k ∧ exists value : Real,
        threshold k <= (k : Real) * mean - value) ↔ 0 < k := by
    intro k
    constructor
    · exact And.left
    · intro hk
      exact ⟨hk, hprojected k hk⟩
  have hpeel' :
      mu {omega : Omega |
          0 < pullCount (action omega) arm n ∧
          threshold (pullCount (action omega) arm n) <=
            (pullCount (action omega) arm n : Real) * mean -
              sumRewards (action omega)
                (rewardFromArmStream action armStream omega) arm n} <=
        ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            0 < k ∧ threshold k <=
              (k : Real) * mean - armPrefixSum arm k stream}) := by
    simpa [positiveLowerDeviationPairs, hprojection_iff] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  simpa [hk'.2] using
    (measure_mul_sub_armPrefixSum_ge_le
      nu arm mean sigma2 hsubG k
        (hthreshold k hk'.2
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk'.1))))

/--
Adaptive-count upper tail for any action trace driven by a canonical latent
arm stream.  No UCB action rule is used.
-/
theorem measure_sumRewards_sub_pullCount_mul_ge_le_of_canonicalArmStream
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : ArmRewardStream K -> ActionTrace (Fin K))
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        threshold (pullCount (action stream) arm n) <=
          sumRewards (action stream)
              (rewardFromArmStream action id stream) arm n -
            (pullCount (action stream) arm n : Real) * mean} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hpeel := measure_pullCount_prod_sumRewards_rewardFromCanonicalArmStream_mem_le
    (armStreamMeasure nu) action arm n (upperDeviationPairs mean threshold)
  have hprojected : forall k : Nat,
      exists value : Real,
        threshold k <= value - (k : Real) * mean := by
    intro k
    refine ⟨threshold k + (k : Real) * mean, ?_⟩
    linarith
  have hpeel' :
      armStreamMeasure nu {stream : ArmRewardStream K |
          threshold (pullCount (action stream) arm n) <=
            sumRewards (action stream)
                (rewardFromArmStream action id stream) arm n -
              (pullCount (action stream) arm n : Real) * mean} <=
        (Finset.range (n + 1)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            threshold k <=
              armPrefixSum arm k stream - (k : Real) * mean}) := by
    simpa [upperDeviationPairs, hprojected] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  exact measure_armPrefixSum_sub_mul_ge_le
    nu arm mean sigma2 hsubG k
      (hthreshold k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/--
Adaptive-count lower tail for any action trace driven by a canonical latent
arm stream.  No UCB action rule is used.
-/
theorem measure_pullCount_mul_sub_sumRewards_ge_le_of_canonicalArmStream
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : ArmRewardStream K -> ActionTrace (Fin K))
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        threshold (pullCount (action stream) arm n) <=
          (pullCount (action stream) arm n : Real) * mean -
            sumRewards (action stream)
              (rewardFromArmStream action id stream) arm n} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hpeel := measure_pullCount_prod_sumRewards_rewardFromCanonicalArmStream_mem_le
    (armStreamMeasure nu) action arm n (lowerDeviationPairs mean threshold)
  have hprojected : forall k : Nat,
      exists value : Real,
        threshold k <= (k : Real) * mean - value := by
    intro k
    refine ⟨(k : Real) * mean - threshold k, ?_⟩
    linarith
  have hpeel' :
      armStreamMeasure nu {stream : ArmRewardStream K |
          threshold (pullCount (action stream) arm n) <=
            (pullCount (action stream) arm n : Real) * mean -
              sumRewards (action stream)
                (rewardFromArmStream action id stream) arm n} <=
        (Finset.range (n + 1)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            threshold k <=
              (k : Real) * mean - armPrefixSum arm k stream}) := by
    simpa [lowerDeviationPairs, hprojected] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  exact measure_mul_sub_armPrefixSum_ge_le
    nu arm mean sigma2 hsubG k
      (hthreshold k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

end UCB

namespace Thompson

/-- Canonical trajectory kernel after freezing the non-stream environment. -/
noncomputable def latentArmStreamTrajectoryKernel
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) :
    Kernel (UCB.ArmRewardStream K) ((n : Nat) -> Fin K × Real) :=
  (canonicalMeasurableEnvironmentTrajectoryKernel algorithm
    (latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K))).comap
      (fun stream => (env, stream)) (measurable_const.prodMk measurable_id)

instance instLatentArmStreamTrajectoryKernelIsMarkov
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) :
    IsMarkovKernel (latentArmStreamTrajectoryKernel algorithm env) := by
  unfold latentArmStreamTrajectoryKernel
  infer_instance

/-- Joint law of a stationary latent arm stream and its generated trajectory. -/
noncomputable def latentArmStreamTrajectoryMeasure
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Measure (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real)) :=
  UCB.armStreamMeasure nu ⊗ₘ latentArmStreamTrajectoryKernel algorithm env

instance instLatentArmStreamTrajectoryMeasureIsProbability
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    IsProbabilityMeasure (latentArmStreamTrajectoryMeasure algorithm env nu) := by
  unfold latentArmStreamTrajectoryMeasure
  infer_instance

/-- Action trace projected from the trajectory coordinate of the coupling. -/
def latentArmStreamTrajectoryAction
    {K : Nat} :
    (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real)) ->
      ActionTrace (Fin K) :=
  fun sample => canonicalHistoryTrajectoryAction sample.2

/-- Reward trace projected from the trajectory coordinate of the coupling. -/
def latentArmStreamTrajectoryReward
    {K : Nat} :
    (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real)) ->
      RewardTrace Real :=
  fun sample => canonicalHistoryTrajectoryReward sample.2

theorem measurable_latentArmStreamTrajectoryAction_apply
    {K : Nat} (t : Nat) :
    Measurable (fun sample :
        UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real) =>
      latentArmStreamTrajectoryAction sample t) :=
  (measurable_canonicalHistoryTrajectoryAction_apply t).comp measurable_snd

theorem measurable_latentArmStreamTrajectoryReward_apply
    {K : Nat} (t : Nat) :
    Measurable (fun sample :
        UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real) =>
      latentArmStreamTrajectoryReward sample t) :=
  (measurable_canonicalHistoryTrajectoryReward_apply t).comp measurable_snd

/-- Pull counts remain measurable when the queried arm is sample-dependent. -/
theorem measurable_pullCount_selectedArm
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t, Measurable (fun omega => action omega t))
    (arm : Omega -> Fin K) (harm : Measurable arm) (n : Nat) :
    Measurable (fun omega => pullCount (action omega) (arm omega) n) := by
  induction n with
  | zero => simp [pullCount]
  | succ n ih =>
      have hevent : MeasurableSet {omega | action omega n = arm omega} :=
        measurableSet_eq_fun (haction n) harm
      have hincrement : Measurable (fun omega =>
          if action omega n = arm omega then (1 : Nat) else 0) :=
        Measurable.ite hevent measurable_const measurable_const
      simpa [pullCount_succ] using ih.add hincrement

/-- Selected-arm reward sums are measurable for a measurable arm selector. -/
theorem measurable_sumRewards_selectedArm
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (arm : Omega -> Fin K) (harm : Measurable arm) (n : Nat) :
    Measurable (fun omega =>
      sumRewards (action omega) (reward omega) (arm omega) n) := by
  induction n with
  | zero => simp [sumRewards]
  | succ n ih =>
      have hevent : MeasurableSet {omega | action omega n = arm omega} :=
        measurableSet_eq_fun (haction n) harm
      have hincrement : Measurable (fun omega =>
          if action omega n = arm omega then reward omega n else 0) :=
        Measurable.ite hevent (hreward n) measurable_const
      simpa [sumRewards_succ] using ih.add hincrement

/-- The real empirical mean is measurable for a measurable arm selector. -/
theorem measurable_realEmpiricalMean_selectedArm
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (arm : Omega -> Fin K) (harm : Measurable arm) (n : Nat) :
    Measurable (fun omega =>
      UCB.realEmpiricalMean (action omega) (reward omega) (arm omega) n) := by
  exact
    (measurable_sumRewards_selectedArm action reward haction hreward arm harm n).div
      ((measurable_of_countable fun k : Nat => (k : Real)).comp
        (measurable_pullCount_selectedArm action haction arm harm n))

/-- The stream coordinate of the coupling has exactly the canonical stream law. -/
theorem identDistrib_fst_latentArmStreamTrajectoryMeasure
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    IdentDistrib Prod.fst id
      (latentArmStreamTrajectoryMeasure algorithm env nu)
      (UCB.armStreamMeasure nu) where
  aemeasurable_fst := measurable_fst.aemeasurable
  aemeasurable_snd := measurable_id.aemeasurable
  map_eq := by
    change (latentArmStreamTrajectoryMeasure algorithm env nu).fst =
      Measure.map id (UCB.armStreamMeasure nu)
    rw [latentArmStreamTrajectoryMeasure, Measure.fst_compProd,
      Measure.map_id]

/-- The joint coupling reads its actual rewards from its own latent stream. -/
theorem latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    latentArmStreamTrajectoryReward =ᵐ[
        latentArmStreamTrajectoryMeasure algorithm env nu]
      UCB.rewardFromArmStream latentArmStreamTrajectoryAction Prod.fst := by
  have hcoord : ∀ t, ∀ᵐ sample ∂
      latentArmStreamTrajectoryMeasure algorithm env nu,
      latentArmStreamTrajectoryReward sample t =
        UCB.rewardFromArmStream latentArmStreamTrajectoryAction Prod.fst
          sample t := by
    intro t
    have hp : MeasurableSet
        {sample : UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real) |
          latentArmStreamTrajectoryReward sample t =
            UCB.rewardFromArmStream latentArmStreamTrajectoryAction Prod.fst
              sample t} :=
      measurableSet_eq_fun
        (measurable_latentArmStreamTrajectoryReward_apply t)
        (UCB.measurable_rewardFromArmStream_apply
          latentArmStreamTrajectoryAction
          measurable_latentArmStreamTrajectoryAction_apply Prod.fst
          (fun i arm =>
            (measurable_pi_apply arm).comp
              ((measurable_pi_apply i).comp measurable_fst)) t)
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with stream
    rw [latentArmStreamTrajectoryKernel, Kernel.comap_apply]
    have hfixed :=
      canonicalLatentArmStreamTrajectory_reward_eq_rewardFromArmStream_ae
        algorithm env stream
    filter_upwards [hfixed] with trajectory htrajectory
    exact congrFun htrajectory t
  filter_upwards [ae_all_iff.2 hcoord] with sample hsample
  funext t
  exact hsample t

/-- Upper adaptive-count tail for rewards on the coupled Thompson trajectory. -/
theorem measure_latentArmStreamTrajectory_sumRewards_sub_pullCount_mul_ge_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    latentArmStreamTrajectoryMeasure algorithm env nu
        {sample |
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n -
              (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  let mu := latentArmStreamTrajectoryMeasure algorithm env nu
  have htail :=
    UCB.measure_sumRewards_sub_pullCount_mul_ge_le_of_armStream_identDistrib
      mu nu latentArmStreamTrajectoryAction Prod.fst
      (fun i arm =>
        (measurable_pi_apply arm).comp
          ((measurable_pi_apply i).comp measurable_fst))
      (identDistrib_fst_latentArmStreamTrajectoryMeasure algorithm env nu)
      arm mean sigma2 hsubG n threshold hthreshold
  calc
    _ = mu {sample |
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards (latentArmStreamTrajectoryAction sample)
                (UCB.rewardFromArmStream latentArmStreamTrajectoryAction
                  Prod.fst sample) arm n -
              (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean} := by
        apply measure_congr
        filter_upwards
          [latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
            algorithm env nu] with sample hreward
        apply propext
        change
          (threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n -
              (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean) ↔
          (threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards (latentArmStreamTrajectoryAction sample)
                (UCB.rewardFromArmStream latentArmStreamTrajectoryAction
                  Prod.fst sample) arm n -
              (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean)
        rw [hreward]
    _ <= _ := htail

/-- Lower adaptive-count tail for rewards on the coupled Thompson trajectory. -/
theorem measure_latentArmStreamTrajectory_pullCount_mul_sub_sumRewards_ge_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    latentArmStreamTrajectoryMeasure algorithm env nu
        {sample |
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean -
              sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  let mu := latentArmStreamTrajectoryMeasure algorithm env nu
  have htail :=
    UCB.measure_pullCount_mul_sub_sumRewards_ge_le_of_armStream_identDistrib
      mu nu latentArmStreamTrajectoryAction Prod.fst
      (fun i arm =>
        (measurable_pi_apply arm).comp
          ((measurable_pi_apply i).comp measurable_fst))
      (identDistrib_fst_latentArmStreamTrajectoryMeasure algorithm env nu)
      arm mean sigma2 hsubG n threshold hthreshold
  calc
    _ = mu {sample |
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean -
              sumRewards (latentArmStreamTrajectoryAction sample)
                (UCB.rewardFromArmStream latentArmStreamTrajectoryAction
                  Prod.fst sample) arm n} := by
        apply measure_congr
        filter_upwards
          [latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
            algorithm env nu] with sample hreward
        apply propext
        change
          (threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean -
              sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n) ↔
          (threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean -
              sumRewards (latentArmStreamTrajectoryAction sample)
                (UCB.rewardFromArmStream latentArmStreamTrajectoryAction
                  Prod.fst sample) arm n)
        rw [hreward]
    _ <= _ := htail

/-- Positive-count upper tail for rewards on the coupled trajectory. -/
theorem measure_latentArmStreamTrajectory_pos_and_sumRewards_sub_pullCount_mul_ge_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    latentArmStreamTrajectoryMeasure algorithm env nu
        {sample |
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n -
              (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  let mu := latentArmStreamTrajectoryMeasure algorithm env nu
  have htail :=
    UCB.measure_pos_and_sumRewards_sub_pullCount_mul_ge_le_of_armStream_identDistrib
      mu nu latentArmStreamTrajectoryAction Prod.fst
      (fun i arm =>
        (measurable_pi_apply arm).comp
          ((measurable_pi_apply i).comp measurable_fst))
      (identDistrib_fst_latentArmStreamTrajectoryMeasure algorithm env nu)
      arm mean sigma2 hsubG n threshold hthreshold
  calc
    _ = mu {sample |
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards (latentArmStreamTrajectoryAction sample)
                (UCB.rewardFromArmStream latentArmStreamTrajectoryAction
                  Prod.fst sample) arm n -
              (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean} := by
        apply measure_congr
        filter_upwards
          [latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
            algorithm env nu] with sample hreward
        apply propext
        change
          (0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
            threshold (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
              sumRewards (latentArmStreamTrajectoryAction sample)
                  (latentArmStreamTrajectoryReward sample) arm n -
                (pullCount (latentArmStreamTrajectoryAction sample) arm n : Real) *
                  mean) ↔
          (0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
            threshold (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
              sumRewards (latentArmStreamTrajectoryAction sample)
                  (UCB.rewardFromArmStream latentArmStreamTrajectoryAction
                    Prod.fst sample) arm n -
                (pullCount (latentArmStreamTrajectoryAction sample) arm n : Real) *
                  mean)
        rw [hreward]
    _ <= _ := htail

/-- Positive-count lower tail for rewards on the coupled trajectory. -/
theorem measure_latentArmStreamTrajectory_pos_and_pullCount_mul_sub_sumRewards_ge_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    latentArmStreamTrajectoryMeasure algorithm env nu
        {sample |
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean -
              sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  let mu := latentArmStreamTrajectoryMeasure algorithm env nu
  have htail :=
    UCB.measure_pos_and_pullCount_mul_sub_sumRewards_ge_le_of_armStream_identDistrib
      mu nu latentArmStreamTrajectoryAction Prod.fst
      (fun i arm =>
        (measurable_pi_apply arm).comp
          ((measurable_pi_apply i).comp measurable_fst))
      (identDistrib_fst_latentArmStreamTrajectoryMeasure algorithm env nu)
      arm mean sigma2 hsubG n threshold hthreshold
  calc
    _ = mu {sample |
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) * mean -
              sumRewards (latentArmStreamTrajectoryAction sample)
                (UCB.rewardFromArmStream latentArmStreamTrajectoryAction
                  Prod.fst sample) arm n} := by
        apply measure_congr
        filter_upwards
          [latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
            algorithm env nu] with sample hreward
        apply propext
        change
          (0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
            threshold (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
              (pullCount (latentArmStreamTrajectoryAction sample) arm n : Real) *
                  mean -
                sumRewards (latentArmStreamTrajectoryAction sample)
                  (latentArmStreamTrajectoryReward sample) arm n) ↔
          (0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
            threshold (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
              (pullCount (latentArmStreamTrajectoryAction sample) arm n : Real) *
                  mean -
                sumRewards (latentArmStreamTrajectoryAction sample)
                  (UCB.rewardFromArmStream latentArmStreamTrajectoryAction
                    Prod.fst sample) arm n)
        rw [hreward]
    _ <= _ := htail

/--
Environment-indexed kernel that samples the stationary latent stream and then
runs the actual history algorithm against next-unused deterministic feedback.
-/
noncomputable def stationaryLatentArmStreamTrajectoryKernel
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real) :
    Kernel Env
      (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real)) :=
  stationaryArmStreamKernel rewardKernel ⊗ₖ
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm
      (latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K))

instance instStationaryLatentArmStreamTrajectoryKernelIsMarkov
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real) :
    IsMarkovKernel
      (stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm) := by
  unfold stationaryLatentArmStreamTrajectoryKernel
  infer_instance

/-- Its conditional law is exactly the fixed-environment coupling above. -/
theorem stationaryLatentArmStreamTrajectoryKernel_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) :
    stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm env =
      latentArmStreamTrajectoryMeasure algorithm env
        (stationaryRewardKernelAt rewardKernel env) := by
  rw [stationaryLatentArmStreamTrajectoryKernel,
    Kernel.compProd_apply_eq_compProd_sectR,
    stationaryArmStreamKernel_apply]
  unfold latentArmStreamTrajectoryMeasure
  congr 1

/-- Pointwise upper tail for the actual augmented Thompson trajectory kernel. -/
theorem stationaryLatentArmStreamTrajectoryKernel_sumRewards_upper_tail
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real) (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (env : Env) (arm : Fin K) (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm env
        {sample |
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n -
              (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) *
                mean env arm} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  rw [stationaryLatentArmStreamTrajectoryKernel_apply]
  apply measure_latentArmStreamTrajectory_sumRewards_sub_pullCount_mul_ge_le
  simpa using hsubG env arm
  exact hthreshold

/-- Pointwise lower tail for the actual augmented Thompson trajectory kernel. -/
theorem stationaryLatentArmStreamTrajectoryKernel_sumRewards_lower_tail
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real) (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (env : Env) (arm : Fin K) (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm env
        {sample |
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) *
                mean env arm -
              sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  rw [stationaryLatentArmStreamTrajectoryKernel_apply]
  apply measure_latentArmStreamTrajectory_pullCount_mul_sub_sumRewards_ge_le
  simpa using hsubG env arm
  exact hthreshold

/-- Positive-count upper tail for the environment-indexed augmented kernel. -/
theorem stationaryLatentArmStreamTrajectoryKernel_pos_and_sumRewards_upper_tail
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real) (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (env : Env) (arm : Fin K) (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm env
        {sample |
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n -
              (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) *
                mean env arm} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  rw [stationaryLatentArmStreamTrajectoryKernel_apply]
  apply measure_latentArmStreamTrajectory_pos_and_sumRewards_sub_pullCount_mul_ge_le
  simpa using hsubG env arm
  exact hthreshold

/-- Positive-count lower tail for the environment-indexed augmented kernel. -/
theorem stationaryLatentArmStreamTrajectoryKernel_pos_and_sumRewards_lower_tail
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real) (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (env : Env) (arm : Fin K) (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm env
        {sample |
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm n ∧
          threshold
              (pullCount (latentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (latentArmStreamTrajectoryAction sample) arm n : Real) *
                mean env arm -
              sumRewards (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm n} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  rw [stationaryLatentArmStreamTrajectoryKernel_apply]
  apply measure_latentArmStreamTrajectory_pos_and_pullCount_mul_sub_sumRewards_ge_le
  simpa using hsubG env arm
  exact hthreshold

/-- Environment coordinate of the stationary augmented trajectory sample. -/
def stationaryLatentArmStreamTrajectoryEnvironment
    {Env : Type u} {K : Nat} :
    (Env × (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real))) -> Env :=
  Prod.fst

/-- Action trace of the stationary augmented trajectory sample. -/
def stationaryLatentArmStreamTrajectoryAction
    {Env : Type u} {K : Nat} :
    (Env × (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real))) ->
      ActionTrace (Fin K) :=
  fun sample => latentArmStreamTrajectoryAction sample.2

/-- Reward trace of the stationary augmented trajectory sample. -/
def stationaryLatentArmStreamTrajectoryReward
    {Env : Type u} {K : Nat} :
    (Env × (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real))) ->
      RewardTrace Real :=
  fun sample => latentArmStreamTrajectoryReward sample.2

theorem measurable_stationaryLatentArmStreamTrajectoryEnvironment
    {Env : Type u} {K : Nat} [MeasurableSpace Env] :
    Measurable
      (stationaryLatentArmStreamTrajectoryEnvironment (Env := Env) (K := K)) :=
  measurable_fst

theorem measurable_stationaryLatentArmStreamTrajectoryAction_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env] (t : Nat) :
    Measurable (fun sample :
        Env × (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real)) =>
      stationaryLatentArmStreamTrajectoryAction sample t) :=
  (measurable_latentArmStreamTrajectoryAction_apply t).comp measurable_snd

theorem measurable_stationaryLatentArmStreamTrajectoryReward_apply
    {Env : Type u} {K : Nat} [MeasurableSpace Env] (t : Nat) :
    Measurable (fun sample :
        Env × (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real)) =>
      stationaryLatentArmStreamTrajectoryReward sample t) :=
  (measurable_latentArmStreamTrajectoryReward_apply t).comp measurable_snd

/-- Prior mixture of the stationary latent stream and its actual trajectory. -/
noncomputable def stationaryLatentArmStreamTrajectoryMeasure
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (prior : Measure Env) (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real) :
    Measure
      (Env × (UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real))) :=
  prior ⊗ₘ stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm

instance instStationaryLatentArmStreamTrajectoryMeasureIsProbability
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real) :
    IsProbabilityMeasure
      (stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm) := by
  unfold stationaryLatentArmStreamTrajectoryMeasure
  infer_instance

/--
Upper fixed-arm adaptive-count tail after mixing the fixed-environment
augmented trajectory through the environment prior.
-/
theorem stationaryLatentArmStreamTrajectoryMeasure_sumRewards_upper_tail
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (arm : Fin K) (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          threshold
              (pullCount
                (stationaryLatentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm n -
              (pullCount
                (stationaryLatentArmStreamTrajectoryAction sample) arm n :
                  Real) * mean
                    (stationaryLatentArmStreamTrajectoryEnvironment sample) arm} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  let action := stationaryLatentArmStreamTrajectoryAction
    (Env := Env) (K := K)
  let reward := stationaryLatentArmStreamTrajectoryReward
    (Env := Env) (K := K)
  let environment := stationaryLatentArmStreamTrajectoryEnvironment
    (Env := Env) (K := K)
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryReward_apply
  have hpull : Measurable (fun sample => pullCount (action sample) arm n) :=
    measurable_pullCount action haction arm n
  have hsum : Measurable (fun sample =>
      sumRewards (action sample) (reward sample) arm n) :=
    measurable_sumRewards action reward haction hreward arm n
  have hmean : Measurable (fun sample => mean (environment sample) arm) :=
    hmeas_mean.comp
      (measurable_stationaryLatentArmStreamTrajectoryEnvironment.prodMk
        measurable_const)
  have hs : MeasurableSet {sample |
      threshold (pullCount (action sample) arm n) <=
        sumRewards (action sample) (reward sample) arm n -
          (pullCount (action sample) arm n : Real) *
            mean (environment sample) arm} :=
    measurableSet_le
      ((measurable_of_countable threshold).comp hpull)
      (hsum.sub
        (((measurable_of_countable fun k : Nat => (k : Real)).comp hpull).mul
          hmean))
  rw [stationaryLatentArmStreamTrajectoryMeasure,
    Measure.compProd_apply hs]
  calc
    (∫⁻ env, stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm env
        (Prod.mk env ⁻¹' {sample |
          threshold (pullCount (action sample) arm n) <=
            sumRewards (action sample) (reward sample) arm n -
              (pullCount (action sample) arm n : Real) *
                mean (environment sample) arm}) ∂prior) <=
        ∫⁻ _ : Env, (Finset.range (n + 1)).sum (fun k =>
          ENNReal.ofReal
            (Real.exp
              (-(threshold k) ^ 2 /
                (2 * (k : Real) * (sigma2 : Real))))) ∂prior := by
      apply lintegral_mono
      intro env
      simpa [action, reward, environment,
        stationaryLatentArmStreamTrajectoryAction,
        stationaryLatentArmStreamTrajectoryReward,
        stationaryLatentArmStreamTrajectoryEnvironment] using
        stationaryLatentArmStreamTrajectoryKernel_sumRewards_upper_tail
          rewardKernel algorithm mean sigma2 hsubG env arm n threshold hthreshold
    _ = (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by simp

/-- Lower-tail counterpart of the augmented-prior mixture theorem. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_sumRewards_lower_tail
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (arm : Fin K) (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          threshold
              (pullCount
                (stationaryLatentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (stationaryLatentArmStreamTrajectoryAction sample) arm n :
                  Real) * mean
                    (stationaryLatentArmStreamTrajectoryEnvironment sample) arm -
              sumRewards
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm n} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  let action := stationaryLatentArmStreamTrajectoryAction
    (Env := Env) (K := K)
  let reward := stationaryLatentArmStreamTrajectoryReward
    (Env := Env) (K := K)
  let environment := stationaryLatentArmStreamTrajectoryEnvironment
    (Env := Env) (K := K)
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryReward_apply
  have hpull : Measurable (fun sample => pullCount (action sample) arm n) :=
    measurable_pullCount action haction arm n
  have hsum : Measurable (fun sample =>
      sumRewards (action sample) (reward sample) arm n) :=
    measurable_sumRewards action reward haction hreward arm n
  have hmean : Measurable (fun sample => mean (environment sample) arm) :=
    hmeas_mean.comp
      (measurable_stationaryLatentArmStreamTrajectoryEnvironment.prodMk
        measurable_const)
  have hs : MeasurableSet {sample |
      threshold (pullCount (action sample) arm n) <=
        (pullCount (action sample) arm n : Real) *
            mean (environment sample) arm -
          sumRewards (action sample) (reward sample) arm n} :=
    measurableSet_le
      ((measurable_of_countable threshold).comp hpull)
      ((((measurable_of_countable fun k : Nat => (k : Real)).comp hpull).mul
          hmean).sub hsum)
  rw [stationaryLatentArmStreamTrajectoryMeasure,
    Measure.compProd_apply hs]
  calc
    (∫⁻ env, stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm env
        (Prod.mk env ⁻¹' {sample |
          threshold (pullCount (action sample) arm n) <=
            (pullCount (action sample) arm n : Real) *
                mean (environment sample) arm -
              sumRewards (action sample) (reward sample) arm n}) ∂prior) <=
        ∫⁻ _ : Env, (Finset.range (n + 1)).sum (fun k =>
          ENNReal.ofReal
            (Real.exp
              (-(threshold k) ^ 2 /
                (2 * (k : Real) * (sigma2 : Real))))) ∂prior := by
      apply lintegral_mono
      intro env
      simpa [action, reward, environment,
        stationaryLatentArmStreamTrajectoryAction,
        stationaryLatentArmStreamTrajectoryReward,
        stationaryLatentArmStreamTrajectoryEnvironment] using
        stationaryLatentArmStreamTrajectoryKernel_sumRewards_lower_tail
          rewardKernel algorithm mean sigma2 hsubG env arm n threshold hthreshold
    _ = (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by simp

/-- Integrate a uniform pointwise kernel event bound through a probability prior. -/
theorem measure_compProd_le_of_forall_kernel_apply_le
    {Env : Type u} {Omega : Type v}
    [MeasurableSpace Env] [MeasurableSpace Omega]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (kernel : Kernel Env Omega) [IsMarkovKernel kernel]
    (event : Set (Env × Omega)) (hevent : MeasurableSet event)
    (bound : ENNReal)
    (hbound : forall env, kernel env (Prod.mk env ⁻¹' event) <= bound) :
    (prior ⊗ₘ kernel) event <= bound := by
  rw [Measure.compProd_apply hevent]
  calc
    (∫⁻ env, kernel env (Prod.mk env ⁻¹' event) ∂prior) <=
        ∫⁻ _ : Env, bound ∂prior := lintegral_mono hbound
    _ = bound := by simp

/-- Positive-count upper tail after mixing through the environment prior. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_pos_and_sumRewards_upper_tail
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (arm : Fin K) (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          0 < pullCount
              (stationaryLatentArmStreamTrajectoryAction sample) arm n ∧
          threshold
              (pullCount
                (stationaryLatentArmStreamTrajectoryAction sample) arm n) <=
            sumRewards
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm n -
              (pullCount
                (stationaryLatentArmStreamTrajectoryAction sample) arm n :
                  Real) * mean
                    (stationaryLatentArmStreamTrajectoryEnvironment sample) arm} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  let action := stationaryLatentArmStreamTrajectoryAction
    (Env := Env) (K := K)
  let reward := stationaryLatentArmStreamTrajectoryReward
    (Env := Env) (K := K)
  let environment := stationaryLatentArmStreamTrajectoryEnvironment
    (Env := Env) (K := K)
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryReward_apply
  have hpull : Measurable (fun sample => pullCount (action sample) arm n) :=
    measurable_pullCount action haction arm n
  have hsum : Measurable (fun sample =>
      sumRewards (action sample) (reward sample) arm n) :=
    measurable_sumRewards action reward haction hreward arm n
  have hmean : Measurable (fun sample => mean (environment sample) arm) :=
    hmeas_mean.comp
      (measurable_stationaryLatentArmStreamTrajectoryEnvironment.prodMk
        measurable_const)
  have hs : MeasurableSet {sample |
      0 < pullCount (action sample) arm n ∧
      threshold (pullCount (action sample) arm n) <=
        sumRewards (action sample) (reward sample) arm n -
          (pullCount (action sample) arm n : Real) *
            mean (environment sample) arm} :=
    (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le
        ((measurable_of_countable threshold).comp hpull)
        (hsum.sub
          (((measurable_of_countable fun k : Nat => (k : Real)).comp hpull).mul
            hmean)))
  unfold stationaryLatentArmStreamTrajectoryMeasure
  apply measure_compProd_le_of_forall_kernel_apply_le prior
    (stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm) _ hs
  intro env
  simpa [action, reward, environment,
    stationaryLatentArmStreamTrajectoryAction,
    stationaryLatentArmStreamTrajectoryReward,
    stationaryLatentArmStreamTrajectoryEnvironment] using
    stationaryLatentArmStreamTrajectoryKernel_pos_and_sumRewards_upper_tail
      rewardKernel algorithm mean sigma2 hsubG env arm n threshold hthreshold

/-- Positive-count lower tail after mixing through the environment prior. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_pos_and_sumRewards_lower_tail
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (arm : Fin K) (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          0 < pullCount
              (stationaryLatentArmStreamTrajectoryAction sample) arm n ∧
          threshold
              (pullCount
                (stationaryLatentArmStreamTrajectoryAction sample) arm n) <=
            (pullCount
                (stationaryLatentArmStreamTrajectoryAction sample) arm n :
                  Real) * mean
                    (stationaryLatentArmStreamTrajectoryEnvironment sample) arm -
              sumRewards
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm n} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  let action := stationaryLatentArmStreamTrajectoryAction
    (Env := Env) (K := K)
  let reward := stationaryLatentArmStreamTrajectoryReward
    (Env := Env) (K := K)
  let environment := stationaryLatentArmStreamTrajectoryEnvironment
    (Env := Env) (K := K)
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryReward_apply
  have hpull : Measurable (fun sample => pullCount (action sample) arm n) :=
    measurable_pullCount action haction arm n
  have hsum : Measurable (fun sample =>
      sumRewards (action sample) (reward sample) arm n) :=
    measurable_sumRewards action reward haction hreward arm n
  have hmean : Measurable (fun sample => mean (environment sample) arm) :=
    hmeas_mean.comp
      (measurable_stationaryLatentArmStreamTrajectoryEnvironment.prodMk
        measurable_const)
  have hs : MeasurableSet {sample |
      0 < pullCount (action sample) arm n ∧
      threshold (pullCount (action sample) arm n) <=
        (pullCount (action sample) arm n : Real) *
            mean (environment sample) arm -
          sumRewards (action sample) (reward sample) arm n} :=
    (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le
        ((measurable_of_countable threshold).comp hpull)
        ((((measurable_of_countable fun k : Nat => (k : Real)).comp hpull).mul
            hmean).sub hsum))
  unfold stationaryLatentArmStreamTrajectoryMeasure
  apply measure_compProd_le_of_forall_kernel_apply_le prior
    (stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm) _ hs
  intro env
  simpa [action, reward, environment,
    stationaryLatentArmStreamTrajectoryAction,
    stationaryLatentArmStreamTrajectoryReward,
    stationaryLatentArmStreamTrajectoryEnvironment] using
    stationaryLatentArmStreamTrajectoryKernel_pos_and_sumRewards_lower_tail
      rewardKernel algorithm mean sigma2 hsubG env arm n threshold hthreshold

/-- Pull-count-scaled radius used by the clipped Thompson score. -/
noncomputable def clippedCountWidthThreshold
    (sigma2 : NNReal) (delta : Real) (k : Nat) : Real :=
  (k : Real) *
    Real.sqrt
      (2 * (sigma2 : Real) * Real.log (1 / delta) / (k : Real))

theorem clippedCountWidthThreshold_nonneg
    (sigma2 : NNReal) (delta : Real) (k : Nat) :
    0 <= clippedCountWidthThreshold sigma2 delta k := by
  exact mul_nonneg (Nat.cast_nonneg k) (Real.sqrt_nonneg _)

/-- The clipped-score count threshold has the intended confidence exponent. -/
theorem clippedCountWidthThreshold_sq_div_eq
    (sigma2 : NNReal) (delta : Real) (k : Nat)
    (hsigma2 : sigma2 ≠ 0) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hk : 0 < k) :
    (clippedCountWidthThreshold sigma2 delta k) ^ 2 /
        (2 * (k : Real) * (sigma2 : Real)) =
      Real.log (1 / delta) := by
  have hk_real : 0 < (k : Real) := by exact_mod_cast hk
  have hk_ne : (k : Real) ≠ 0 := ne_of_gt hk_real
  have hsigma_pos : 0 < (sigma2 : Real) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hsigma2)
  have hsigma_ne : (sigma2 : Real) ≠ 0 := ne_of_gt hsigma_pos
  have hinv_one : 1 <= 1 / delta := by
    exact (le_div_iff₀ hdelta).2 (by simpa using hdelta_one)
  have hlog : 0 <= Real.log (1 / delta) := Real.log_nonneg hinv_one
  have hsqrt : 0 <=
      2 * (sigma2 : Real) * Real.log (1 / delta) / (k : Real) := by
    positivity
  unfold clippedCountWidthThreshold
  rw [mul_pow, Real.sq_sqrt hsqrt]
  field_simp [hk_ne, hsigma_ne]

/-- The positive-count clipped-radius exponential sum is exactly `n * delta`. -/
theorem sum_clippedCountWidthThreshold_tail_eq
    (sigma2 : NNReal) (delta : Real) (n : Nat)
    (hsigma2 : sigma2 ≠ 0) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(clippedCountWidthThreshold sigma2 delta k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) =
      (n : ENNReal) * ENNReal.ofReal delta := by
  rw [UCB.positiveCountFilter_eq_Icc]
  have hterm : forall k, k ∈ Finset.Icc 1 n ->
      ENNReal.ofReal
          (Real.exp
            (-(clippedCountWidthThreshold sigma2 delta k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real)))) =
        ENNReal.ofReal delta := by
    intro k hk
    rw [neg_div,
      clippedCountWidthThreshold_sq_div_eq sigma2 delta k hsigma2 hdelta
        hdelta_one (Finset.mem_Icc.mp hk).1]
    ring_nf
    rw [UCB.exp_neg_log_eq_inv]
    · simp
    · exact inv_pos.mpr hdelta
  rw [Finset.sum_congr rfl hterm]
  simp [nsmul_eq_mul]

/-- A finite union of lower prefix deviations pays once per positive pull count. -/
theorem measure_biUnion_clippedCountWidthThreshold_le_mul_sub_armPrefixSum_le
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (m : Nat) :
    UCB.armStreamMeasure nu
        (⋃ k ∈ Finset.Icc 1 m,
          {stream : UCB.ArmRewardStream K |
            clippedCountWidthThreshold sigma2 delta k <=
              (k : Real) * mean - UCB.armPrefixSum arm k stream}) <=
      (m : ENNReal) * ENNReal.ofReal delta := by
  classical
  calc
    _ <= (Finset.Icc 1 m).sum (fun k =>
        UCB.armStreamMeasure nu
          {stream : UCB.ArmRewardStream K |
            clippedCountWidthThreshold sigma2 delta k <=
              (k : Real) * mean - UCB.armPrefixSum arm k stream}) :=
      ProbabilityUnionBound.measure_biUnion_finset_le
        (UCB.armStreamMeasure nu) (Finset.Icc 1 m) _
    _ <= (Finset.Icc 1 m).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(clippedCountWidthThreshold sigma2 delta k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact UCB.measure_mul_sub_armPrefixSum_ge_le
        nu arm mean sigma2 hsubG k
          (clippedCountWidthThreshold_nonneg sigma2 delta k)
    _ = _ := by
      simpa [UCB.positiveCountFilter_eq_Icc] using
        sum_clippedCountWidthThreshold_tail_eq
          sigma2 delta m hsigma2 hdelta hdelta_one

/-- A clipped-score lower-confidence failure implies a lower sum deviation. -/
theorem clippedCountWidthThreshold_le_mul_mean_sub_sumRewards
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (arm : Fin K) (n : Nat) (mean : Real) (sigma2 : NNReal) (delta : Real)
    (hcount : 0 < pullCount action arm n)
    (hindex :
      UCB.realEmpiricalMean action reward arm n +
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount action arm n : Real)) <= mean) :
    clippedCountWidthThreshold sigma2 delta (pullCount action arm n) <=
      (pullCount action arm n : Real) * mean -
        sumRewards action reward arm n := by
  let k := pullCount action arm n
  let total := sumRewards action reward arm n
  have hk : 0 < (k : Real) := by exact_mod_cast hcount
  have hk_ne : (k : Real) ≠ 0 := ne_of_gt hk
  have hdiv : total / (k : Real) * (k : Real) = total :=
    div_mul_cancel₀ total hk_ne
  change total / (k : Real) +
      Real.sqrt
        (2 * (sigma2 : Real) * Real.log (1 / delta) / (k : Real)) <=
    mean at hindex
  change (k : Real) *
      Real.sqrt
        (2 * (sigma2 : Real) * Real.log (1 / delta) / (k : Real)) <=
    (k : Real) * mean - total
  nlinarith

/-- A clipped-score upper-confidence failure implies an upper sum deviation. -/
theorem clippedCountWidthThreshold_le_sumRewards_sub_mul_mean
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (arm : Fin K) (n : Nat) (mean : Real) (sigma2 : NNReal) (delta : Real)
    (hcount : 0 < pullCount action arm n)
    (hindex : mean <=
      UCB.realEmpiricalMean action reward arm n -
        Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) /
            (pullCount action arm n : Real))) :
    clippedCountWidthThreshold sigma2 delta (pullCount action arm n) <=
      sumRewards action reward arm n -
        (pullCount action arm n : Real) * mean := by
  let k := pullCount action arm n
  let total := sumRewards action reward arm n
  have hk : 0 < (k : Real) := by exact_mod_cast hcount
  have hk_ne : (k : Real) ≠ 0 := ne_of_gt hk
  have hdiv : total / (k : Real) * (k : Real) = total :=
    div_mul_cancel₀ total hk_ne
  change mean <= total / (k : Real) -
      Real.sqrt
        (2 * (sigma2 : Real) * Real.log (1 / delta) / (k : Real)) at hindex
  change (k : Real) *
      Real.sqrt
        (2 * (sigma2 : Real) * Real.log (1 / delta) / (k : Real)) <=
    total - (k : Real) * mean
  nlinarith

/--
Finite-horizon lower-confidence failure for one arm on the coupled trajectory.

All times with the same realized pull count reduce to the same latent-stream
prefix event, so the bound pays for `1, ..., n - 1` once rather than unioning
the fixed-time bounds.
-/
theorem measure_latentArmStreamTrajectory_exists_realEmpiricalMean_add_width_le_mean_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    latentArmStreamTrajectoryMeasure algorithm env nu
        {sample | ∃ t < n,
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm t ∧
          UCB.realEmpiricalMean
                (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm t +
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (latentArmStreamTrajectoryAction sample) arm t : Real)) <=
            mean} <=
      (n - 1 : Nat) * ENNReal.ofReal delta := by
  classical
  let mu := latentArmStreamTrajectoryMeasure algorithm env nu
  let action := latentArmStreamTrajectoryAction (K := K)
  let rewardFromStream :=
    UCB.rewardFromArmStream action
      (Prod.fst : UCB.ArmRewardStream K ×
        ((n : Nat) -> Fin K × Real) -> UCB.ArmRewardStream K)
  let counts := Finset.Icc 1 (n - 1)
  let fixedEvent := fun k : Nat =>
    {stream : UCB.ArmRewardStream K |
      clippedCountWidthThreshold sigma2 delta k <=
        (k : Real) * mean - UCB.armPrefixSum arm k stream}
  have hfixedEvent : forall k, MeasurableSet (fixedEvent k) := by
    intro k
    exact measurableSet_le measurable_const
      (measurable_const.sub (UCB.measurable_armPrefixSum arm k))
  have hstreamEvent : MeasurableSet (⋃ k ∈ counts, fixedEvent k) :=
    counts.measurableSet_biUnion fun k _hk => hfixedEvent k
  calc
    _ = mu {sample | ∃ t < n,
          0 < pullCount (action sample) arm t ∧
          UCB.realEmpiricalMean (action sample) (rewardFromStream sample) arm t +
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount (action sample) arm t : Real)) <= mean} := by
      apply measure_congr
      filter_upwards
        [latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
          algorithm env nu] with sample hreward
      apply propext
      constructor
      · rintro ⟨t, ht, hcount, hindex⟩
        refine ⟨t, ht, hcount, ?_⟩
        simpa [rewardFromStream, action, hreward] using hindex
      · rintro ⟨t, ht, hcount, hindex⟩
        refine ⟨t, ht, hcount, ?_⟩
        simpa [rewardFromStream, action, hreward] using hindex
    _ <= mu (Prod.fst ⁻¹' (⋃ k ∈ counts, fixedEvent k)) := by
      apply measure_mono
      rintro sample ⟨t, ht, hcount, hindex⟩
      let k := pullCount (action sample) arm t
      have hk_le_t : k <= t := pullCount_le_time (action sample) arm t
      have hk_le : k <= n - 1 := by omega
      have hk_counts : k ∈ counts :=
        Finset.mem_Icc.mpr ⟨hcount, hk_le⟩
      have hthreshold :
          clippedCountWidthThreshold sigma2 delta k <=
            (k : Real) * mean -
              sumRewards (action sample) (rewardFromStream sample) arm t :=
        clippedCountWidthThreshold_le_mul_mean_sub_sumRewards
          (action sample) (rewardFromStream sample) arm t mean sigma2 delta
            hcount hindex
      have hprefix :
          clippedCountWidthThreshold sigma2 delta k <=
            (k : Real) * mean - UCB.armPrefixSum arm k sample.1 := by
        simpa [k, rewardFromStream,
          UCB.sumRewards_rewardFromArmStream_eq_armPrefixSum] using hthreshold
      simp only [Set.mem_preimage, Set.mem_iUnion]
      exact ⟨k, ⟨hk_counts, hprefix⟩⟩
    _ = UCB.armStreamMeasure nu (⋃ k ∈ counts, fixedEvent k) := by
      calc
        mu (Prod.fst ⁻¹' (⋃ k ∈ counts, fixedEvent k)) =
            Measure.map Prod.fst mu (⋃ k ∈ counts, fixedEvent k) :=
          (Measure.map_apply measurable_fst hstreamEvent).symm
        _ = Measure.map id (UCB.armStreamMeasure nu)
              (⋃ k ∈ counts, fixedEvent k) := by
          rw [(identDistrib_fst_latentArmStreamTrajectoryMeasure
            algorithm env nu).map_eq]
        _ = UCB.armStreamMeasure nu (⋃ k ∈ counts, fixedEvent k) := by
          rw [Measure.map_id]
    _ <= _ := by
      simpa [counts, fixedEvent] using
        measure_biUnion_clippedCountWidthThreshold_le_mul_sub_armPrefixSum_le
          nu arm mean sigma2 hsubG hsigma2 delta hdelta hdelta_one (n - 1)

/--
Prior-mixed finite-horizon lower-confidence failure for an
environment-dependent measurable arm selector.
-/
theorem stationaryLatentArmStreamTrajectoryMeasure_exists_selectedArm_realEmpiricalMean_add_width_le_mean_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (selectedArm : Env -> Fin K) (hselectedArm : Measurable selectedArm)
    (n : Nat) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample | ∃ t < n,
          0 < pullCount
              (stationaryLatentArmStreamTrajectoryAction sample)
              (selectedArm
                (stationaryLatentArmStreamTrajectoryEnvironment sample)) t ∧
          UCB.realEmpiricalMean
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample)
                (selectedArm
                  (stationaryLatentArmStreamTrajectoryEnvironment sample)) t +
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (stationaryLatentArmStreamTrajectoryAction sample)
                    (selectedArm
                      (stationaryLatentArmStreamTrajectoryEnvironment sample)) t :
                      Real)) <=
            mean (stationaryLatentArmStreamTrajectoryEnvironment sample)
              (selectedArm
                (stationaryLatentArmStreamTrajectoryEnvironment sample))} <=
      (n - 1 : Nat) * ENNReal.ofReal delta := by
  classical
  let action := stationaryLatentArmStreamTrajectoryAction
    (Env := Env) (K := K)
  let reward := stationaryLatentArmStreamTrajectoryReward
    (Env := Env) (K := K)
  let environment := stationaryLatentArmStreamTrajectoryEnvironment
    (Env := Env) (K := K)
  let arm := fun sample => selectedArm (environment sample)
  let bad := fun t : Nat =>
    {sample |
      0 < pullCount (action sample) (arm sample) t ∧
      UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) (arm sample) t : Real)) <=
        mean (environment sample) (arm sample)}
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryReward_apply
  have henvironment : Measurable environment :=
    measurable_stationaryLatentArmStreamTrajectoryEnvironment
  have harm : Measurable arm := hselectedArm.comp henvironment
  have hmean : Measurable (fun sample =>
      mean (environment sample) (arm sample)) :=
    hmeas_mean.comp (henvironment.prodMk harm)
  have hbad : forall t, MeasurableSet (bad t) := by
    intro t
    have hpull : Measurable (fun sample =>
        pullCount (action sample) (arm sample) t) :=
      measurable_pullCount_selectedArm action haction arm harm t
    have hemp : Measurable (fun sample =>
        UCB.realEmpiricalMean
          (action sample) (reward sample) (arm sample) t) :=
      measurable_realEmpiricalMean_selectedArm
        action reward haction hreward arm harm t
    have hwidth : Measurable (fun sample =>
        Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) /
            (pullCount (action sample) (arm sample) t : Real))) :=
      (measurable_const.div
        ((measurable_of_countable fun k : Nat => (k : Real)).comp hpull)).sqrt
    exact (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le (hemp.add hwidth) hmean)
  have hevent : MeasurableSet {sample | ∃ t < n,
      0 < pullCount (action sample) (arm sample) t ∧
      UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) (arm sample) t : Real)) <=
        mean (environment sample) (arm sample)} := by
    have hunion : MeasurableSet (⋃ t ∈ Finset.range n, bad t) :=
      (Finset.range n).measurableSet_biUnion fun t _ht => hbad t
    have heq : {sample | ∃ t < n,
        0 < pullCount (action sample) (arm sample) t ∧
        UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
            Real.sqrt
              (2 * (sigma2 : Real) * Real.log (1 / delta) /
                (pullCount (action sample) (arm sample) t : Real)) <=
          mean (environment sample) (arm sample)} =
        ⋃ t ∈ Finset.range n, bad t := by
      ext sample
      simp [bad, and_left_comm]
    rw [heq]
    exact hunion
  unfold stationaryLatentArmStreamTrajectoryMeasure
  apply measure_compProd_le_of_forall_kernel_apply_le prior
    (stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm) _ hevent
  intro env
  simpa [action, reward, environment, arm,
    stationaryLatentArmStreamTrajectoryAction,
    stationaryLatentArmStreamTrajectoryReward,
    stationaryLatentArmStreamTrajectoryEnvironment,
    stationaryLatentArmStreamTrajectoryKernel_apply] using
    measure_latentArmStreamTrajectory_exists_realEmpiricalMean_add_width_le_mean_le
      algorithm env (stationaryRewardKernelAt rewardKernel env)
        (selectedArm env) (mean env (selectedArm env)) sigma2
        (hsubG env (selectedArm env)) hsigma2 delta hdelta hdelta_one n

/-- Prior-mixed lower-confidence failure bound for the clipped score radius. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_realEmpiricalMean_add_width_le_mean
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (delta : Real) (arm : Fin K) (n : Nat) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          0 < pullCount
              (stationaryLatentArmStreamTrajectoryAction sample) arm n ∧
          UCB.realEmpiricalMean
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm n +
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (stationaryLatentArmStreamTrajectoryAction sample) arm n :
                      Real)) <=
            mean
              (stationaryLatentArmStreamTrajectoryEnvironment sample) arm} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(clippedCountWidthThreshold sigma2 delta k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  let action := stationaryLatentArmStreamTrajectoryAction
    (Env := Env) (K := K)
  let reward := stationaryLatentArmStreamTrajectoryReward
    (Env := Env) (K := K)
  let environment := stationaryLatentArmStreamTrajectoryEnvironment
    (Env := Env) (K := K)
  have hsubset :
      {sample |
        0 < pullCount (action sample) arm n ∧
        UCB.realEmpiricalMean (action sample) (reward sample) arm n +
            Real.sqrt
              (2 * (sigma2 : Real) * Real.log (1 / delta) /
                (pullCount (action sample) arm n : Real)) <=
          mean (environment sample) arm} ⊆
      {sample |
        0 < pullCount (action sample) arm n ∧
        clippedCountWidthThreshold sigma2 delta
            (pullCount (action sample) arm n) <=
          (pullCount (action sample) arm n : Real) *
              mean (environment sample) arm -
            sumRewards (action sample) (reward sample) arm n} := by
    intro sample hsample
    exact ⟨hsample.1,
      clippedCountWidthThreshold_le_mul_mean_sub_sumRewards
        (action sample) (reward sample) arm n (mean (environment sample) arm)
        sigma2 delta hsample.1 hsample.2⟩
  calc
    _ <= stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          0 < pullCount (action sample) arm n ∧
          clippedCountWidthThreshold sigma2 delta
              (pullCount (action sample) arm n) <=
            (pullCount (action sample) arm n : Real) *
                mean (environment sample) arm -
              sumRewards (action sample) (reward sample) arm n} :=
      measure_mono hsubset
    _ <= _ := by
      exact stationaryLatentArmStreamTrajectoryMeasure_pos_and_sumRewards_lower_tail
        prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG arm n
          (clippedCountWidthThreshold sigma2 delta)
          (fun k _hk _hkn => clippedCountWidthThreshold_nonneg sigma2 delta k)

/-- Prior-mixed upper-confidence failure bound for the clipped score radius. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_mean_le_realEmpiricalMean_sub_width
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (delta : Real) (arm : Fin K) (n : Nat) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          0 < pullCount
              (stationaryLatentArmStreamTrajectoryAction sample) arm n ∧
          mean
              (stationaryLatentArmStreamTrajectoryEnvironment sample) arm <=
            UCB.realEmpiricalMean
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm n -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (stationaryLatentArmStreamTrajectoryAction sample) arm n :
                      Real))} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(clippedCountWidthThreshold sigma2 delta k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  let action := stationaryLatentArmStreamTrajectoryAction
    (Env := Env) (K := K)
  let reward := stationaryLatentArmStreamTrajectoryReward
    (Env := Env) (K := K)
  let environment := stationaryLatentArmStreamTrajectoryEnvironment
    (Env := Env) (K := K)
  have hsubset :
      {sample |
        0 < pullCount (action sample) arm n ∧
        mean (environment sample) arm <=
          UCB.realEmpiricalMean (action sample) (reward sample) arm n -
            Real.sqrt
              (2 * (sigma2 : Real) * Real.log (1 / delta) /
                (pullCount (action sample) arm n : Real))} ⊆
      {sample |
        0 < pullCount (action sample) arm n ∧
        clippedCountWidthThreshold sigma2 delta
            (pullCount (action sample) arm n) <=
          sumRewards (action sample) (reward sample) arm n -
            (pullCount (action sample) arm n : Real) *
              mean (environment sample) arm} := by
    intro sample hsample
    exact ⟨hsample.1,
      clippedCountWidthThreshold_le_sumRewards_sub_mul_mean
        (action sample) (reward sample) arm n (mean (environment sample) arm)
        sigma2 delta hsample.1 hsample.2⟩
  calc
    _ <= stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          0 < pullCount (action sample) arm n ∧
          clippedCountWidthThreshold sigma2 delta
              (pullCount (action sample) arm n) <=
            sumRewards (action sample) (reward sample) arm n -
              (pullCount (action sample) arm n : Real) *
                mean (environment sample) arm} :=
      measure_mono hsubset
    _ <= _ := by
      exact stationaryLatentArmStreamTrajectoryMeasure_pos_and_sumRewards_upper_tail
        prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG arm n
          (clippedCountWidthThreshold sigma2 delta)
          (fun k _hk _hkn => clippedCountWidthThreshold_nonneg sigma2 delta k)

/-- Simplified `n * delta` lower-confidence failure bound. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_realEmpiricalMean_add_width_le_mean_le_nat_mul_delta
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (arm : Fin K) (n : Nat) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          0 < pullCount
              (stationaryLatentArmStreamTrajectoryAction sample) arm n ∧
          UCB.realEmpiricalMean
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm n +
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (stationaryLatentArmStreamTrajectoryAction sample) arm n :
                      Real)) <=
            mean
              (stationaryLatentArmStreamTrajectoryEnvironment sample) arm} <=
      (n : ENNReal) * ENNReal.ofReal delta := by
  calc
    _ <= ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(clippedCountWidthThreshold sigma2 delta k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) :=
      stationaryLatentArmStreamTrajectoryMeasure_realEmpiricalMean_add_width_le_mean
        prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG delta arm n
    _ = _ := sum_clippedCountWidthThreshold_tail_eq
      sigma2 delta n hsigma2 hdelta hdelta_one

/-- Simplified `n * delta` upper-confidence failure bound. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_mean_le_realEmpiricalMean_sub_width_le_nat_mul_delta
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (arm : Fin K) (n : Nat) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample |
          0 < pullCount
              (stationaryLatentArmStreamTrajectoryAction sample) arm n ∧
          mean
              (stationaryLatentArmStreamTrajectoryEnvironment sample) arm <=
            UCB.realEmpiricalMean
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm n -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (stationaryLatentArmStreamTrajectoryAction sample) arm n :
                      Real))} <=
      (n : ENNReal) * ENNReal.ofReal delta := by
  calc
    _ <= ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(clippedCountWidthThreshold sigma2 delta k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) :=
      stationaryLatentArmStreamTrajectoryMeasure_mean_le_realEmpiricalMean_sub_width
        prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG delta arm n
    _ = _ := sum_clippedCountWidthThreshold_tail_eq
      sigma2 delta n hsigma2 hdelta hdelta_one

/-- Bayesian prior augmented with the stationary latent arm stream. -/
noncomputable def stationaryLatentArmStreamPrior
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (prior : Measure Env) (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel] :
    Measure (Env × UCB.ArmRewardStream K) :=
  prior ⊗ₘ stationaryArmStreamKernel rewardKernel

instance instStationaryLatentArmStreamPriorIsProbability
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel] :
    IsProbabilityMeasure (stationaryLatentArmStreamPrior prior rewardKernel) := by
  unfold stationaryLatentArmStreamPrior
  infer_instance

/--
Canonical trajectory measure in the left-associated sample shape consumed by
the Thompson Bayesian-regret decomposition.
-/
noncomputable def stationaryLatentArmStreamCanonicalTrajectoryMeasure
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (prior : Measure Env) (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real) :
    Measure
      ((Env × UCB.ArmRewardStream K) × ((n : Nat) -> Fin K × Real)) :=
  stationaryLatentArmStreamPrior prior rewardKernel ⊗ₘ
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm
      (latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K))

instance instStationaryLatentArmStreamCanonicalTrajectoryMeasureIsProbability
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real) :
    IsProbabilityMeasure
      (stationaryLatentArmStreamCanonicalTrajectoryMeasure
        prior rewardKernel algorithm) := by
  unfold stationaryLatentArmStreamCanonicalTrajectoryMeasure
  infer_instance

/-- The concentration and decomposition sample shapes agree by product associativity. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_map_prodAssoc_symm
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (prior : Measure Env)
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real) :
    (stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm).map
        MeasurableEquiv.prodAssoc.symm =
      stationaryLatentArmStreamCanonicalTrajectoryMeasure
        prior rewardKernel algorithm := by
  unfold stationaryLatentArmStreamTrajectoryMeasure
  unfold stationaryLatentArmStreamTrajectoryKernel
  unfold stationaryLatentArmStreamCanonicalTrajectoryMeasure
  unfold stationaryLatentArmStreamPrior
  exact Measure.compProd_assoc

/--
Decomposition-facing lower-confidence failure bound on the canonical augmented
trajectory measure.
-/
theorem stationaryLatentArmStreamCanonicalTrajectoryMeasure_realEmpiricalMean_add_width_le_mean_le_nat_mul_delta
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (arm : Fin K) (n : Nat) :
    stationaryLatentArmStreamCanonicalTrajectoryMeasure
        prior rewardKernel algorithm
        {sample :
            (Env × UCB.ArmRewardStream K) × ((n : Nat) → Fin K × Real) |
          0 < pullCount (environmentTrajectoryAction sample) arm n ∧
          UCB.realEmpiricalMean
                (environmentTrajectoryAction sample)
                (environmentTrajectoryReward sample) arm n +
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount (environmentTrajectoryAction sample) arm n : Real)) <=
            mean sample.1.1 arm} <=
      (n : ENNReal) * ENNReal.ofReal delta := by
  let action := environmentTrajectoryAction
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let reward := environmentTrajectoryReward
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_environmentTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_environmentTrajectoryReward_apply
  have hpull : Measurable (fun sample => pullCount (action sample) arm n) :=
    measurable_pullCount action haction arm n
  have hemp : Measurable (fun sample =>
      UCB.realEmpiricalMean (action sample) (reward sample) arm n) :=
    UCB.measurable_realEmpiricalMean action reward haction hreward arm n
  have hwidth : Measurable (fun sample =>
      Real.sqrt
        (2 * (sigma2 : Real) * Real.log (1 / delta) /
          (pullCount (action sample) arm n : Real))) :=
    (measurable_const.div
      ((measurable_of_countable fun k : Nat => (k : Real)).comp hpull)).sqrt
  have hmean : Measurable (fun sample :
      (Env × UCB.ArmRewardStream K) × ((n : Nat) → Fin K × Real) =>
        mean sample.1.1 arm) :=
    hmeas_mean.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_const)
  have hevent : MeasurableSet {sample |
      0 < pullCount (action sample) arm n ∧
      UCB.realEmpiricalMean (action sample) (reward sample) arm n +
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) arm n : Real)) <=
        mean sample.1.1 arm} :=
    (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le (hemp.add hwidth) hmean)
  rw [← stationaryLatentArmStreamTrajectoryMeasure_map_prodAssoc_symm
    prior rewardKernel algorithm,
    Measure.map_apply MeasurableEquiv.prodAssoc.symm.measurable hevent]
  simpa [action, reward, environmentTrajectoryAction,
    environmentTrajectoryReward,
    stationaryLatentArmStreamTrajectoryAction,
    stationaryLatentArmStreamTrajectoryReward,
    stationaryLatentArmStreamTrajectoryEnvironment] using
    stationaryLatentArmStreamTrajectoryMeasure_realEmpiricalMean_add_width_le_mean_le_nat_mul_delta
      prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG hsigma2 delta
        hdelta hdelta_one arm n

/--
Decomposition-facing upper-confidence failure bound on the canonical augmented
trajectory measure.
-/
theorem stationaryLatentArmStreamCanonicalTrajectoryMeasure_mean_le_realEmpiricalMean_sub_width_le_nat_mul_delta
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (arm : Fin K) (n : Nat) :
    stationaryLatentArmStreamCanonicalTrajectoryMeasure
        prior rewardKernel algorithm
        {sample :
            (Env × UCB.ArmRewardStream K) × ((n : Nat) → Fin K × Real) |
          0 < pullCount (environmentTrajectoryAction sample) arm n ∧
          mean sample.1.1 arm <=
            UCB.realEmpiricalMean
                (environmentTrajectoryAction sample)
                (environmentTrajectoryReward sample) arm n -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount (environmentTrajectoryAction sample) arm n : Real))} <=
      (n : ENNReal) * ENNReal.ofReal delta := by
  let action := environmentTrajectoryAction
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let reward := environmentTrajectoryReward
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_environmentTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_environmentTrajectoryReward_apply
  have hpull : Measurable (fun sample => pullCount (action sample) arm n) :=
    measurable_pullCount action haction arm n
  have hemp : Measurable (fun sample =>
      UCB.realEmpiricalMean (action sample) (reward sample) arm n) :=
    UCB.measurable_realEmpiricalMean action reward haction hreward arm n
  have hwidth : Measurable (fun sample =>
      Real.sqrt
        (2 * (sigma2 : Real) * Real.log (1 / delta) /
          (pullCount (action sample) arm n : Real))) :=
    (measurable_const.div
      ((measurable_of_countable fun k : Nat => (k : Real)).comp hpull)).sqrt
  have hmean : Measurable (fun sample :
      (Env × UCB.ArmRewardStream K) × ((n : Nat) → Fin K × Real) =>
        mean sample.1.1 arm) :=
    hmeas_mean.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_const)
  have hevent : MeasurableSet {sample |
      0 < pullCount (action sample) arm n ∧
      mean sample.1.1 arm <=
        UCB.realEmpiricalMean (action sample) (reward sample) arm n -
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) arm n : Real))} :=
    (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le hmean (hemp.sub hwidth))
  rw [← stationaryLatentArmStreamTrajectoryMeasure_map_prodAssoc_symm
    prior rewardKernel algorithm,
    Measure.map_apply MeasurableEquiv.prodAssoc.symm.measurable hevent]
  simpa [action, reward, environmentTrajectoryAction,
    environmentTrajectoryReward,
    stationaryLatentArmStreamTrajectoryAction,
    stationaryLatentArmStreamTrajectoryReward,
    stationaryLatentArmStreamTrajectoryEnvironment] using
    stationaryLatentArmStreamTrajectoryMeasure_mean_le_realEmpiricalMean_sub_width_le_nat_mul_delta
      prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG hsigma2 delta
        hdelta hdelta_one arm n

/--
Decomposition-facing horizon-uniform lower-confidence failure for a measurable
environment-dependent arm, with the exact `(n - 1) * delta` cost.
-/
theorem stationaryLatentArmStreamCanonicalTrajectoryMeasure_exists_selectedArm_realEmpiricalMean_add_width_le_mean_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (selectedArm : Env -> Fin K) (hselectedArm : Measurable selectedArm)
    (n : Nat) :
    stationaryLatentArmStreamCanonicalTrajectoryMeasure
        prior rewardKernel algorithm
        {sample :
            (Env × UCB.ArmRewardStream K) × ((n : Nat) -> Fin K × Real) |
          ∃ t < n,
            0 < pullCount (environmentTrajectoryAction sample)
                (selectedArm sample.1.1) t ∧
            UCB.realEmpiricalMean
                  (environmentTrajectoryAction sample)
                  (environmentTrajectoryReward sample)
                  (selectedArm sample.1.1) t +
                Real.sqrt
                  (2 * (sigma2 : Real) * Real.log (1 / delta) /
                    (pullCount (environmentTrajectoryAction sample)
                      (selectedArm sample.1.1) t : Real)) <=
              mean sample.1.1 (selectedArm sample.1.1)} <=
      (n - 1 : Nat) * ENNReal.ofReal delta := by
  classical
  let action := environmentTrajectoryAction
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let reward := environmentTrajectoryReward
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let environment := fun sample :
      (Env × UCB.ArmRewardStream K) × ((n : Nat) -> Fin K × Real) =>
    sample.1.1
  let arm := fun sample :
      (Env × UCB.ArmRewardStream K) × ((n : Nat) -> Fin K × Real) =>
    selectedArm (environment sample)
  let bad := fun t : Nat =>
    {sample |
      0 < pullCount (action sample) (arm sample) t ∧
      UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) (arm sample) t : Real)) <=
        mean (environment sample) (arm sample)}
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_environmentTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_environmentTrajectoryReward_apply
  have henvironment : Measurable environment :=
    measurable_fst.comp measurable_fst
  have harm : Measurable arm := hselectedArm.comp henvironment
  have hmean : Measurable (fun sample =>
      mean (environment sample) (arm sample)) :=
    hmeas_mean.comp (henvironment.prodMk harm)
  have hbad : forall t, MeasurableSet (bad t) := by
    intro t
    have hpull : Measurable (fun sample =>
        pullCount (action sample) (arm sample) t) :=
      measurable_pullCount_selectedArm action haction arm harm t
    have hemp : Measurable (fun sample =>
        UCB.realEmpiricalMean
          (action sample) (reward sample) (arm sample) t) :=
      measurable_realEmpiricalMean_selectedArm
        action reward haction hreward arm harm t
    have hwidth : Measurable (fun sample =>
        Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) /
            (pullCount (action sample) (arm sample) t : Real))) :=
      (measurable_const.div
        ((measurable_of_countable fun k : Nat => (k : Real)).comp hpull)).sqrt
    exact (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le (hemp.add hwidth) hmean)
  have hevent : MeasurableSet {sample | ∃ t < n,
      0 < pullCount (action sample) (arm sample) t ∧
      UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) (arm sample) t : Real)) <=
        mean (environment sample) (arm sample)} := by
    have hunion : MeasurableSet (⋃ t ∈ Finset.range n, bad t) :=
      (Finset.range n).measurableSet_biUnion fun t _ht => hbad t
    have heq : {sample | ∃ t < n,
        0 < pullCount (action sample) (arm sample) t ∧
        UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
            Real.sqrt
              (2 * (sigma2 : Real) * Real.log (1 / delta) /
                (pullCount (action sample) (arm sample) t : Real)) <=
          mean (environment sample) (arm sample)} =
        ⋃ t ∈ Finset.range n, bad t := by
      ext sample
      simp [bad, and_left_comm]
    rw [heq]
    exact hunion
  rw [← stationaryLatentArmStreamTrajectoryMeasure_map_prodAssoc_symm
    prior rewardKernel algorithm,
    Measure.map_apply MeasurableEquiv.prodAssoc.symm.measurable hevent]
  simpa [action, reward, environment, arm,
    environmentTrajectoryAction, environmentTrajectoryReward,
    stationaryLatentArmStreamTrajectoryAction,
    stationaryLatentArmStreamTrajectoryReward,
    stationaryLatentArmStreamTrajectoryEnvironment] using
    stationaryLatentArmStreamTrajectoryMeasure_exists_selectedArm_realEmpiricalMean_add_width_le_mean_le
      prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG hsigma2 delta
        hdelta hdelta_one selectedArm hselectedArm n

/--
The first pinned-LML Thompson concentration expectation: the finite-horizon
best-action mean minus clipped-UCB sum is controlled by the horizon-uniform
lower-confidence failure event.
-/
theorem stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_sum_mean_bestAction_sub_clippedUCB_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (bestAction : Env -> Fin K) (hbestAction : Measurable bestAction)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (l u : Real) (hlu : l <= u)
    (hmeanMem : forall env arm, mean env arm ∈ Set.Icc l u)
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    integral
        (stationaryLatentArmStreamCanonicalTrajectoryMeasure
          prior rewardKernel algorithm)
        (fun sample =>
          ∑ t ∈ Finset.range n,
            (mean sample.1.1 (bestAction sample.1.1) -
              clippedUCB l u (sigma2 : Real) delta
                (environmentTrajectoryAction sample)
                (environmentTrajectoryReward sample)
                (bestAction sample.1.1) t)) <=
      (u - l) * (n - 1) * n * delta := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  let mu := stationaryLatentArmStreamCanonicalTrajectoryMeasure
    prior rewardKernel algorithm
  let action := environmentTrajectoryAction
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let reward := environmentTrajectoryReward
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let environment := fun sample :
      (Env × UCB.ArmRewardStream K) × ((n : Nat) -> Fin K × Real) =>
    sample.1.1
  let arm := fun sample :
      (Env × UCB.ArmRewardStream K) × ((n : Nat) -> Fin K × Real) =>
    bestAction (environment sample)
  let bad := fun t : Nat =>
    {sample |
      0 < pullCount (action sample) (arm sample) t ∧
      UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) (arm sample) t : Real)) <=
        mean (environment sample) (arm sample)}
  let F := ⋃ t ∈ Finset.range n, bad t
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_environmentTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_environmentTrajectoryReward_apply
  have henvironment : Measurable environment :=
    measurable_fst.comp measurable_fst
  have harm : Measurable arm := hbestAction.comp henvironment
  have hmean : Measurable (fun sample =>
      mean (environment sample) (arm sample)) :=
    hmeas_mean.comp (henvironment.prodMk harm)
  have hbad : forall t, MeasurableSet (bad t) := by
    intro t
    have hpull : Measurable (fun sample =>
        pullCount (action sample) (arm sample) t) :=
      measurable_pullCount_selectedArm action haction arm harm t
    have hemp : Measurable (fun sample =>
        UCB.realEmpiricalMean
          (action sample) (reward sample) (arm sample) t) :=
      measurable_realEmpiricalMean_selectedArm
        action reward haction hreward arm harm t
    have hwidth : Measurable (fun sample =>
        Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) /
            (pullCount (action sample) (arm sample) t : Real))) :=
      (measurable_const.div
        ((measurable_of_countable fun k : Nat => (k : Real)).comp hpull)).sqrt
    exact (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le (hemp.add hwidth) hmean)
  have hF : MeasurableSet F :=
    (Finset.range n).measurableSet_biUnion fun t _ht => hbad t
  have hmeanLift : Measurable (fun input :
      (Env × UCB.ArmRewardStream K) × Fin K =>
        mean input.1.1 input.2) :=
    hmeas_mean.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmeanBest : Integrable (fun sample =>
      mean (environment sample) (arm sample)) mu := by
    simpa [environment, arm] using
      integrable_trajectoryMean_bestAction mu
        (fun envStream arm => mean envStream.1 arm) hmeanLift
        (fun envStream arm => hmeanMem envStream.1 arm)
        (fun envStream => bestAction envStream.1)
        (hbestAction.comp measurable_fst)
  have hscoreBest : forall t, Integrable (fun sample =>
      clippedUCB l u (sigma2 : Real) delta
        (action sample) (reward sample) (arm sample) t) mu := by
    intro t
    simpa [action, reward, environment, arm,
      trajectoryBestHistoryScore, clippedUCBHistoryScore_atBestTrace] using
      integrable_trajectoryBestHistoryScore_clippedUCB mu
        (fun envStream => bestAction envStream.1)
        (hbestAction.comp measurable_fst)
        l u (sigma2 : Real) delta hlu t
  have hsum : Integrable (fun sample =>
      ∑ t ∈ Finset.range n,
        (mean (environment sample) (arm sample) -
          clippedUCB l u (sigma2 : Real) delta
            (action sample) (reward sample) (arm sample) t)) mu := by
    exact IntegrabilitySums.integrable_finset_sum mu (Finset.range n)
      (fun t sample =>
        mean (environment sample) (arm sample) -
          clippedUCB l u (sigma2 : Real) delta
            (action sample) (reward sample) (arm sample) t)
      (fun t _ht => hmeanBest.sub (hscoreBest t))
  have hprob : mu F <= (n - 1 : ENNReal) * ENNReal.ofReal delta := by
    have heq : F = {sample | ∃ t < n,
        0 < pullCount (action sample) (arm sample) t ∧
        UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
            Real.sqrt
              (2 * (sigma2 : Real) * Real.log (1 / delta) /
                (pullCount (action sample) (arm sample) t : Real)) <=
          mean (environment sample) (arm sample)} := by
      ext sample
      simp [F, bad, and_left_comm]
    rw [heq]
    simpa [mu, action, reward, environment, arm] using
      stationaryLatentArmStreamCanonicalTrajectoryMeasure_exists_selectedArm_realEmpiricalMean_add_width_le_mean_le
        prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG hsigma2
          delta hdelta hdelta_one bestAction hbestAction n
  have hprobReal : mu.real F <= (n - 1 : Nat) * delta := by
    apply ENNReal.toReal_le_of_le_ofReal
    · positivity
    · simpa [ENNReal.ofReal_mul (Nat.cast_nonneg (n - 1))] using hprob
  change integral mu (fun sample =>
      ∑ t ∈ Finset.range n,
        (mean (environment sample) (arm sample) -
          clippedUCB l u (sigma2 : Real) delta
            (action sample) (reward sample) (arm sample) t)) <= _
  calc
    _ <= ∫ sample in F,
        ∑ t ∈ Finset.range n,
          (mean (environment sample) (arm sample) -
            clippedUCB l u (sigma2 : Real) delta
              (action sample) (reward sample) (arm sample) t) ∂mu := by
      rw [← integral_add_compl hF hsum]
      apply add_le_of_nonpos_right
      apply setIntegral_nonpos hF.compl
      intro sample hsample
      apply Finset.sum_nonpos
      intro t ht
      have hnot : sample ∉ bad t := by
        intro hmem
        exact hsample (Set.mem_iUnion.2 ⟨t,
          Set.mem_iUnion.2 ⟨Finset.mem_range.mpr (Finset.mem_range.mp ht), hmem⟩⟩)
      have hmeanRange := hmeanMem (environment sample) (arm sample)
      have hscoreRange := clippedUCB_mem_Icc
        l u (sigma2 : Real) delta hlu
        (action sample) (reward sample) (arm sample) t
      simp only [bad, Set.mem_setOf_eq] at hnot
      by_cases hcount : pullCount (action sample) (arm sample) t = 0
      · simp [clippedUCB, hcount]
        exact hmeanRange.2
      · have hcountPos : 0 < pullCount (action sample) (arm sample) t :=
          Nat.pos_of_ne_zero hcount
        have hraw : mean (environment sample) (arm sample) <
            UCB.realEmpiricalMean (action sample) (reward sample) (arm sample) t +
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount (action sample) (arm sample) t : Real)) := by
          exact lt_of_not_ge (fun hle => hnot ⟨hcountPos, hle⟩)
        unfold clippedUCB
        rw [if_neg hcount]
        grind
    _ <= ∫ sample in F,
        ∑ _t ∈ Finset.range n, (u - l) ∂mu := by
      apply setIntegral_mono_on hsum.integrableOn
        (integrable_const (c := (Finset.range n).sum fun _ => u - l)).integrableOn hF
      intro sample _hsample
      apply Finset.sum_le_sum
      intro t _ht
      have hmeanRange := hmeanMem (environment sample) (arm sample)
      have hscoreRange := clippedUCB_mem_Icc
        l u (sigma2 : Real) delta hlu
        (action sample) (reward sample) (arm sample) t
      nlinarith [hmeanRange.2, hscoreRange.1]
    _ = mu.real F * (n * (u - l)) := by
      simp_rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        setIntegral_const, smul_eq_mul]
    _ <= ((n - 1 : Nat) * delta) * (n * (u - l)) := by
      exact mul_le_mul_of_nonneg_right hprobReal
        (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hlu))
    _ = (u - l) * (n - 1) * n * delta := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn)]
      ring

/-- A finite union of upper prefix deviations pays once per positive pull count. -/
theorem measure_biUnion_clippedCountWidthThreshold_le_armPrefixSum_sub_mul_le
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (m : Nat) :
    UCB.armStreamMeasure nu
        (⋃ k ∈ Finset.Icc 1 m,
          {stream : UCB.ArmRewardStream K |
            clippedCountWidthThreshold sigma2 delta k <=
              UCB.armPrefixSum arm k stream - (k : Real) * mean}) <=
      (m : ENNReal) * ENNReal.ofReal delta := by
  classical
  calc
    _ <= (Finset.Icc 1 m).sum (fun k =>
        UCB.armStreamMeasure nu
          {stream : UCB.ArmRewardStream K |
            clippedCountWidthThreshold sigma2 delta k <=
              UCB.armPrefixSum arm k stream - (k : Real) * mean}) :=
      ProbabilityUnionBound.measure_biUnion_finset_le
        (UCB.armStreamMeasure nu) (Finset.Icc 1 m) _
    _ <= (Finset.Icc 1 m).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(clippedCountWidthThreshold sigma2 delta k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact UCB.measure_armPrefixSum_sub_mul_ge_le
        nu arm mean sigma2 hsubG k
          (clippedCountWidthThreshold_nonneg sigma2 delta k)
    _ = _ := by
      simpa [UCB.positiveCountFilter_eq_Icc] using
        sum_clippedCountWidthThreshold_tail_eq
          sigma2 delta m hsigma2 hdelta hdelta_one

/--
Finite-horizon upper-confidence failure for one arm on the coupled trajectory.
Times with the same positive pull count collapse to one latent-stream prefix
event, preserving the exact `(n - 1) * delta` cost.
-/
theorem measure_latentArmStreamTrajectory_exists_mean_le_realEmpiricalMean_sub_width_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    latentArmStreamTrajectoryMeasure algorithm env nu
        {sample | ∃ t < n,
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm t ∧
          mean <=
            UCB.realEmpiricalMean
                (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm t -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (latentArmStreamTrajectoryAction sample) arm t : Real))} <=
      (n - 1 : Nat) * ENNReal.ofReal delta := by
  classical
  let mu := latentArmStreamTrajectoryMeasure algorithm env nu
  let action := latentArmStreamTrajectoryAction (K := K)
  let rewardFromStream :=
    UCB.rewardFromArmStream action
      (Prod.fst : UCB.ArmRewardStream K ×
        ((n : Nat) -> Fin K × Real) -> UCB.ArmRewardStream K)
  let counts := Finset.Icc 1 (n - 1)
  let fixedEvent := fun k : Nat =>
    {stream : UCB.ArmRewardStream K |
      clippedCountWidthThreshold sigma2 delta k <=
        UCB.armPrefixSum arm k stream - (k : Real) * mean}
  have hfixedEvent : forall k, MeasurableSet (fixedEvent k) := by
    intro k
    exact measurableSet_le measurable_const
      ((UCB.measurable_armPrefixSum arm k).sub measurable_const)
  have hstreamEvent : MeasurableSet (⋃ k ∈ counts, fixedEvent k) :=
    counts.measurableSet_biUnion fun k _hk => hfixedEvent k
  calc
    _ = mu {sample | ∃ t < n,
          0 < pullCount (action sample) arm t ∧
          mean <=
            UCB.realEmpiricalMean (action sample) (rewardFromStream sample) arm t -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount (action sample) arm t : Real))} := by
      apply measure_congr
      filter_upwards
        [latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
          algorithm env nu] with sample hreward
      apply propext
      constructor
      · rintro ⟨t, ht, hcount, hindex⟩
        refine ⟨t, ht, hcount, ?_⟩
        simpa [rewardFromStream, action, hreward] using hindex
      · rintro ⟨t, ht, hcount, hindex⟩
        refine ⟨t, ht, hcount, ?_⟩
        simpa [rewardFromStream, action, hreward] using hindex
    _ <= mu (Prod.fst ⁻¹' (⋃ k ∈ counts, fixedEvent k)) := by
      apply measure_mono
      rintro sample ⟨t, ht, hcount, hindex⟩
      let k := pullCount (action sample) arm t
      have hk_le_t : k <= t := pullCount_le_time (action sample) arm t
      have hk_le : k <= n - 1 := by omega
      have hk_counts : k ∈ counts :=
        Finset.mem_Icc.mpr ⟨hcount, hk_le⟩
      have hthreshold :
          clippedCountWidthThreshold sigma2 delta k <=
            sumRewards (action sample) (rewardFromStream sample) arm t -
              (k : Real) * mean :=
        clippedCountWidthThreshold_le_sumRewards_sub_mul_mean
          (action sample) (rewardFromStream sample) arm t mean sigma2 delta
            hcount hindex
      have hprefix :
          clippedCountWidthThreshold sigma2 delta k <=
            UCB.armPrefixSum arm k sample.1 - (k : Real) * mean := by
        simpa [k, rewardFromStream,
          UCB.sumRewards_rewardFromArmStream_eq_armPrefixSum] using hthreshold
      simp only [Set.mem_preimage, Set.mem_iUnion]
      exact ⟨k, ⟨hk_counts, hprefix⟩⟩
    _ = UCB.armStreamMeasure nu (⋃ k ∈ counts, fixedEvent k) := by
      calc
        mu (Prod.fst ⁻¹' (⋃ k ∈ counts, fixedEvent k)) =
            Measure.map Prod.fst mu (⋃ k ∈ counts, fixedEvent k) :=
          (Measure.map_apply measurable_fst hstreamEvent).symm
        _ = Measure.map id (UCB.armStreamMeasure nu)
              (⋃ k ∈ counts, fixedEvent k) := by
          rw [(identDistrib_fst_latentArmStreamTrajectoryMeasure
            algorithm env nu).map_eq]
        _ = UCB.armStreamMeasure nu (⋃ k ∈ counts, fixedEvent k) := by
          rw [Measure.map_id]
    _ <= _ := by
      simpa [counts, fixedEvent] using
        measure_biUnion_clippedCountWidthThreshold_le_armPrefixSum_sub_mul_le
          nu arm mean sigma2 hsubG hsigma2 delta hdelta hdelta_one (n - 1)

/-- Finite-arm union of the horizon upper-confidence failures at fixed environment. -/
theorem measure_latentArmStreamTrajectory_exists_arm_exists_mean_le_realEmpiricalMean_sub_width_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (mean : Fin K -> Real) (sigma2 : NNReal)
    (hsubG : forall arm,
      HasSubgaussianMGF (fun reward => reward - mean arm) sigma2 (nu arm))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    latentArmStreamTrajectoryMeasure algorithm env nu
        {sample | ∃ arm : Fin K, ∃ t < n,
          0 < pullCount (latentArmStreamTrajectoryAction sample) arm t ∧
          mean arm <=
            UCB.realEmpiricalMean
                (latentArmStreamTrajectoryAction sample)
                (latentArmStreamTrajectoryReward sample) arm t -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (latentArmStreamTrajectoryAction sample) arm t : Real))} <=
      (K : ENNReal) * ((n - 1 : Nat) : ENNReal) * ENNReal.ofReal delta := by
  let bad := fun arm : Fin K =>
    {sample | ∃ t < n,
      0 < pullCount (latentArmStreamTrajectoryAction sample) arm t ∧
      mean arm <=
        UCB.realEmpiricalMean
            (latentArmStreamTrajectoryAction sample)
            (latentArmStreamTrajectoryReward sample) arm t -
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (latentArmStreamTrajectoryAction sample) arm t : Real))}
  have heq : {sample | ∃ arm : Fin K, ∃ t < n,
      0 < pullCount (latentArmStreamTrajectoryAction sample) arm t ∧
      mean arm <=
        UCB.realEmpiricalMean
            (latentArmStreamTrajectoryAction sample)
            (latentArmStreamTrajectoryReward sample) arm t -
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (latentArmStreamTrajectoryAction sample) arm t : Real))} =
      ⋃ arm, bad arm := by
    ext sample
    simp [bad]
  rw [heq]
  calc
    _ <= ∑ arm : Fin K,
        latentArmStreamTrajectoryMeasure algorithm env nu (bad arm) :=
      ProbabilityUnionBound.measure_iUnion_fintype_le_sum _ _
    _ <= ∑ _arm : Fin K,
        ((n - 1 : Nat) : ENNReal) * ENNReal.ofReal delta := by
      apply Finset.sum_le_sum
      intro arm _harm
      simpa [bad] using
        measure_latentArmStreamTrajectory_exists_mean_le_realEmpiricalMean_sub_width_le
          algorithm env nu arm (mean arm) sigma2 (hsubG arm) hsigma2
            delta hdelta hdelta_one n
    _ = _ := by
      simp [nsmul_eq_mul]
      ring

/-- Prior mixing preserves the finite-arm horizon upper-confidence budget. -/
theorem stationaryLatentArmStreamTrajectoryMeasure_exists_arm_exists_mean_le_realEmpiricalMean_sub_width_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    stationaryLatentArmStreamTrajectoryMeasure prior rewardKernel algorithm
        {sample | ∃ arm : Fin K, ∃ t < n,
          0 < pullCount
            (stationaryLatentArmStreamTrajectoryAction sample) arm t ∧
          mean (stationaryLatentArmStreamTrajectoryEnvironment sample) arm <=
            UCB.realEmpiricalMean
                (stationaryLatentArmStreamTrajectoryAction sample)
                (stationaryLatentArmStreamTrajectoryReward sample) arm t -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount
                    (stationaryLatentArmStreamTrajectoryAction sample) arm t : Real))} <=
      (K : ENNReal) * ((n - 1 : Nat) : ENNReal) * ENNReal.ofReal delta := by
  classical
  let action := stationaryLatentArmStreamTrajectoryAction (Env := Env) (K := K)
  let reward := stationaryLatentArmStreamTrajectoryReward (Env := Env) (K := K)
  let environment := stationaryLatentArmStreamTrajectoryEnvironment
    (Env := Env) (K := K)
  let bad := fun arm : Fin K => fun t : Nat =>
    {sample |
      0 < pullCount (action sample) arm t ∧
      mean (environment sample) arm <=
        UCB.realEmpiricalMean (action sample) (reward sample) arm t -
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) arm t : Real))}
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_stationaryLatentArmStreamTrajectoryReward_apply
  have henvironment : Measurable environment :=
    measurable_stationaryLatentArmStreamTrajectoryEnvironment
  have hbad : forall arm t, MeasurableSet (bad arm t) := by
    intro arm t
    have hpull : Measurable (fun sample => pullCount (action sample) arm t) :=
      measurable_pullCount action haction arm t
    have hemp : Measurable (fun sample =>
        UCB.realEmpiricalMean (action sample) (reward sample) arm t) :=
      UCB.measurable_realEmpiricalMean action reward haction hreward arm t
    have hwidth : Measurable (fun sample =>
        Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) /
            (pullCount (action sample) arm t : Real))) :=
      (measurable_const.div
        ((measurable_of_countable fun k : Nat => (k : Real)).comp hpull)).sqrt
    have hmean : Measurable (fun sample => mean (environment sample) arm) :=
      hmeas_mean.comp (henvironment.prodMk measurable_const)
    exact (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le hmean (hemp.sub hwidth))
  have hevent : MeasurableSet {sample | ∃ arm : Fin K, ∃ t < n,
      0 < pullCount (action sample) arm t ∧
      mean (environment sample) arm <=
        UCB.realEmpiricalMean (action sample) (reward sample) arm t -
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) arm t : Real))} := by
    have hunion : MeasurableSet
        (⋃ arm : Fin K, ⋃ t ∈ Finset.range n, bad arm t) :=
      MeasurableSet.iUnion fun arm =>
        (Finset.range n).measurableSet_biUnion fun t _ht => hbad arm t
    have heq : {sample | ∃ arm : Fin K, ∃ t < n,
        0 < pullCount (action sample) arm t ∧
        mean (environment sample) arm <=
          UCB.realEmpiricalMean (action sample) (reward sample) arm t -
            Real.sqrt
              (2 * (sigma2 : Real) * Real.log (1 / delta) /
                (pullCount (action sample) arm t : Real))} =
        ⋃ arm : Fin K, ⋃ t ∈ Finset.range n, bad arm t := by
      ext sample
      simp [bad, and_left_comm]
    rw [heq]
    exact hunion
  unfold stationaryLatentArmStreamTrajectoryMeasure
  apply measure_compProd_le_of_forall_kernel_apply_le prior
    (stationaryLatentArmStreamTrajectoryKernel rewardKernel algorithm) _ hevent
  intro env
  simpa [action, reward, environment, bad,
    stationaryLatentArmStreamTrajectoryAction,
    stationaryLatentArmStreamTrajectoryReward,
    stationaryLatentArmStreamTrajectoryEnvironment,
    stationaryLatentArmStreamTrajectoryKernel_apply] using
    measure_latentArmStreamTrajectory_exists_arm_exists_mean_le_realEmpiricalMean_sub_width_le
      algorithm env (stationaryRewardKernelAt rewardKernel env) (mean env) sigma2
        (hsubG env) hsigma2 delta hdelta hdelta_one n

/--
Decomposition-facing finite-arm horizon upper-confidence failure with exact
`K * (n - 1) * delta` cost.
-/
theorem stationaryLatentArmStreamCanonicalTrajectoryMeasure_exists_arm_exists_mean_le_realEmpiricalMean_sub_width_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    stationaryLatentArmStreamCanonicalTrajectoryMeasure
        prior rewardKernel algorithm
        {sample | ∃ arm : Fin K, ∃ t < n,
          0 < pullCount (environmentTrajectoryAction sample) arm t ∧
          mean sample.1.1 arm <=
            UCB.realEmpiricalMean
                (environmentTrajectoryAction sample)
                (environmentTrajectoryReward sample) arm t -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount (environmentTrajectoryAction sample) arm t : Real))} <=
      (K : ENNReal) * ((n - 1 : Nat) : ENNReal) * ENNReal.ofReal delta := by
  let action := environmentTrajectoryAction
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let reward := environmentTrajectoryReward
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let bad := fun arm : Fin K => fun t : Nat =>
    {sample |
      0 < pullCount (action sample) arm t ∧
      mean sample.1.1 arm <=
        UCB.realEmpiricalMean (action sample) (reward sample) arm t -
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) arm t : Real))}
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_environmentTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_environmentTrajectoryReward_apply
  have hbad : forall arm t, MeasurableSet (bad arm t) := by
    intro arm t
    have hpull : Measurable (fun sample => pullCount (action sample) arm t) :=
      measurable_pullCount action haction arm t
    have hemp : Measurable (fun sample =>
        UCB.realEmpiricalMean (action sample) (reward sample) arm t) :=
      UCB.measurable_realEmpiricalMean action reward haction hreward arm t
    have hwidth : Measurable (fun sample =>
        Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) /
            (pullCount (action sample) arm t : Real))) :=
      (measurable_const.div
        ((measurable_of_countable fun k : Nat => (k : Real)).comp hpull)).sqrt
    have hmean : Measurable (fun sample :
        (Env × UCB.ArmRewardStream K) × ((n : Nat) -> Fin K × Real) =>
          mean sample.1.1 arm) :=
      hmeas_mean.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_const)
    exact (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le hmean (hemp.sub hwidth))
  have hevent : MeasurableSet {sample | ∃ arm : Fin K, ∃ t < n,
      0 < pullCount (action sample) arm t ∧
      mean sample.1.1 arm <=
        UCB.realEmpiricalMean (action sample) (reward sample) arm t -
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) arm t : Real))} := by
    have hunion : MeasurableSet
        (⋃ arm : Fin K, ⋃ t ∈ Finset.range n, bad arm t) :=
      MeasurableSet.iUnion fun arm =>
        (Finset.range n).measurableSet_biUnion fun t _ht => hbad arm t
    have heq : {sample | ∃ arm : Fin K, ∃ t < n,
        0 < pullCount (action sample) arm t ∧
        mean sample.1.1 arm <=
          UCB.realEmpiricalMean (action sample) (reward sample) arm t -
            Real.sqrt
              (2 * (sigma2 : Real) * Real.log (1 / delta) /
                (pullCount (action sample) arm t : Real))} =
        ⋃ arm : Fin K, ⋃ t ∈ Finset.range n, bad arm t := by
      ext sample
      simp [bad, and_left_comm]
    rw [heq]
    exact hunion
  rw [← stationaryLatentArmStreamTrajectoryMeasure_map_prodAssoc_symm
    prior rewardKernel algorithm,
    Measure.map_apply MeasurableEquiv.prodAssoc.symm.measurable hevent]
  simpa [action, reward, bad,
    environmentTrajectoryAction, environmentTrajectoryReward,
    stationaryLatentArmStreamTrajectoryAction,
    stationaryLatentArmStreamTrajectoryReward,
    stationaryLatentArmStreamTrajectoryEnvironment] using
    stationaryLatentArmStreamTrajectoryMeasure_exists_arm_exists_mean_le_realEmpiricalMean_sub_width_le
      prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG hsigma2
        delta hdelta hdelta_one n

/--
The second pinned-LML Thompson concentration expectation: selected-action
clipped-UCB excess is bounded by deterministic pull-count summation plus the
finite-arm horizon upper-confidence failure budget.
-/
theorem stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_sum_clippedUCB_action_sub_mean_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (algorithm : HistoryAlgorithm (Fin K) Real)
    (mean : Env -> Fin K -> Real)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (l u : Real) (hlu : l <= u)
    (hmeanMem : forall env arm, mean env arm ∈ Set.Icc l u)
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    integral
        (stationaryLatentArmStreamCanonicalTrajectoryMeasure
          prior rewardKernel algorithm)
        (fun sample =>
          ∑ t ∈ Finset.range n,
            (clippedUCB l u (sigma2 : Real) delta
                (environmentTrajectoryAction sample)
                (environmentTrajectoryReward sample)
                (environmentTrajectoryAction sample t) t -
              mean sample.1.1 (environmentTrajectoryAction sample t))) <=
      (u - l) * K +
        4 * Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) * K * n) +
        (u - l) * K * (n - 1) * n * delta := by
  classical
  by_cases hn : n = 0
  · simp [hn, hlu, mul_nonneg]
  let mu := stationaryLatentArmStreamCanonicalTrajectoryMeasure
    prior rewardKernel algorithm
  let action := environmentTrajectoryAction
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let reward := environmentTrajectoryReward
    (Env := Env × UCB.ArmRewardStream K) (Action := Fin K) (Reward := Real)
  let environment := fun sample :
      (Env × UCB.ArmRewardStream K) × ((n : Nat) -> Fin K × Real) =>
    sample.1.1
  let bad := fun arm : Fin K => fun t : Nat =>
    {sample |
      0 < pullCount (action sample) arm t ∧
      mean (environment sample) arm <=
        UCB.realEmpiricalMean (action sample) (reward sample) arm t -
          Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) /
              (pullCount (action sample) arm t : Real))}
  let F := ⋃ arm : Fin K, ⋃ t ∈ Finset.range n, bad arm t
  let C := (u - l) * K +
    4 * Real.sqrt
      (2 * (sigma2 : Real) * Real.log (1 / delta) * K * n)
  have haction : forall t, Measurable (fun sample => action sample t) :=
    measurable_environmentTrajectoryAction_apply
  have hreward : forall t, Measurable (fun sample => reward sample t) :=
    measurable_environmentTrajectoryReward_apply
  have henvironment : Measurable environment :=
    measurable_fst.comp measurable_fst
  have hbad : forall arm t, MeasurableSet (bad arm t) := by
    intro arm t
    have hpull : Measurable (fun sample => pullCount (action sample) arm t) :=
      measurable_pullCount action haction arm t
    have hemp : Measurable (fun sample =>
        UCB.realEmpiricalMean (action sample) (reward sample) arm t) :=
      UCB.measurable_realEmpiricalMean action reward haction hreward arm t
    have hwidth : Measurable (fun sample =>
        Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) /
            (pullCount (action sample) arm t : Real))) :=
      (measurable_const.div
        ((measurable_of_countable fun k : Nat => (k : Real)).comp hpull)).sqrt
    have hmean : Measurable (fun sample => mean (environment sample) arm) :=
      hmeas_mean.comp (henvironment.prodMk measurable_const)
    exact (measurableSet_lt measurable_const hpull).inter
      (measurableSet_le hmean (hemp.sub hwidth))
  have hF : MeasurableSet F :=
    MeasurableSet.iUnion fun arm =>
      (Finset.range n).measurableSet_biUnion fun t _ht => hbad arm t
  have hmeanLift : Measurable (fun input :
      (Env × UCB.ArmRewardStream K) × Fin K => mean input.1.1 input.2) :=
    hmeas_mean.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmeanAction : forall t, Integrable (fun sample =>
      mean (environment sample) (action sample t)) mu := by
    intro t
    simpa [mu, environment, action] using
      integrable_trajectoryMean_action mu
        (fun envStream arm => mean envStream.1 arm) hmeanLift
        (fun envStream arm => hmeanMem envStream.1 arm) t
  have hscoreAction : forall t, Integrable (fun sample =>
      clippedUCB l u (sigma2 : Real) delta
        (action sample) (reward sample) (action sample t) t) mu := by
    intro t
    simpa [action, reward, trajectoryHistoryScore,
      clippedUCBHistoryScore_atTrace] using
      integrable_trajectoryHistoryScore_clippedUCB
        mu l u (sigma2 : Real) delta hlu t
  have hsum : Integrable (fun sample =>
      ∑ t ∈ Finset.range n,
        (clippedUCB l u (sigma2 : Real) delta
            (action sample) (reward sample) (action sample t) t -
          mean (environment sample) (action sample t))) mu := by
    exact IntegrabilitySums.integrable_finset_sum mu (Finset.range n)
      (fun t sample =>
        clippedUCB l u (sigma2 : Real) delta
            (action sample) (reward sample) (action sample t) t -
          mean (environment sample) (action sample t))
      (fun t _ht => (hscoreAction t).sub (hmeanAction t))
  have hprob : mu F <=
      (K : ENNReal) * ((n - 1 : Nat) : ENNReal) * ENNReal.ofReal delta := by
    have heq : F = {sample | ∃ arm : Fin K, ∃ t < n,
        0 < pullCount (action sample) arm t ∧
        mean (environment sample) arm <=
          UCB.realEmpiricalMean (action sample) (reward sample) arm t -
            Real.sqrt
              (2 * (sigma2 : Real) * Real.log (1 / delta) /
                (pullCount (action sample) arm t : Real))} := by
      ext sample
      simp [F, bad, and_left_comm]
    rw [heq]
    simpa [mu, action, reward, environment] using
      stationaryLatentArmStreamCanonicalTrajectoryMeasure_exists_arm_exists_mean_le_realEmpiricalMean_sub_width_le
        prior rewardKernel algorithm mean hmeas_mean sigma2 hsubG hsigma2
          delta hdelta hdelta_one n
  have hprobReal : mu.real F <= (K : Nat) * (n - 1 : Nat) * delta := by
    change (mu F).toReal <= _
    calc
      (mu F).toReal <=
          ((K : ENNReal) * ((n - 1 : Nat) : ENNReal) *
            ENNReal.ofReal delta).toReal :=
        ENNReal.toReal_mono (by finiteness) hprob
      _ = (K : Nat) * (n - 1 : Nat) * delta := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_natCast, ENNReal.toReal_natCast,
          ENNReal.toReal_ofReal hdelta.le]
  have hC : 0 <= C := by
    dsimp [C]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hlu) (Nat.cast_nonneg K))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  change integral mu (fun sample =>
      ∑ t ∈ Finset.range n,
        (clippedUCB l u (sigma2 : Real) delta
            (action sample) (reward sample) (action sample t) t -
          mean (environment sample) (action sample t))) <= _
  calc
    _ <= (∫ sample in F, ∑ _t ∈ Finset.range n, (u - l) ∂mu) +
        ∫ sample in Fᶜ, C ∂mu := by
      rw [← integral_add_compl hF hsum]
      apply add_le_add
      · apply setIntegral_mono_on hsum.integrableOn
          (integrable_const (c := (Finset.range n).sum fun _ => u - l)).integrableOn hF
        intro sample _hsample
        apply Finset.sum_le_sum
        intro t _ht
        have hscore := clippedUCB_mem_Icc
          l u (sigma2 : Real) delta hlu
          (action sample) (reward sample) (action sample t) t
        have hmean := hmeanMem (environment sample) (action sample t)
        nlinarith [hscore.2, hmean.1]
      · apply setIntegral_mono_on hsum.integrableOn
          (integrable_const (c := C)).integrableOn hF.compl
        intro sample hsample
        apply sum_clippedUCB_action_sub_mean_le
          (action sample) (reward sample)
          (mean (environment sample)) l u (sigma2 : Real) delta
          (hmeanMem (environment sample)) hlu
        intro t ht hcount
        have hnot : ¬ mean (environment sample) (action sample t) <=
            UCB.realEmpiricalMean
                (action sample) (reward sample) (action sample t) t -
              Real.sqrt
                (2 * (sigma2 : Real) * Real.log (1 / delta) /
                  (pullCount (action sample) (action sample t) t : Real)) := by
          intro hindex
          apply hsample
          exact Set.mem_iUnion.2 ⟨action sample t,
              Set.mem_iUnion.2 ⟨t,
              Set.mem_iUnion.2 ⟨Finset.mem_range.mpr ht,
                ⟨Nat.pos_of_ne_zero hcount, hindex⟩⟩⟩⟩
        exact lt_of_not_ge (fun hwidth => hnot (by linarith))
    _ = mu.real F * (n * (u - l)) + mu.real Fᶜ * C := by
      simp_rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        setIntegral_const, smul_eq_mul]
    _ <= ((K : Nat) * (n - 1 : Nat) * delta) * (n * (u - l)) +
        1 * C := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hprobReal
          (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hlu))
      · exact mul_le_mul_of_nonneg_right measureReal_le_one hC
    _ = (u - l) * K +
          4 * Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) * K * n) +
          (u - l) * K * (n - 1) * n * delta := by
      dsimp [C]
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn)]
      ring

set_option linter.unusedVariables false in
/--
Stationary-reward Thompson Bayesian regret with an explicit confidence
parameter.  This is the decomposition-facing join of the two pinned-LML
clipped-UCB expectation bounds.  The analytic upper bound is in fact
comparator-uniform, but the public Bayesian-regret endpoint deliberately
retains `IsOptimalMeanSelector mean bestAction` as an interpretation contract.
-/
theorem stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le_of_delta
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [Nonempty Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (bestAction : Env -> Fin K) (hbestAction : Measurable bestAction)
    (mean : Env -> Fin K -> Real)
    (hbest : IsOptimalMeanSelector mean bestAction)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (l u : Real) (hlu : l <= u)
    (hmeanMem : forall env arm, mean env arm ∈ Set.Icc l u)
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    let augmentedPrior := stationaryLatentArmStreamPrior prior rewardKernel
    let feedbackEnvironment :=
      latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K)
    let augmentedBestAction := fun envStream : Env × UCB.ArmRewardStream K =>
      bestAction envStream.1
    let augmentedMean := fun envStream : Env × UCB.ArmRewardStream K =>
      fun arm => mean envStream.1 arm
    let algorithm := uniformReferenceThompsonAlgorithm
      augmentedPrior feedbackEnvironment augmentedBestAction
        (hbestAction.comp measurable_fst)
    integral
        (stationaryLatentArmStreamCanonicalTrajectoryMeasure
          prior rewardKernel algorithm)
        (fun sample =>
          trajectoryBayesMeanRegret
            augmentedMean augmentedBestAction sample n) <=
      (u - l) * K +
        4 * Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) * K * n) +
        (u - l) * (K + 1) * (n - 1) * n * delta := by
  classical
  dsimp only
  let augmentedPrior := stationaryLatentArmStreamPrior prior rewardKernel
  let feedbackEnvironment :=
    latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K)
  let augmentedBestAction := fun envStream : Env × UCB.ArmRewardStream K =>
    bestAction envStream.1
  let augmentedMean := fun envStream : Env × UCB.ArmRewardStream K =>
    fun arm => mean envStream.1 arm
  let haugmentedMean : Measurable
      (fun input : (Env × UCB.ArmRewardStream K) × Fin K =>
        augmentedMean input.1 input.2) :=
    hmeas_mean.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  let algorithm := uniformReferenceThompsonAlgorithm
    augmentedPrior feedbackEnvironment augmentedBestAction
      (hbestAction.comp measurable_fst)
  have hdecomp := integral_trajectoryBayesMeanRegret_eq_add_clippedUCB
    augmentedPrior feedbackEnvironment augmentedBestAction
      (hbestAction.comp measurable_fst) augmentedMean haugmentedMean
      l u (sigma2 : Real) delta hlu
      (fun envStream arm => hmeanMem envStream.1 arm) n
  dsimp only at hdecomp
  have hdecompCanonical :
      integral
          (stationaryLatentArmStreamCanonicalTrajectoryMeasure
            prior rewardKernel algorithm)
          (fun sample =>
            trajectoryBayesMeanRegret augmentedMean augmentedBestAction sample n) =
        integral
            (stationaryLatentArmStreamCanonicalTrajectoryMeasure
              prior rewardKernel algorithm)
            (fun sample =>
              ∑ t ∈ Finset.range n,
                (augmentedMean sample.1 (augmentedBestAction sample.1) -
                  clippedUCB l u (sigma2 : Real) delta
                    (environmentTrajectoryAction sample)
                    (environmentTrajectoryReward sample)
                    (augmentedBestAction sample.1) t)) +
          integral
            (stationaryLatentArmStreamCanonicalTrajectoryMeasure
              prior rewardKernel algorithm)
            (fun sample =>
              ∑ t ∈ Finset.range n,
                (clippedUCB l u (sigma2 : Real) delta
                    (environmentTrajectoryAction sample)
                    (environmentTrajectoryReward sample)
                    (environmentTrajectoryAction sample t) t -
                  augmentedMean sample.1
                    (environmentTrajectoryAction sample t))) := by
    simpa only [stationaryLatentArmStreamCanonicalTrajectoryMeasure,
      augmentedPrior, feedbackEnvironment, algorithm] using hdecomp
  rw [hdecompCanonical]
  calc
    _ <= (u - l) * (n - 1) * n * delta +
        ((u - l) * K +
          4 * Real.sqrt
            (2 * (sigma2 : Real) * Real.log (1 / delta) * K * n) +
          (u - l) * K * (n - 1) * n * delta) := by
      apply add_le_add
      · simpa [augmentedPrior, feedbackEnvironment, augmentedBestAction,
          augmentedMean, algorithm,
          stationaryLatentArmStreamCanonicalTrajectoryMeasure] using
          stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_sum_mean_bestAction_sub_clippedUCB_le
            prior rewardKernel algorithm bestAction hbestAction mean hmeas_mean
              l u hlu hmeanMem sigma2 hsubG hsigma2
              delta hdelta hdelta_one n
      · simpa [augmentedPrior, feedbackEnvironment, augmentedBestAction,
          augmentedMean, algorithm,
          stationaryLatentArmStreamCanonicalTrajectoryMeasure] using
          stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_sum_clippedUCB_action_sub_mean_le
            prior rewardKernel algorithm mean hmeas_mean l u hlu hmeanMem
              sigma2 hsubG hsigma2 delta hdelta hdelta_one n
    _ = (u - l) * K +
        4 * Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) * K * n) +
        (u - l) * (K + 1) * (n - 1) * n * delta := by ring

/--
Pinned-LML stationary-reward Thompson Bayesian-regret bound, obtained from
the explicit-confidence theorem with `delta = 1 / n ^ 2`.  Unlike the
comparator-relative decomposition, this endpoint explicitly requires the
selector to maximize the declared mean surface pointwise.
-/
theorem stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [Nonempty Env] [NeZero K]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (rewardKernel : Kernel (Env × Fin K) Real)
    [IsMarkovKernel rewardKernel]
    (bestAction : Env -> Fin K) (hbestAction : Measurable bestAction)
    (mean : Env -> Fin K -> Real)
    (hbest : IsOptimalMeanSelector mean bestAction)
    (hmeas_mean : Measurable (fun input : Env × Fin K =>
      mean input.1 input.2))
    (l u : Real) (hlu : l <= u)
    (hmeanMem : forall env arm, mean env arm ∈ Set.Icc l u)
    (sigma2 : NNReal)
    (hsubG : forall env arm,
      HasSubgaussianMGF
        (fun reward => reward - mean env arm) sigma2
        (rewardKernel (env, arm)))
    (hsigma2 : sigma2 ≠ 0)
    (n : Nat) :
    let augmentedPrior := stationaryLatentArmStreamPrior prior rewardKernel
    let feedbackEnvironment :=
      latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K)
    let augmentedBestAction := fun envStream : Env × UCB.ArmRewardStream K =>
      bestAction envStream.1
    let augmentedMean := fun envStream : Env × UCB.ArmRewardStream K =>
      fun arm => mean envStream.1 arm
    let algorithm := uniformReferenceThompsonAlgorithm
      augmentedPrior feedbackEnvironment augmentedBestAction
        (hbestAction.comp measurable_fst)
    integral
        (stationaryLatentArmStreamCanonicalTrajectoryMeasure
          prior rewardKernel algorithm)
        (fun sample =>
          trajectoryBayesMeanRegret
            augmentedMean augmentedBestAction sample n) <=
      (2 * K + 1) * (u - l) +
        8 * Real.sqrt
          ((sigma2 : Real) * K * n * Real.log n) := by
  classical
  dsimp only
  by_cases hn : n = 0
  · simp [hn, trajectoryBayesMeanRegret]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hlu)
  let delta : Real := 1 / (n : Real) ^ 2
  have hnReal : 0 < (n : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_one : delta <= 1 := by
    dsimp [delta]
    rw [div_le_one (sq_pos_of_pos hnReal)]
    nlinarith [show (1 : Real) <= n by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn]
  let augmentedPrior := stationaryLatentArmStreamPrior prior rewardKernel
  let feedbackEnvironment :=
    latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K)
  let augmentedBestAction := fun envStream : Env × UCB.ArmRewardStream K =>
    bestAction envStream.1
  let augmentedMean := fun envStream : Env × UCB.ArmRewardStream K =>
    fun arm => mean envStream.1 arm
  let algorithm := uniformReferenceThompsonAlgorithm
    augmentedPrior feedbackEnvironment augmentedBestAction
      (hbestAction.comp measurable_fst)
  have hgeneral :=
    stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le_of_delta
      prior rewardKernel bestAction hbestAction mean hbest hmeas_mean
        l u hlu hmeanMem sigma2 hsubG hsigma2
        delta hdelta hdelta_one n
  dsimp only at hgeneral
  change integral
      (stationaryLatentArmStreamCanonicalTrajectoryMeasure
        prior rewardKernel algorithm)
      (fun sample =>
        trajectoryBayesMeanRegret augmentedMean augmentedBestAction sample n) <= _
  calc
    _ <= (u - l) * K +
        4 * Real.sqrt
          (2 * (sigma2 : Real) * Real.log (1 / delta) * K * n) +
        (u - l) * (K + 1) * (n - 1) * n * delta := by
      simpa [augmentedPrior, feedbackEnvironment, augmentedBestAction,
        augmentedMean, algorithm] using hgeneral
    _ = K * (u - l) + (K + 1) * (u - l) * ((n - 1) / n) +
        4 * Real.sqrt
          ((2 : Real) ^ 2 *
            ((sigma2 : Real) * K * n * Real.log n)) := by
      dsimp [delta]
      field_simp
      rw [Real.log_pow]
      ring_nf
    _ = K * (u - l) + (K + 1) * (u - l) * ((n - 1) / n) +
        8 * Real.sqrt
          ((sigma2 : Real) * K * n * Real.log n) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      ring
    _ <= K * (u - l) + (K + 1) * (u - l) * 1 +
        8 * Real.sqrt
          ((sigma2 : Real) * K * n * Real.log n) := by
      have hwidth : 0 <= u - l := sub_nonneg.mpr hlu
      gcongr
      rw [div_le_one hnReal]
      linarith
    _ = (2 * K + 1) * (u - l) +
        8 * Real.sqrt
          ((sigma2 : Real) * K * n * Real.log n) := by ring

end Thompson
end BanditRLProof
