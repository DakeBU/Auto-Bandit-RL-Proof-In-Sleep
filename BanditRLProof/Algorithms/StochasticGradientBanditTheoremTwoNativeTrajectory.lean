import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoLatentReward
import BanditRLProof.Algorithms.ThompsonRecursiveSampler
import BanditRLProof.Algorithms.ThompsonReferencePolicy
import BanditRLProof.KernelIndependentExtension
import BanditRLProof.KernelTrajectoryPrefix

/-!
# Two-arm SGB Theorem 2: deferred-decisions trajectory prefix

The latent arm-stream coupling samples every reward coordinate before the
algorithm runs.  The native fixed-IID process samples only the reward selected
at each round.  Connecting those constructions requires a deferred-decisions
argument, not merely equality of one-coordinate marginals.

This module proves the first process-level half of that adapter.  A visible
trajectory prefix through `n` depends only on latent reward coordinates with
pull index at most `n`.  It packages that dependence as a Markov prefix kernel
and gives the exact finite stream-box/visible-prefix mixture law.  It also
separates the compiled next-action factorization and pathwise selected-coordinate
readout from the missing freshness argument, and types the exact branch-locality
contract together with its finite-kernel consumer and count-cap bookkeeping.
The remaining producer is a count-capped restricted-measure induction proving
that locality.  Branchwise freshness, native-prefix identification, and
trajectory uniqueness remain downstream.  Consequently, no full native
trajectory-law equality, stopped-reward IID statement, or Theorem-2 terminal is
claimed here.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
noncomputable section
universe u

namespace UCB

/-- Restricting the latent arm stream through time `n` gives the exact finite
product of the per-round arm-vector laws. -/
theorem armStreamMeasure_map_frestrictLe_eq_pi
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Measure.map (Preorder.frestrictLe n) (armStreamMeasure nu) =
      Measure.pi (fun _ : Finset.Iic n =>
        Measure.infinitePi fun arm : Fin K => nu arm) := by
  simpa only [armStreamMeasure, Preorder.frestrictLe] using
    (Measure.infinitePi_map_restrict
      (μ := fun _ : Nat => Measure.infinitePi fun arm : Fin K => nu arm)
      (I := Finset.Iic n))

/-- Extend a finite arm-stream box by zero rows after its endpoint. -/
def extendArmStreamFinitePrefix {K : Nat} (n : Nat)
    (streamBox : (i : Finset.Iic n) -> Fin K -> Real) : ArmRewardStream K :=
  fun t => if h : t <= n then
    streamBox ⟨t, Finset.mem_Iic.mpr h⟩ else fun _arm => 0

theorem measurable_extendArmStreamFinitePrefix
    {K : Nat} (n : Nat) :
    Measurable (extendArmStreamFinitePrefix (K := K) n) := by
  exact measurable_pi_lambda _ (fun t => by
    by_cases ht : t <= n
    · simpa [extendArmStreamFinitePrefix, ht] using
        (measurable_pi_apply
          (⟨t, Finset.mem_Iic.mpr ht⟩ : Finset.Iic n))
    · simp [extendArmStreamFinitePrefix, ht])

@[simp]
theorem extendArmStreamFinitePrefix_apply_of_le
    {K : Nat} (n t : Nat) (ht : t <= n)
    (streamBox : (i : Finset.Iic n) -> Fin K -> Real) :
    extendArmStreamFinitePrefix n streamBox t =
      streamBox ⟨t, Finset.mem_Iic.mpr ht⟩ := by
  simp [extendArmStreamFinitePrefix, ht]

/-- A finite kernel driven only by the complement of one arm-stream
coordinate leaves that coordinate's prescribed marginal independent of the
kernel output.  The output kernel may be sub-Markov, as needed after branch
restriction. -/
theorem armStreamMeasure_map_output_coordinate_compProd_comap_without_eq_prod
    {K : Nat} {Output : Type*} [MeasurableSpace Output]
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (target : Nat × Fin K)
    (kernel : Kernel
      ({index : Nat × Fin K // index ≠ target} -> Real) Output)
    [IsFiniteKernel kernel] :
    Measure.map
        (fun sample : ArmRewardStream K × Output =>
          (sample.2, armStreamCoordinate target sample.1))
        (armStreamMeasure nu ⊗ₘ
          kernel.comap (armStreamWithoutCoordinate target)
            (measurable_armStreamWithoutCoordinate target)) =
      (Measure.map Prod.snd
          (armStreamMeasure nu ⊗ₘ
            kernel.comap (armStreamWithoutCoordinate target)
              (measurable_armStreamWithoutCoordinate target))).prod
        (nu target.2) := by
  have hfactor :=
    map_snd_x_compProd_comap_eq_prod_map_of_indepFun
      (armStreamMeasure nu)
      (armStreamCoordinate target) (measurable_armStreamCoordinate target)
      (armStreamWithoutCoordinate target)
        (measurable_armStreamWithoutCoordinate target)
      kernel (indepFun_armStreamMeasure_coordinate_without nu target)
  have hcoordinate :
      Measure.map (armStreamCoordinate target) (armStreamMeasure nu) =
        nu target.2 := by
    simpa [armStreamCoordinate] using
      armStreamMeasure_map_coord nu target.1 target.2
  rw [hcoordinate] at hfactor
  exact hfactor

end UCB

namespace Thompson

/-- Two latent streams agreeing through `n` generate the same visible
trajectory law through `n`.  Action randomization remains inside the canonical
trajectory kernel; the argument changes only deterministic reward fibers. -/
theorem latentArmStreamTrajectoryKernel_map_frestrictLe_eq_of_streamPrefix_eq
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (stream₁ stream₂ : UCB.ArmRewardStream K) (n : Nat)
    (hstream : Preorder.frestrictLe n stream₁ =
      Preorder.frestrictLe n stream₂) :
    (latentArmStreamTrajectoryKernel algorithm env stream₁).map
        (Preorder.frestrictLe n) =
      (latentArmStreamTrajectoryKernel algorithm env stream₂).map
        (Preorder.frestrictLe n) := by
  let environment := latentArmStreamMeasurableHistoryEnvironment
    (Env := Env) (K := K)
  change
    (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
        (env, stream₁)).map (Preorder.frestrictLe n) =
      (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
        (env, stream₂)).map (Preorder.frestrictLe n)
  rw [canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical,
    canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical]
  apply KernelTrajectoryPrefix.trajMeasure_map_frestrictLe_congr
  · have hzero : stream₁ 0 = stream₂ 0 := by
      have h := congrFun hstream
        (⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ : Finset.Iic n)
      simpa [Preorder.frestrictLe_apply] using h
    have hinitial :
        (environment.at (env, stream₁)).initialFeedback =
          (environment.at (env, stream₂)).initialFeedback := by
      ext arm event hevent
      rw [latentArmStreamMeasurableHistoryEnvironment_at_initialFeedback_apply,
        latentArmStreamMeasurableHistoryEnvironment_at_initialFeedback_apply,
        hzero]
    rw [hinitial]
  · intro k hk
    have hfeedback :
        (environment.at (env, stream₁)).feedback k =
          (environment.at (env, stream₂)).feedback k := by
      ext input event hevent
      let count := ETC.realHistoryPullCount k input.1 input.2
      have hcount_le : count <= k + 1 := by
        unfold count ETC.realHistoryPullCount
        calc
          (Finset.univ.sum fun i : Finset.Iic k =>
              if (input.1 i).1 = input.2 then 1 else 0) <=
              Finset.univ.sum (fun _i : Finset.Iic k => 1) := by
                apply Finset.sum_le_sum
                intro i _hi
                split <;> simp
          _ = k + 1 := by simp
      have hcount_n : count <= n :=
        hcount_le.trans (Nat.succ_le_iff.mpr hk)
      have hrow := congrFun hstream
        (⟨count, Finset.mem_Iic.mpr hcount_n⟩ : Finset.Iic n)
      have hreward := congrFun hrow input.2
      have hreward' : stream₁ count input.2 = stream₂ count input.2 := by
        simpa [Preorder.frestrictLe_apply] using hreward
      rw [latentArmStreamMeasurableHistoryEnvironment_at_feedback_apply,
        latentArmStreamMeasurableHistoryEnvironment_at_feedback_apply]
      change (Measure.dirac (stream₁ count input.2)) event =
        (Measure.dirac (stream₂ count input.2)) event
      rw [hreward']
    unfold historyStepKernel
    rw [hfeedback]

/-- Finite visible-prefix kernel after replacing the infinite reward stream by
its zero-extended finite box. -/
noncomputable def latentArmStreamVisiblePrefixKernel
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) (n : Nat) :
    Kernel ((i : Finset.Iic n) -> Fin K -> Real)
      (History.FinitePairHistory (Fin K) Real n) :=
  ((latentArmStreamTrajectoryKernel algorithm env).comap
      (UCB.extendArmStreamFinitePrefix n)
      (UCB.measurable_extendArmStreamFinitePrefix n)).map
    (Preorder.frestrictLe n)

instance instLatentArmStreamVisiblePrefixKernelIsMarkov
    {Env : Type u} {K : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) (n : Nat) :
    IsMarkovKernel (latentArmStreamVisiblePrefixKernel algorithm env n) := by
  unfold latentArmStreamVisiblePrefixKernel
  letI : IsMarkovKernel
      ((latentArmStreamTrajectoryKernel algorithm env).comap
        (UCB.extendArmStreamFinitePrefix n)
        (UCB.measurable_extendArmStreamFinitePrefix n)) := by
    infer_instance
  exact Kernel.IsMarkovKernel.map _ (Preorder.measurable_frestrictLe n)

/-- The latent visible-prefix kernel factors exactly through the finite stream
box through the same endpoint. -/
theorem latentArmStreamTrajectoryKernel_map_frestrictLe_eq_prefixKernel_comap
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) (n : Nat) :
    (latentArmStreamTrajectoryKernel algorithm env).map
        (Preorder.frestrictLe n) =
      (latentArmStreamVisiblePrefixKernel algorithm env n).comap
        (Preorder.frestrictLe n) (Preorder.measurable_frestrictLe n) := by
  apply Kernel.ext
  intro stream
  rw [Kernel.map_apply _ (Preorder.measurable_frestrictLe n),
    Kernel.comap_apply]
  unfold latentArmStreamVisiblePrefixKernel
  rw [Kernel.map_apply _ (Preorder.measurable_frestrictLe n),
    Kernel.comap_apply]
  have hprefix : Preorder.frestrictLe n stream =
      Preorder.frestrictLe n
        (UCB.extendArmStreamFinitePrefix n
          (Preorder.frestrictLe n stream)) := by
    funext i
    simp [Preorder.frestrictLe_apply,
      UCB.extendArmStreamFinitePrefix_apply_of_le n i.1
        (Finset.mem_Iic.mp i.2)]
  exact latentArmStreamTrajectoryKernel_map_frestrictLe_eq_of_streamPrefix_eq
    algorithm env stream
      (UCB.extendArmStreamFinitePrefix n
        (Preorder.frestrictLe n stream)) n hprefix

/-- Visible history through `n` paired with the action selected at `n + 1`. -/
def latentArmStreamVisiblePrefixNextAction
    {K : Nat} (n : Nat) :
    ((t : Nat) -> Fin K × Real) ->
      History.FinitePairHistory (Fin K) Real n × Fin K :=
  fun trajectory =>
    (Preorder.frestrictLe n trajectory, (trajectory (n + 1)).1)

theorem measurable_latentArmStreamVisiblePrefixNextAction
    {K : Nat} (n : Nat) :
    Measurable (latentArmStreamVisiblePrefixNextAction (K := K) n) := by
  exact (Preorder.measurable_frestrictLe n).prodMk
    (measurable_fst.comp (measurable_pi_apply (n + 1)))

/-- Reward observed at the shifted successor time `n + 1`. -/
def latentArmStreamVisibleNextReward
    {K : Nat} (n : Nat) :
    ((t : Nat) -> Fin K × Real) -> Real :=
  fun trajectory => (trajectory (n + 1)).2

theorem measurable_latentArmStreamVisibleNextReward
    {K : Nat} (n : Nat) :
    Measurable (latentArmStreamVisibleNextReward (K := K) n) := by
  exact measurable_snd.comp (measurable_pi_apply (n + 1))

/-- Canonical candidate for the condition kernel on one next-coordinate
branch, reconstructed after fixing the omitted coordinate to zero. -/
noncomputable def latentArmStreamVisiblePrefixNextActionBranchKernel
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (n : Nat) (target : Nat × Fin K) :
    Kernel ({index : Nat × Fin K // index ≠ target} -> Real)
      (History.FinitePairHistory (Fin K) Real n × Fin K) :=
  ((((latentArmStreamTrajectoryKernel algorithm env).map
      (latentArmStreamVisiblePrefixNextAction n)).comap
        (UCB.armStreamInsertCoordinate target 0)
        (UCB.measurable_armStreamInsertCoordinate target 0)).restrict
    (UCB.measurableSet_armStreamHistoryActionCoordinateBranch n target))

instance instLatentArmStreamVisiblePrefixNextActionBranchKernelIsFinite
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (n : Nat) (target : Nat × Fin K) :
    IsFiniteKernel
      (latentArmStreamVisiblePrefixNextActionBranchKernel
        algorithm env n target) := by
  unfold latentArmStreamVisiblePrefixNextActionBranchKernel
  infer_instance

/-- Histories through `n` that have not consumed the designated latent
coordinate.  The inclusive history count can equal the coordinate index: that
coordinate is used only by the next reward from the same arm. -/
def latentArmStreamPrefixCountCap
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    Set (History.FinitePairHistory (Fin K) Real n) :=
  {history |
    ETC.realHistoryPullCount n history target.2 <= target.1}

theorem measurableSet_latentArmStreamPrefixCountCap
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    MeasurableSet (latentArmStreamPrefixCountCap n target) := by
  exact measurableSet_le
    (UCB.measurable_realHistoryPullCount n target.2) measurable_const

/-- Extending an inclusive finite pair history increments exactly the count of
the arm selected by the appended pair. -/
@[simp]
theorem realHistoryPullCount_extendPairHistorySucc
    {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (next : Fin K × Real) (arm : Fin K) :
    ETC.realHistoryPullCount (n + 1)
        (History.extendPairHistorySucc history next) arm =
      ETC.realHistoryPullCount n history arm +
        if next.1 = arm then 1 else 0 := by
  classical
  let action : ActionTrace (Fin K) := fun t =>
    if h : t <= n then
      history ⟨t, Finset.mem_Iic.mpr h⟩ |>.1
    else next.1
  let reward : RewardTrace Real := fun t =>
    if h : t <= n then
      history ⟨t, Finset.mem_Iic.mpr h⟩ |>.2
    else next.2
  have hprefix :
      History.finitePairHistoryOfTrace action reward n = history := by
    funext i
    simp [action, reward, Finset.mem_Iic.mp i.2]
  have hsucc :
      History.finitePairHistoryOfTrace action reward (n + 1) =
        History.extendPairHistorySucc history next := by
    rw [History.finitePairHistoryOfTrace_succ, hprefix]
    congr 1
    simp [action, reward]
  calc
    ETC.realHistoryPullCount (n + 1)
        (History.extendPairHistorySucc history next) arm =
      ETC.realHistoryPullCount (n + 1)
        (History.finitePairHistoryOfTrace action reward (n + 1)) arm := by
          rw [hsucc]
    _ = pullCount action arm ((n + 1) + 1) :=
      ETC.realHistoryPullCount_finitePairHistoryOfTrace
        action reward (n + 1) arm
    _ = pullCount action arm (n + 1) +
        if action (n + 1) = arm then 1 else 0 := by
          rw [pullCount_succ]
    _ = ETC.realHistoryPullCount n history arm +
        if next.1 = arm then 1 else 0 := by
          rw [← ETC.realHistoryPullCount_finitePairHistoryOfTrace
            action reward n arm, hprefix]
          simp [action]

/-- Exact remaining producer contract for branchwise prefix/action locality.
It is intentionally a proposition, not an instance or a proved theorem: the
current module supplies its finite-kernel consumer below while leaving this
count-capped trajectory induction explicit. -/
def LatentArmStreamVisiblePrefixNextActionBranchLocality
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (n : Nat) : Prop :=
  ∀ target : Nat × Fin K,
    (((latentArmStreamTrajectoryKernel algorithm env).map
        (latentArmStreamVisiblePrefixNextAction n)).restrict
      (UCB.measurableSet_armStreamHistoryActionCoordinateBranch n target)) =
    (latentArmStreamVisiblePrefixNextActionBranchKernel
        algorithm env n target).comap
      (UCB.armStreamWithoutCoordinate target)
      (UCB.measurable_armStreamWithoutCoordinate target)

/-- Once the branch-locality producer is available, coordinate independence
immediately yields the exact branchwise condition/selected-coordinate product
law.  This consumer is valid for the sub-Markov branch kernel and therefore
does not misstate branch restriction as ordinary probability independence. -/
theorem latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod_of_locality
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (n : Nat)
    (hlocal : LatentArmStreamVisiblePrefixNextActionBranchLocality
      algorithm env n)
    (target : Nat × Fin K) :
    let branchKernel :=
      ((latentArmStreamTrajectoryKernel algorithm env).map
        (latentArmStreamVisiblePrefixNextAction n)).restrict
          (UCB.measurableSet_armStreamHistoryActionCoordinateBranch n target)
    Measure.map
        (fun sample : UCB.ArmRewardStream K ×
            (History.FinitePairHistory (Fin K) Real n × Fin K) =>
          (sample.2, UCB.armStreamCoordinate target sample.1))
        (UCB.armStreamMeasure nu ⊗ₘ branchKernel) =
      (Measure.map Prod.snd
          (UCB.armStreamMeasure nu ⊗ₘ branchKernel)).prod
        (nu target.2) := by
  dsimp only
  rw [hlocal target]
  exact
    UCB.armStreamMeasure_map_output_coordinate_compProd_comap_without_eq_prod
      nu target
        (latentArmStreamVisiblePrefixNextActionBranchKernel
          algorithm env n target)

/-- After the latent reward stream is mixed out, the next action still follows
the algorithm's history policy.  This isolates action randomization from the
remaining selected-reward freshness obligation. -/
theorem latentArmStreamTrajectoryMeasure_map_visiblePrefix_nextAction_eq_compProd
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Measure.map
        (fun sample : UCB.ArmRewardStream K ×
            ((t : Nat) -> Fin K × Real) =>
          latentArmStreamVisiblePrefixNextAction n sample.2)
        (latentArmStreamTrajectoryMeasure algorithm env nu) =
      Measure.map
          (fun sample : UCB.ArmRewardStream K ×
              ((t : Nat) -> Fin K × Real) =>
            Preorder.frestrictLe n sample.2)
          (latentArmStreamTrajectoryMeasure algorithm env nu) ⊗ₘ
        algorithm.policy n := by
  unfold latentArmStreamTrajectoryMeasure
  apply trajectoryMixture_map_history_action_eq_compProd
    (UCB.armStreamMeasure nu)
    (latentArmStreamTrajectoryKernel algorithm env)
    (Preorder.frestrictLe n) (Preorder.measurable_frestrictLe n)
    (fun trajectory => (trajectory (n + 1)).1)
    (measurable_fst.comp (measurable_pi_apply (n + 1)))
    (algorithm.policy n)
  intro stream
  unfold latentArmStreamTrajectoryKernel
  rw [Kernel.comap_apply]
  exact
    canonicalMeasurableEnvironmentTrajectoryKernel_map_history_action_eq_compProd
      algorithm
      (latentArmStreamMeasurableHistoryEnvironment
        (Env := Env) (K := K)) (env, stream) n

/-- On the coupling, the actual successor reward is the latent coordinate
encoded by the visible prefix and the sampled next action.  This is pathwise
support; conditional freshness still requires the branchwise product proof. -/
theorem latentArmStreamVisibleNextReward_eq_selectedCoordinate_ae
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    ∀ᵐ sample ∂latentArmStreamTrajectoryMeasure algorithm env nu,
      latentArmStreamVisibleNextReward n sample.2 =
        UCB.armStreamCoordinate
          (UCB.armStreamCoordinateOfHistoryAction n
            (latentArmStreamVisiblePrefixNextAction n sample.2)) sample.1 := by
  have hreward := latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
    algorithm env nu
  filter_upwards [hreward] with sample hsample
  have htime := congrFun hsample (n + 1)
  let arm := (sample.2 (n + 1)).1
  have hcount := ETC.realHistoryPullCount_finitePairHistoryOfTrace
    (canonicalHistoryTrajectoryAction (Reward := Real) sample.2)
    (canonicalHistoryTrajectoryReward (Action := Fin K) sample.2) n arm
  change ETC.realHistoryPullCount n
      (Preorder.frestrictLe n sample.2) arm =
    pullCount (canonicalHistoryTrajectoryAction sample.2) arm (n + 1) at hcount
  change (sample.2 (n + 1)).2 =
    sample.1
      (pullCount (canonicalHistoryTrajectoryAction sample.2) arm (n + 1)) arm
      at htime
  change (sample.2 (n + 1)).2 =
    sample.1
      (ETC.realHistoryPullCount n (Preorder.frestrictLe n sample.2) arm) arm
  rw [hcount]
  exact htime

/-- Exact finite mixture law for the latent stream box and the visible SGB
trajectory prefix.  This is the deferred-decisions representation that the
remaining native-prefix comparison must consume. -/
theorem latentArmStreamTrajectoryMeasure_map_stream_visiblePrefix_eq
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Measure.map
        (fun sample : UCB.ArmRewardStream K ×
            ((t : Nat) -> Fin K × Real) =>
          (Preorder.frestrictLe n sample.1,
            Preorder.frestrictLe n sample.2))
        (latentArmStreamTrajectoryMeasure algorithm env nu) =
      Measure.pi (fun _ : Finset.Iic n =>
          Measure.infinitePi fun arm : Fin K => nu arm) ⊗ₘ
        latentArmStreamVisiblePrefixKernel algorithm env n := by
  let streamPrefix : UCB.ArmRewardStream K ->
      ((i : Finset.Iic n) -> Fin K -> Real) :=
    Preorder.frestrictLe n
  let visiblePrefix : ((t : Nat) -> Fin K × Real) ->
      History.FinitePairHistory (Fin K) Real n :=
    Preorder.frestrictLe n
  let prefixKernel := latentArmStreamVisiblePrefixKernel algorithm env n
  have hstreamPrefix : Measurable streamPrefix :=
    Preorder.measurable_frestrictLe n
  have hvisiblePrefix : Measurable visiblePrefix :=
    Preorder.measurable_frestrictLe n
  calc
    _ = ((latentArmStreamTrajectoryMeasure algorithm env nu).map
          (fun sample => (sample.1, visiblePrefix sample.2))).map
          (fun sample => (streamPrefix sample.1, sample.2)) := by
        rw [Measure.map_map]
        · rfl
        · exact (hstreamPrefix.comp measurable_fst).prodMk measurable_snd
        · exact measurable_fst.prodMk (hvisiblePrefix.comp measurable_snd)
    _ = (UCB.armStreamMeasure nu ⊗ₘ
          (latentArmStreamTrajectoryKernel algorithm env).map visiblePrefix).map
          (fun sample => (streamPrefix sample.1, sample.2)) := by
        rw [latentArmStreamTrajectoryMeasure]
        congr 1
        simpa only [Prod.map_apply, id_eq] using
          (Measure.compProd_map
            (μ := UCB.armStreamMeasure nu)
            (κ := latentArmStreamTrajectoryKernel algorithm env)
            hvisiblePrefix).symm
    _ = (UCB.armStreamMeasure nu ⊗ₘ
          prefixKernel.comap streamPrefix hstreamPrefix).map
          (fun sample => (streamPrefix sample.1, sample.2)) := by
        rw [latentArmStreamTrajectoryKernel_map_frestrictLe_eq_prefixKernel_comap]
    _ = (UCB.armStreamMeasure nu).map streamPrefix ⊗ₘ prefixKernel := by
        simpa only [streamPrefix, prefixKernel] using
          (map_compProd_comap_history
            (UCB.armStreamMeasure nu) streamPrefix hstreamPrefix prefixKernel)
    _ = Measure.pi (fun _ : Finset.Iic n =>
          Measure.infinitePi fun arm : Fin K => nu arm) ⊗ₘ prefixKernel := by
        rw [UCB.armStreamMeasure_map_frestrictLe_eq_pi]

end Thompson
end
end BanditRLProof
