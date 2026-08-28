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
readout from the missing aggregate freshness argument.  A count-capped
restricted-measure induction proves the exact branch-locality contract and its
unconditional branchwise product law.  Aggregating those branches into a
selected-reward freshness theorem, native-prefix identification, selected-IID
laws, future/no-return control, and trajectory uniqueness remain downstream.
Consequently, no full native trajectory-law equality, stopped-reward IID
statement, or Theorem-2 terminal is claimed here.
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

/-- Fixed-stream finite-prefix/next-pair recursion for the latent arm-stream
trajectory.  This is the trajectory-level recurrence used by the count-capped
locality induction below. -/
theorem latentArmStreamTrajectoryKernel_map_prefix_next_eq_compProd
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (stream : UCB.ArmRewardStream K) (n : Nat) :
    (latentArmStreamTrajectoryKernel algorithm env stream).map
        (fun trajectory =>
          (Preorder.frestrictLe n trajectory, trajectory (n + 1))) =
      (latentArmStreamTrajectoryKernel algorithm env stream).map
          (Preorder.frestrictLe n) ⊗ₘ
        historyStepKernel algorithm
          ((latentArmStreamMeasurableHistoryEnvironment
            (Env := Env) (K := K)).at (env, stream)) n := by
  unfold latentArmStreamTrajectoryKernel
  rw [Kernel.comap_apply]
  exact
    canonicalMeasurableEnvironmentTrajectoryKernel_map_prefix_next_eq_compProd
      algorithm
      (latentArmStreamMeasurableHistoryEnvironment (Env := Env) (K := K))
      (env, stream) n

/-- If two latent reward streams agree away from one coordinate, then their
feedback laws agree at every history/action pair whose next-unused coordinate
is not the omitted one. -/
theorem latentArmStreamFeedback_eq_of_withoutCoordinate_eq_of_selectedCoordinate_ne
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (env : Env) (target : Nat × Fin K)
    (stream₁ stream₂ : UCB.ArmRewardStream K) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K)
    (hwithout : UCB.armStreamWithoutCoordinate target stream₁ =
      UCB.armStreamWithoutCoordinate target stream₂)
    (hne : (ETC.realHistoryPullCount n history arm, arm) ≠ target) :
    ((latentArmStreamMeasurableHistoryEnvironment
        (Env := Env) (K := K)).at (env, stream₁)).feedback n (history, arm) =
      ((latentArmStreamMeasurableHistoryEnvironment
        (Env := Env) (K := K)).at (env, stream₂)).feedback n (history, arm) := by
  rw [latentArmStreamMeasurableHistoryEnvironment_at_feedback_apply,
    latentArmStreamMeasurableHistoryEnvironment_at_feedback_apply]
  have hcoordinate := congrFun hwithout
    (⟨(ETC.realHistoryPullCount n history arm, arm), hne⟩ :
      {index : Nat × Fin K // index ≠ target})
  have hreward :
      stream₁ (ETC.realHistoryPullCount n history arm) arm =
        stream₂ (ETC.realHistoryPullCount n history arm) arm := by
    simpa [UCB.armStreamWithoutCoordinate, UCB.armStreamCoordinate] using hcoordinate
  rw [hreward]

/-- Before the target coordinate can be the next coordinate of its arm, the
entire next-pair law agrees for streams with the same omitted-coordinate
projection. -/
theorem historyStepKernel_apply_eq_of_withoutCoordinate_eq_of_target_count_lt
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (target : Nat × Fin K) (stream₁ stream₂ : UCB.ArmRewardStream K)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (hwithout : UCB.armStreamWithoutCoordinate target stream₁ =
      UCB.armStreamWithoutCoordinate target stream₂)
    (hcount : ETC.realHistoryPullCount n history target.2 < target.1) :
    historyStepKernel algorithm
        ((latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)).at (env, stream₁)) n history =
      historyStepKernel algorithm
        ((latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)).at (env, stream₂)) n history := by
  unfold historyStepKernel
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  congr 1
  apply Kernel.ext
  intro arm
  rw [Kernel.sectR_apply, Kernel.sectR_apply]
  apply latentArmStreamFeedback_eq_of_withoutCoordinate_eq_of_selectedCoordinate_ne
    env target stream₁ stream₂ n history arm hwithout
  intro heq
  have hindex := congrArg Prod.fst heq
  have harm := congrArg Prod.snd heq
  simp only at hindex harm
  subst arm
  omega

/-- Next pairs whose action avoids a designated arm. -/
def latentArmStreamNextActionNeSet {K : Nat} (arm : Fin K) :
    Set (Fin K × Real) :=
  {candidate | candidate ≠ arm} ×ˢ Set.univ

/-- Initial actions whose time-zero reward coordinate is not the omitted
target. -/
def latentArmStreamInitialSafeArmSet
    {K : Nat} (target : Nat × Fin K) : Set (Fin K) :=
  {arm | (0, arm) ≠ target}

theorem measurableSet_latentArmStreamNextActionNeSet
    {K : Nat} (arm : Fin K) :
    MeasurableSet (latentArmStreamNextActionNeSet arm) := by
  exact (measurableSet_singleton arm).compl.prod MeasurableSet.univ

/-- Even when the target pull index may already be next, the part of the
next-pair law selecting another arm remains independent of the target
coordinate. -/
theorem historyStepKernel_apply_restrict_nextActionNe_eq_of_withoutCoordinate_eq
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (target : Nat × Fin K) (stream₁ stream₂ : UCB.ArmRewardStream K)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (hwithout : UCB.armStreamWithoutCoordinate target stream₁ =
      UCB.armStreamWithoutCoordinate target stream₂) :
    (historyStepKernel algorithm
        ((latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)).at (env, stream₁)) n history).restrict
        (latentArmStreamNextActionNeSet target.2) =
      (historyStepKernel algorithm
        ((latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)).at (env, stream₂)) n history).restrict
        (latentArmStreamNextActionNeSet target.2) := by
  let actionNe : Set (Fin K) := {candidate | candidate ≠ target.2}
  have hactionNe : MeasurableSet actionNe :=
    (measurableSet_singleton target.2).compl
  unfold historyStepKernel
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  change
    ((algorithm.policy n history) ⊗ₘ
        Kernel.sectR
          (((latentArmStreamMeasurableHistoryEnvironment
            (Env := Env) (K := K)).at (env, stream₁)).feedback n) history).restrict
      (actionNe ×ˢ Set.univ) =
    ((algorithm.policy n history) ⊗ₘ
        Kernel.sectR
          (((latentArmStreamMeasurableHistoryEnvironment
            (Env := Env) (K := K)).at (env, stream₂)).feedback n) history).restrict
      (actionNe ×ˢ Set.univ)
  rw [Measure.compProd_restrict_prod _ _ hactionNe MeasurableSet.univ,
    Measure.compProd_restrict_prod _ _ hactionNe MeasurableSet.univ]
  apply Measure.compProd_congr
  filter_upwards [ae_restrict_mem hactionNe] with arm harm
  change arm ≠ target.2 at harm
  rw [Kernel.restrict_apply, Kernel.restrict_apply, Measure.restrict_univ,
    Measure.restrict_univ, Kernel.sectR_apply, Kernel.sectR_apply]
  apply latentArmStreamFeedback_eq_of_withoutCoordinate_eq_of_selectedCoordinate_ne
    env target stream₁ stream₂ n history arm hwithout
  intro heq
  have harm' := congrArg Prod.snd heq
  exact harm (by simpa using harm')

/-- The time-zero visible prefix is the initial action/feedback pair pushed
through the singleton-history constructor. -/
theorem latentArmStreamTrajectoryKernel_map_frestrictLe_zero
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (stream : UCB.ArmRewardStream K) :
    (latentArmStreamTrajectoryKernel algorithm env stream).map
        (Preorder.frestrictLe 0) =
      (algorithm.initialAction ⊗ₘ
        ((latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)).at (env, stream)).initialFeedback).map
        singletonPairHistory := by
  let environment := latentArmStreamMeasurableHistoryEnvironment
    (Env := Env) (K := K)
  have hprefix :
      (Preorder.frestrictLe 0 :
        ((t : Nat) -> Fin K × Real) ->
          History.FinitePairHistory (Fin K) Real 0) =
        singletonPairHistory ∘ (fun trajectory => trajectory 0) := by
    funext trajectory index
    have hindex : index = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ :=
      Subsingleton.elim _ _
    subst index
    rfl
  have heval :
      Measure.map (fun trajectory : (t : Nat) -> Fin K × Real => trajectory 0)
          (latentArmStreamTrajectoryKernel algorithm env stream) =
        algorithm.initialAction ⊗ₘ
          (environment.at (env, stream)).initialFeedback := by
    have hkernel := congrArg
      (fun kernel : Kernel (Env × UCB.ArmRewardStream K) (Fin K × Real) =>
        kernel (env, stream))
      (canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero
        algorithm environment)
    change
      ((canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment).map
        (fun trajectory => trajectory 0)) (env, stream) =
      (measurableEnvironmentInitialPairKernel algorithm environment)
        (env, stream) at hkernel
    rw [Kernel.map_apply _ (measurable_pi_apply 0),
      measurableEnvironmentInitialPairKernel_apply] at hkernel
    unfold latentArmStreamTrajectoryKernel
    rw [Kernel.comap_apply]
    exact hkernel
  rw [hprefix]
  change Measure.map
      (singletonPairHistory ∘
        (fun trajectory : (t : Nat) -> Fin K × Real => trajectory 0))
      (latentArmStreamTrajectoryKernel algorithm env stream) = _
  rw [← Measure.map_map measurable_singletonPairHistory
    (measurable_pi_apply 0), heval]

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

/-- Pulling the time-zero count cap back through the singleton-history
constructor leaves exactly the actions whose initial reward coordinate is not
the omitted target. -/
theorem singletonPairHistory_preimage_latentArmStreamPrefixCountCap_zero
    {K : Nat} (target : Nat × Fin K) :
    (@singletonPairHistory (Fin K) Real) ⁻¹'
        latentArmStreamPrefixCountCap 0 target =
      latentArmStreamInitialSafeArmSet target ×ˢ Set.univ := by
  classical
  rcases target with ⟨index, arm⟩
  ext pair
  cases index with
  | zero =>
      simp [latentArmStreamPrefixCountCap,
        latentArmStreamInitialSafeArmSet,
        ETC.realHistoryPullCount, singletonPairHistory]
  | succ index =>
      by_cases hpair : pair.1 = arm <;>
        simp [latentArmStreamPrefixCountCap,
          latentArmStreamInitialSafeArmSet,
          ETC.realHistoryPullCount, singletonPairHistory, hpair]

/-- Count-cap locality at the initial pair. -/
theorem latentArmStreamPrefixCountCapLocality_zero
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (target : Nat × Fin K)
    (stream₁ stream₂ : UCB.ArmRewardStream K)
    (hwithout : UCB.armStreamWithoutCoordinate target stream₁ =
      UCB.armStreamWithoutCoordinate target stream₂) :
    ((latentArmStreamTrajectoryKernel algorithm env stream₁).map
        (Preorder.frestrictLe 0)).restrict
      (latentArmStreamPrefixCountCap 0 target) =
    ((latentArmStreamTrajectoryKernel algorithm env stream₂).map
        (Preorder.frestrictLe 0)).restrict
      (latentArmStreamPrefixCountCap 0 target) := by
  rw [latentArmStreamTrajectoryKernel_map_frestrictLe_zero,
    latentArmStreamTrajectoryKernel_map_frestrictLe_zero,
    Measure.restrict_map measurable_singletonPairHistory
      (measurableSet_latentArmStreamPrefixCountCap 0 target),
    Measure.restrict_map measurable_singletonPairHistory
      (measurableSet_latentArmStreamPrefixCountCap 0 target),
    singletonPairHistory_preimage_latentArmStreamPrefixCountCap_zero]
  have hsafe : MeasurableSet (latentArmStreamInitialSafeArmSet target) := by
    exact (measurableSet_eq_fun
      (measurable_const.prodMk measurable_id) measurable_const).compl
  congr 1
  rw [Measure.compProd_restrict_prod
      algorithm.initialAction
      ((latentArmStreamMeasurableHistoryEnvironment
        (Env := Env) (K := K)).at (env, stream₁)).initialFeedback
      hsafe MeasurableSet.univ,
    Measure.compProd_restrict_prod
      algorithm.initialAction
      ((latentArmStreamMeasurableHistoryEnvironment
        (Env := Env) (K := K)).at (env, stream₂)).initialFeedback
      hsafe MeasurableSet.univ]
  apply Measure.compProd_congr
  filter_upwards [ae_restrict_mem hsafe] with arm harm
  have hne : (0, arm) ≠ target := harm
  have hcoordinate := congrFun hwithout
    (⟨(0, arm), hne⟩ : {index : Nat × Fin K // index ≠ target})
  have hreward : stream₁ 0 arm = stream₂ 0 arm := by
    simpa [UCB.armStreamWithoutCoordinate, UCB.armStreamCoordinate] using
      hcoordinate
  rw [Kernel.restrict_apply, Kernel.restrict_apply,
    Measure.restrict_univ, Measure.restrict_univ,
    latentArmStreamMeasurableHistoryEnvironment_at_initialFeedback_apply,
    latentArmStreamMeasurableHistoryEnvironment_at_initialFeedback_apply,
    hreward]

/-- Strict count region used by the first rectangle in the successor cap
decomposition. -/
def latentArmStreamPrefixCountLt
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    Set (History.FinitePairHistory (Fin K) Real n) :=
  {history | ETC.realHistoryPullCount n history target.2 < target.1}

theorem measurableSet_latentArmStreamPrefixCountLt
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    MeasurableSet (latentArmStreamPrefixCountLt n target) := by
  exact measurableSet_lt
    (UCB.measurable_realHistoryPullCount n target.2) measurable_const

/-- Exact count region used by the second rectangle in the successor cap
decomposition. -/
def latentArmStreamPrefixCountEq
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    Set (History.FinitePairHistory (Fin K) Real n) :=
  {history | ETC.realHistoryPullCount n history target.2 = target.1}

theorem measurableSet_latentArmStreamPrefixCountEq
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    MeasurableSet (latentArmStreamPrefixCountEq n target) := by
  exact measurableSet_eq_fun
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

/-- The successor prefix remains below the target count cap exactly when the
old prefix is capped and either has strict slack or avoids the target arm. -/
theorem mem_latentArmStreamPrefixCountCap_extendPairHistorySucc_iff
    {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (next : Fin K × Real) (target : Nat × Fin K) :
    History.extendPairHistorySucc history next ∈
        latentArmStreamPrefixCountCap (n + 1) target ↔
      history ∈ latentArmStreamPrefixCountCap n target ∧
        (ETC.realHistoryPullCount n history target.2 < target.1 ∨
          next.1 ≠ target.2) := by
  rw [latentArmStreamPrefixCountCap, Set.mem_setOf_eq,
    realHistoryPullCount_extendPairHistorySucc,
    latentArmStreamPrefixCountCap, Set.mem_setOf_eq]
  by_cases hnext : next.1 = target.2
  · simp [hnext]
    omega
  · simp [hnext]

/-- A capped successor prefix was already capped before appending its last
action/reward pair. -/
theorem latentArmStreamPrefixCountCap_of_extendPairHistorySucc_mem
    {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (next : Fin K × Real) (target : Nat × Fin K)
    (hcap : History.extendPairHistorySucc history next ∈
      latentArmStreamPrefixCountCap (n + 1) target) :
    history ∈ latentArmStreamPrefixCountCap n target := by
  exact
    (mem_latentArmStreamPrefixCountCap_extendPairHistorySucc_iff
      n history next target).mp hcap |>.1

/-- Every appended pair that remains in the successor cap reads a stream
coordinate different from the omitted target. -/
theorem selectedCoordinate_ne_of_extendPairHistorySucc_mem_prefixCountCap
    {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (next : Fin K × Real) (target : Nat × Fin K)
    (hcap : History.extendPairHistorySucc history next ∈
      latentArmStreamPrefixCountCap (n + 1) target) :
    (ETC.realHistoryPullCount n history next.1, next.1) ≠ target := by
  intro heq
  have hnext : next.1 = target.2 := congrArg Prod.snd heq
  rcases
      (mem_latentArmStreamPrefixCountCap_extendPairHistorySucc_iff
        n history next target).mp hcap with ⟨_hcap, hstrict | havoid⟩
  · have hcountEq : ETC.realHistoryPullCount n history target.2 = target.1 := by
      simpa [hnext] using congrArg Prod.fst heq
    exact (Nat.ne_of_lt hstrict) hcountEq
  · exact havoid hnext

/-- Pulling the successor count cap back through history extension gives two
measurable rectangles: below the target count every action is safe, while at
the target count only actions avoiding the target arm are safe. -/
theorem latentArmStreamSuccessorCountCap_preimage
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    (fun sample : History.FinitePairHistory (Fin K) Real n × (Fin K × Real) =>
      History.extendPairHistorySucc sample.1 sample.2) ⁻¹'
        latentArmStreamPrefixCountCap (n + 1) target =
      (latentArmStreamPrefixCountLt n target ×ˢ Set.univ) ∪
        (latentArmStreamPrefixCountEq n target ×ˢ
          latentArmStreamNextActionNeSet target.2) := by
  ext sample
  rw [Set.mem_preimage]
  simp only [latentArmStreamPrefixCountCap, Set.mem_setOf_eq,
    realHistoryPullCount_extendPairHistorySucc, Set.mem_union, Set.mem_prod,
    Set.mem_univ, and_true, latentArmStreamPrefixCountLt,
    latentArmStreamPrefixCountEq, latentArmStreamNextActionNeSet]
  by_cases haction : sample.2.1 = target.2
  · simp [haction]
  · simp [haction]
    omega

/-- Next action/reward pairs that keep a fixed old prefix below the successor
count cap. -/
def latentArmStreamSuccessorCountCapSection
    {K : Nat} (n : Nat) (target : Nat × Fin K)
    (history : History.FinitePairHistory (Fin K) Real n) :
    Set (Fin K × Real) :=
  {next |
    History.extendPairHistorySucc history next ∈
      latentArmStreamPrefixCountCap (n + 1) target}

theorem measurableSet_latentArmStreamSuccessorCountCapSection
    {K : Nat} (n : Nat) (target : Nat × Fin K)
    (history : History.FinitePairHistory (Fin K) Real n) :
    MeasurableSet
      (latentArmStreamSuccessorCountCapSection n target history) := by
  exact (measurableSet_latentArmStreamPrefixCountCap (n + 1) target).preimage
    (History.measurable_extendPairHistorySucc.comp
      (measurable_const.prodMk measurable_id))

/-- Over a previously capped prefix, the one-step law restricted to capped
successors depends only on the complement of the omitted stream coordinate. -/
theorem historyStepKernel_apply_restrict_successorCountCap_eq_of_withoutCoordinate_eq
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (target : Nat × Fin K) (stream₁ stream₂ : UCB.ArmRewardStream K)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (hwithout : UCB.armStreamWithoutCoordinate target stream₁ =
      UCB.armStreamWithoutCoordinate target stream₂)
    (hcap : history ∈ latentArmStreamPrefixCountCap n target) :
    (historyStepKernel algorithm
        ((latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)).at (env, stream₁)) n history).restrict
      (latentArmStreamSuccessorCountCapSection n target history) =
    (historyStepKernel algorithm
        ((latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)).at (env, stream₂)) n history).restrict
      (latentArmStreamSuccessorCountCapSection n target history) := by
  by_cases hstrict :
      ETC.realHistoryPullCount n history target.2 < target.1
  · rw [historyStepKernel_apply_eq_of_withoutCoordinate_eq_of_target_count_lt
      algorithm env target stream₁ stream₂ n history hwithout hstrict]
  · have hsection :
        latentArmStreamSuccessorCountCapSection n target history =
          latentArmStreamNextActionNeSet target.2 := by
      ext next
      simp only [latentArmStreamSuccessorCountCapSection,
        latentArmStreamNextActionNeSet, Set.mem_setOf_eq, Set.mem_prod,
        Set.mem_univ, and_true]
      rw [mem_latentArmStreamPrefixCountCap_extendPairHistorySucc_iff]
      simp [hcap, hstrict]
    rw [hsection]
    exact
      historyStepKernel_apply_restrict_nextActionNe_eq_of_withoutCoordinate_eq
        algorithm env target stream₁ stream₂ n history hwithout

/-- Successor step for count-capped locality of the fixed-stream visible
trajectory prefix law. -/
theorem latentArmStreamTrajectoryKernel_map_frestrictLe_restrict_countCap_succ
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (target : Nat × Fin K) (stream₁ stream₂ : UCB.ArmRewardStream K)
    (hwithout : UCB.armStreamWithoutCoordinate target stream₁ =
      UCB.armStreamWithoutCoordinate target stream₂)
    (n : Nat)
    (hprefix :
      ((latentArmStreamTrajectoryKernel algorithm env stream₁).map
          (Preorder.frestrictLe n)).restrict
        (latentArmStreamPrefixCountCap n target) =
      ((latentArmStreamTrajectoryKernel algorithm env stream₂).map
          (Preorder.frestrictLe n)).restrict
        (latentArmStreamPrefixCountCap n target)) :
    ((latentArmStreamTrajectoryKernel algorithm env stream₁).map
        (Preorder.frestrictLe (n + 1))).restrict
      (latentArmStreamPrefixCountCap (n + 1) target) =
    ((latentArmStreamTrajectoryKernel algorithm env stream₂).map
        (Preorder.frestrictLe (n + 1))).restrict
      (latentArmStreamPrefixCountCap (n + 1) target) := by
  let environment := latentArmStreamMeasurableHistoryEnvironment
    (Env := Env) (K := K)
  let join := fun trajectory : (t : Nat) → Fin K × Real =>
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))
  let successor := fun sample :
      History.FinitePairHistory (Fin K) Real n × (Fin K × Real) =>
    History.extendPairHistorySucc sample.1 sample.2
  have hjoin : Measurable join :=
    (Preorder.measurable_frestrictLe n).prodMk
      (measurable_pi_apply (n + 1))
  have hsuccessor : Measurable successor := by
    exact History.measurable_extendPairHistorySucc
  have hjoint₁ :
      (latentArmStreamTrajectoryKernel algorithm env stream₁).map join =
        (latentArmStreamTrajectoryKernel algorithm env stream₁).map
            (Preorder.frestrictLe n) ⊗ₘ
          historyStepKernel algorithm (environment.at (env, stream₁)) n := by
    exact latentArmStreamTrajectoryKernel_map_prefix_next_eq_compProd
      algorithm env stream₁ n
  have hjoint₂ :
      (latentArmStreamTrajectoryKernel algorithm env stream₂).map join =
        (latentArmStreamTrajectoryKernel algorithm env stream₂).map
            (Preorder.frestrictLe n) ⊗ₘ
          historyStepKernel algorithm (environment.at (env, stream₂)) n := by
    exact latentArmStreamTrajectoryKernel_map_prefix_next_eq_compProd
      algorithm env stream₂ n
  have hpreimage :
      successor ⁻¹' latentArmStreamPrefixCountCap (n + 1) target ⊆
        latentArmStreamPrefixCountCap n target ×ˢ Set.univ := by
    intro sample hsample
    exact ⟨latentArmStreamPrefixCountCap_of_extendPairHistorySucc_mem
      n sample.1 sample.2 target hsample, Set.mem_univ _⟩
  have htransfer :=
    Measure.map_compProd_restrict_eq_of_base_restrict_eq_of_fiber_restrict_eq
      successor hsuccessor
      (measurableSet_latentArmStreamPrefixCountCap n target)
      (measurableSet_latentArmStreamPrefixCountCap (n + 1) target)
      hpreimage hprefix
      (fun history historySafe => by
        simpa [successor, latentArmStreamSuccessorCountCapSection] using
          historyStepKernel_apply_restrict_successorCountCap_eq_of_withoutCoordinate_eq
            algorithm env target stream₁ stream₂ n history hwithout historySafe)
  rw [← hjoint₁, ← hjoint₂,
    Measure.map_map hsuccessor hjoin,
    Measure.map_map hsuccessor hjoin] at htransfer
  have hencode : successor ∘ join = Preorder.frestrictLe (n + 1) := by
    funext trajectory
    funext index
    by_cases hindex : index.1 ≤ n
    · simp [successor, join, Function.comp_apply,
        History.extendPairHistorySucc, Preorder.frestrictLe_apply, hindex]
    · have hindex_succ : index.1 = n + 1 := by
        have hle : index.1 ≤ n + 1 := Finset.mem_Iic.mp index.2
        omega
      simp [successor, join, Function.comp_apply,
        History.extendPairHistorySucc, Preorder.frestrictLe_apply,
        hindex_succ]
  simpa only [hencode] using htransfer

/-- Count-capped fixed-stream prefix locality under equality of all latent
coordinates except the omitted target. -/
theorem latentArmStreamTrajectoryKernel_map_frestrictLe_restrict_countCap_eq_of_withoutCoordinate_eq
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (target : Nat × Fin K) (stream₁ stream₂ : UCB.ArmRewardStream K)
    (hwithout : UCB.armStreamWithoutCoordinate target stream₁ =
      UCB.armStreamWithoutCoordinate target stream₂)
    (n : Nat) :
    ((latentArmStreamTrajectoryKernel algorithm env stream₁).map
        (Preorder.frestrictLe n)).restrict
      (latentArmStreamPrefixCountCap n target) =
    ((latentArmStreamTrajectoryKernel algorithm env stream₂).map
        (Preorder.frestrictLe n)).restrict
      (latentArmStreamPrefixCountCap n target) := by
  induction n with
  | zero =>
      exact latentArmStreamPrefixCountCapLocality_zero
        algorithm env target stream₁ stream₂ hwithout
  | succ n ih =>
      exact
        latentArmStreamTrajectoryKernel_map_frestrictLe_restrict_countCap_succ
          algorithm env target stream₁ stream₂ hwithout n ih

/-- Exact contract for branchwise prefix/action locality.  The count-capped
trajectory induction above proves this contract below. -/
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

/-- Count-cap locality of visible prefixes implies the exact history/action
branch-locality contract. -/
theorem latentArmStreamVisiblePrefixNextActionBranchLocality_of_prefixCountCapLocality
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) (n : Nat)
    (hcap : ∀ (target : Nat × Fin K)
        (stream₁ stream₂ : UCB.ArmRewardStream K),
      UCB.armStreamWithoutCoordinate target stream₁ =
        UCB.armStreamWithoutCoordinate target stream₂ →
      (((latentArmStreamTrajectoryKernel algorithm env stream₁).map
          (Preorder.frestrictLe n)).restrict
        (latentArmStreamPrefixCountCap n target)) =
      (((latentArmStreamTrajectoryKernel algorithm env stream₂).map
          (Preorder.frestrictLe n)).restrict
        (latentArmStreamPrefixCountCap n target))) :
    LatentArmStreamVisiblePrefixNextActionBranchLocality
      algorithm env n := by
  intro target
  apply Kernel.ext
  intro stream
  rw [Kernel.restrict_apply, Kernel.comap_apply]
  unfold latentArmStreamVisiblePrefixNextActionBranchKernel
  rw [Kernel.restrict_apply, Kernel.comap_apply]
  rw [Kernel.map_apply _ (measurable_latentArmStreamVisiblePrefixNextAction n),
    Kernel.map_apply _ (measurable_latentArmStreamVisiblePrefixNextAction n)]
  let rebuilt := UCB.armStreamInsertCoordinate target 0
    (UCB.armStreamWithoutCoordinate target stream)
  have hleft :
      ((latentArmStreamTrajectoryKernel algorithm env stream).map
        (latentArmStreamVisiblePrefixNextAction n)) =
        ((latentArmStreamTrajectoryKernel algorithm env stream).map
          (Preorder.frestrictLe n)) ⊗ₘ algorithm.policy n := by
    unfold latentArmStreamTrajectoryKernel
    rw [Kernel.comap_apply]
    exact
      canonicalMeasurableEnvironmentTrajectoryKernel_map_history_action_eq_compProd
        algorithm
        (latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)) (env, stream) n
  have hright :
      ((latentArmStreamTrajectoryKernel algorithm env rebuilt).map
        (latentArmStreamVisiblePrefixNextAction n)) =
        ((latentArmStreamTrajectoryKernel algorithm env rebuilt).map
          (Preorder.frestrictLe n)) ⊗ₘ algorithm.policy n := by
    unfold latentArmStreamTrajectoryKernel
    rw [Kernel.comap_apply]
    exact
      canonicalMeasurableEnvironmentTrajectoryKernel_map_history_action_eq_compProd
        algorithm
        (latentArmStreamMeasurableHistoryEnvironment
          (Env := Env) (K := K)) (env, rebuilt) n
  rw [hleft, hright]
  have hbranchSubset :
      UCB.armStreamHistoryActionCoordinateBranch n target ⊆
        latentArmStreamPrefixCountCap n target ×ˢ Set.univ := by
    intro condition hcondition
    have hcoordinate :
        UCB.armStreamCoordinateOfHistoryAction n condition = target :=
      hcondition
    have hcount := congrArg Prod.fst hcoordinate
    have harm := congrArg Prod.snd hcoordinate
    have hcount' :
        ETC.realHistoryPullCount n condition.1 condition.2 = target.1 := by
      simpa [UCB.armStreamCoordinateOfHistoryAction] using hcount
    have harm' : condition.2 = target.2 := by
      simpa [UCB.armStreamCoordinateOfHistoryAction] using harm
    constructor
    · change ETC.realHistoryPullCount n condition.1 target.2 <= target.1
      rw [← harm', hcount']
    · trivial
  apply Measure.restrict_congr_mono hbranchSubset
  rw [Measure.compProd_restrict_prod
      _ _ (measurableSet_latentArmStreamPrefixCountCap n target)
        MeasurableSet.univ,
    Measure.compProd_restrict_prod
      _ _ (measurableSet_latentArmStreamPrefixCountCap n target)
        MeasurableSet.univ]
  rw [hcap target stream rebuilt (by simp [rebuilt])]

/-- Every latent arm-stream trajectory kernel satisfies branch locality: on
the exact next-coordinate branch, the visible prefix and next action depend
only on the complementary latent coordinates.  This does not yet identify the
latent visible law with the native fixed-IID process. -/
theorem latentArmStreamVisiblePrefixNextActionBranchLocality
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) (n : Nat) :
    LatentArmStreamVisiblePrefixNextActionBranchLocality
      algorithm env n := by
  apply
    latentArmStreamVisiblePrefixNextActionBranchLocality_of_prefixCountCapLocality
      algorithm env n
  intro target stream₁ stream₂ hwithout
  exact
    latentArmStreamTrajectoryKernel_map_frestrictLe_restrict_countCap_eq_of_withoutCoordinate_eq
      algorithm env target stream₁ stream₂ hwithout n

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

/-- Unconditional compiled branchwise product law obtained from the proved
count-capped locality producer. -/
theorem latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (n : Nat) (target : Nat × Fin K) :
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
  exact
    latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod_of_locality
      algorithm env nu n
      (latentArmStreamVisiblePrefixNextActionBranchLocality algorithm env n)
      target

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
