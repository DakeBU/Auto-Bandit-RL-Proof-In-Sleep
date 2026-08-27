import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoLatentReward
import BanditRLProof.Algorithms.ThompsonReferencePolicy
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
and gives the exact finite stream-box/visible-prefix mixture law.  The remaining
route is to prove branchwise prefix-plus-next-pair freshness, use it to identify
the visible marginal of this mixture with the corresponding native fixed-IID
trajectory-prefix law, and then apply trajectory uniqueness.  Consequently, no
full native trajectory-law equality, stopped-reward IID statement, or Theorem-2
terminal is claimed here.
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
