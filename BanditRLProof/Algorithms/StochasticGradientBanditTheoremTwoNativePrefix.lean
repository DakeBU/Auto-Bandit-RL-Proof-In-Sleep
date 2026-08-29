import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoNativeTrajectory

/-!
# Two-arm SGB Theorem 2: native stationary environment and one-step prefix step

The latent arm-stream coupling draws every reward coordinate before the
algorithm runs, whereas the native fixed-IID process draws only the reward of
the arm actually selected in each round.  The compiled deterministic-time
one-step selected-reward laws describe the coupling; this module states the
native process against which those laws must be compared.

It records the stationary reward environment whose feedback kernel is the
selected-arm law, and identifies its history step kernel with the composition
of the algorithm policy and that law.  No native-prefix identification,
full-process equality, selected/stopped IID law, future/no-return statement,
or Theorem-2 endpoint is claimed here.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
noncomputable section
universe u

namespace Thompson

/-- The native stationary environment: feedback is the law of the selected arm,
independent of the observed history. -/
def stationaryRewardHistoryEnvironment
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    HistoryEnvironment (Fin K) Real where
  feedback n := UCB.armStreamSelectedRewardKernel n nu
  initialFeedback := nu

/-- The native step kernel composes the policy with the selected-arm law. -/
theorem historyStepKernel_stationaryRewardHistoryEnvironment
    {K : Nat} (algorithm : HistoryAlgorithm (Fin K) Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    historyStepKernel algorithm (stationaryRewardHistoryEnvironment nu) n =
      algorithm.policy n ⊗ₖ UCB.armStreamSelectedRewardKernel n nu :=
  rfl

/-- One-step native extension of the visible prefix under the latent coupling.

At every deterministic time `n`, the joint law of the visible prefix through
`n` and the next observed action/reward pair is the prefix law composed with the
native stationary step kernel.  This is a single-step statement; it does not
identify whole prefixes or the full native law. -/
theorem latentArmStreamVisiblePrefixNextPair_eq_compProd
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Measure.map
        (fun sample : UCB.ArmRewardStream K × ((t : Nat) -> Fin K × Real) =>
          (Preorder.frestrictLe n sample.2, sample.2 (n + 1)))
        (latentArmStreamTrajectoryMeasure algorithm env nu) =
      Measure.map
          (fun sample : UCB.ArmRewardStream K × ((t : Nat) -> Fin K × Real) =>
            Preorder.frestrictLe n sample.2)
          (latentArmStreamTrajectoryMeasure algorithm env nu) ⊗ₘ
        historyStepKernel algorithm (stationaryRewardHistoryEnvironment nu) n := by
  classical
  have hmeasPair :
      Measurable
        (fun sample : UCB.ArmRewardStream K × ((t : Nat) -> Fin K × Real) =>
          (latentArmStreamVisiblePrefixNextAction n sample.2,
            latentArmStreamVisibleNextReward n sample.2)) := by
    exact ((measurable_latentArmStreamVisiblePrefixNextAction n).comp
      measurable_snd).prodMk
      ((measurable_latentArmStreamVisibleNextReward n).comp measurable_snd)
  have hjoint := latentArmStreamVisibleNextReward_joint_eq_compProd
    algorithm env nu n
  have haction := latentArmStreamTrajectoryMeasure_map_visiblePrefix_nextAction_eq_compProd
    algorithm env nu n
  rw [haction] at hjoint
  have hassoc := Measure.compProd_assoc'
    (μ := Measure.map
      (fun sample : UCB.ArmRewardStream K × ((t : Nat) -> Fin K × Real) =>
        Preorder.frestrictLe n sample.2)
      (latentArmStreamTrajectoryMeasure algorithm env nu))
    (κ := algorithm.policy n)
    (η := UCB.armStreamSelectedRewardKernel n nu)
  rw [historyStepKernel_stationaryRewardHistoryEnvironment, ← hassoc, ← hjoint,
    Measure.map_map MeasurableEquiv.prodAssoc.measurable hmeasPair]
  rfl

/-- Time-zero pair law of the latent coupling: the initial action follows the
algorithm's initial law and the initial reward is a fresh draw from the selected
arm law. -/
theorem latentArmStreamVisibleInitialPair_eq_compProd
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Measure.map
        (fun sample : UCB.ArmRewardStream K × ((t : Nat) -> Fin K × Real) =>
          sample.2 0)
        (latentArmStreamTrajectoryMeasure algorithm env nu) =
      algorithm.initialAction ⊗ₘ nu := by
  classical
  have hzero : forall stream : UCB.ArmRewardStream K,
      (latentArmStreamTrajectoryKernel algorithm env stream).map
          (fun trajectory : (t : Nat) -> Fin K × Real => trajectory 0) =
        algorithm.initialAction ⊗ₘ
          ((latentArmStreamMeasurableHistoryEnvironment
            (Env := Env) (K := K)).at (env, stream)).initialFeedback := by
    intro stream
    have hkernel :
        ((canonicalMeasurableEnvironmentTrajectoryKernel algorithm
            (latentArmStreamMeasurableHistoryEnvironment
              (Env := Env) (K := K))).map
          (fun trajectory : (t : Nat) -> Fin K × Real => trajectory 0))
            (env, stream) =
          measurableEnvironmentInitialPairKernel algorithm
            (latentArmStreamMeasurableHistoryEnvironment
              (Env := Env) (K := K)) (env, stream) := by
      rw [canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero]
    rw [Kernel.map_apply _ (measurable_pi_apply 0),
      measurableEnvironmentInitialPairKernel_apply] at hkernel
    simpa [latentArmStreamTrajectoryKernel, Kernel.comap_apply] using hkernel
  have hdet : forall stream : UCB.ArmRewardStream K,
      ((latentArmStreamMeasurableHistoryEnvironment
        (Env := Env) (K := K)).at (env, stream)).initialFeedback =
        Kernel.deterministic (fun arm : Fin K => stream 0 arm)
          (measurable_from_top) := by
    intro stream
    ext arm S hS
    rw [Kernel.deterministic_apply]
    simp [MeasurableHistoryEnvironment.at,
      latentArmStreamMeasurableHistoryEnvironment_initialFeedback_apply]
  have hmeasEval :
      Measurable
        (fun sample : UCB.ArmRewardStream K × ((t : Nat) -> Fin K × Real) =>
          sample.2 0) := by
    exact (measurable_pi_apply 0).comp measurable_snd
  ext S hS
  rw [Measure.map_apply hmeasEval hS, latentArmStreamTrajectoryMeasure,
    Measure.compProd_apply (hmeasEval hS)]
  have hfiber : forall stream : UCB.ArmRewardStream K,
      (latentArmStreamTrajectoryKernel algorithm env) stream
          (Prod.mk stream ⁻¹'
            ((fun sample : UCB.ArmRewardStream K × ((t : Nat) -> Fin K × Real) =>
              sample.2 0) ⁻¹' S)) =
        algorithm.initialAction ((fun arm : Fin K => (arm, stream 0 arm)) ⁻¹' S) := by
    intro stream
    have hpre :
        (Prod.mk stream ⁻¹'
          ((fun sample : UCB.ArmRewardStream K × ((t : Nat) -> Fin K × Real) =>
            sample.2 0) ⁻¹' S)) =
          (fun trajectory : (t : Nat) -> Fin K × Real => trajectory 0) ⁻¹' S := rfl
    rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) hS, hzero stream,
      hdet stream, Measure.compProd_deterministic (measurable_from_top
        (f := fun arm : Fin K => stream 0 arm))]
    rw [Measure.map_apply (measurable_from_top
      (f := fun arm : Fin K => (arm, stream 0 arm))) hS]
  simp only [hfiber]
  have hmeasSwap :
      Measurable
        (fun p : UCB.ArmRewardStream K × Fin K => (p.2, p.1 0 p.2)) := by
    refine measurable_from_prod_countable_left ?_
    intro arm
    exact measurable_const.prodMk
      ((measurable_pi_apply arm).comp (measurable_pi_apply 0))
  have hmeasSet : MeasurableSet
      ((fun p : UCB.ArmRewardStream K × Fin K => (p.2, p.1 0 p.2)) ⁻¹' S) :=
    hmeasSwap hS
  have hswap :
      ∫⁻ stream : UCB.ArmRewardStream K,
          algorithm.initialAction
            ((fun arm : Fin K => (arm, stream 0 arm)) ⁻¹' S)
          ∂(UCB.armStreamMeasure nu) =
        ∫⁻ arm : Fin K,
          UCB.armStreamMeasure nu
            ((fun stream : UCB.ArmRewardStream K => (arm, stream 0 arm)) ⁻¹' S)
          ∂algorithm.initialAction :=
    (Measure.prod_apply (μ := UCB.armStreamMeasure nu)
        (ν := algorithm.initialAction) hmeasSet).symm.trans
      (Measure.prod_apply_symm (μ := UCB.armStreamMeasure nu)
        (ν := algorithm.initialAction) hmeasSet)
  have hcoord : forall arm : Fin K,
      UCB.armStreamMeasure nu
          ((fun stream : UCB.ArmRewardStream K => (arm, stream 0 arm)) ⁻¹' S) =
        nu arm (Prod.mk arm ⁻¹' S) := by
    intro arm
    have hpre :
        ((fun stream : UCB.ArmRewardStream K => (arm, stream 0 arm)) ⁻¹' S) =
          (fun stream : UCB.ArmRewardStream K => stream 0 arm) ⁻¹'
            (Prod.mk arm ⁻¹' S) := rfl
    have hmeasCoord :
        Measurable (fun stream : UCB.ArmRewardStream K => stream 0 arm) := by
      exact (measurable_pi_apply arm).comp (measurable_pi_apply 0)
    rw [hpre, ← Measure.map_apply hmeasCoord
      (hS.preimage (measurable_prodMk_left)),
      UCB.armStreamMeasure_map_coord nu 0 arm]
  rw [hswap, Measure.compProd_apply hS]
  exact lintegral_congr fun arm => hcoord arm

/-- The Ionescu-Tulcea trajectory law reproduces its initial law at time zero. -/
theorem trajMeasure_map_eval_zero
    {X : Nat -> Type u} [forall n, MeasurableSpace (X n)]
    (mu0 : Measure (X 0)) [IsProbabilityMeasure mu0]
    (kappa : (n : Nat) -> Kernel ((i : Finset.Iic n) -> X i) (X (n + 1)))
    [forall n, IsMarkovKernel (kappa n)] :
    (Kernel.trajMeasure mu0 kappa).map (fun x => x 0) = mu0 := by
  have hcomp :
      (fun x : (n : Nat) -> X n => x 0) =
        (fun h : (i : Finset.Iic 0) -> X i =>
          h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘ Preorder.frestrictLe 0 := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (Preorder.measurable_frestrictLe 0),
    Kernel.trajMeasure, Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
  simp only [Measure.id_comp]
  rw [Measure.map_map (measurable_pi_apply
    (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0)) (by fun_prop)]
  convert Measure.map_id

/-- The visible prefix at `n + 1` is the prefix at `n` extended by the next pair. -/
theorem frestrictLe_succ_eq_extendPairHistorySucc
    {K : Nat} (n : Nat) (x : (t : Nat) -> Fin K × Real) :
    Preorder.frestrictLe (n + 1) x =
      History.extendPairHistorySucc (Preorder.frestrictLe n x) (x (n + 1)) := by
  funext i
  by_cases hi : i.1 <= n
  · rw [History.extendPairHistorySucc_apply_of_le _ _ i hi]
    rfl
  · have hval : i.1 = n + 1 :=
      le_antisymm (Finset.mem_Iic.mp i.2) (Nat.succ_le_of_lt (Nat.not_le.mp hi))
    have hi' : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hval
    subst hi'
    rw [History.extendPairHistorySucc_apply_succ]
    rfl

/-- The native fixed-i.i.d. trajectory law: the same algorithm run against the
stationary environment whose feedback is the selected-arm law. -/
def nativeStationaryTrajectoryMeasure
    {K : Nat} (algorithm : HistoryAlgorithm (Fin K) Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Measure ((n : Nat) -> Fin K × Real) :=
  canonicalHistoryTrajectoryMeasure algorithm
    (stationaryRewardHistoryEnvironment nu)

instance instNativeStationaryTrajectoryMeasureIsProbability
    {K : Nat} (algorithm : HistoryAlgorithm (Fin K) Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    IsProbabilityMeasure (nativeStationaryTrajectoryMeasure algorithm nu) := by
  unfold nativeStationaryTrajectoryMeasure
  infer_instance

/-- **Native-prefix identification.**  At every finite horizon `n`, the visible
trajectory marginal of the latent arm-stream coupling and the native
fixed-i.i.d. process induce the same law on prefixes through `n`.

This is a finite-prefix identity.  It does not by itself give the full native
visible law, selected- or stopped-reward i.i.d. statements, the stopped-prefix
future/no-return law, or Theorem 2. -/
theorem latentArmStreamVisibleTrajectoryMeasure_map_frestrictLe_eq_native
    {Env : Type u} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    ((latentArmStreamTrajectoryMeasure algorithm env nu).map Prod.snd).map
        (Preorder.frestrictLe n) =
      (nativeStationaryTrajectoryMeasure algorithm nu).map
        (Preorder.frestrictLe n) := by
  classical
  have hmarginal : forall {gamma : Type} [MeasurableSpace gamma]
      (g : ((t : Nat) -> Fin K × Real) -> gamma), Measurable g ->
      ((latentArmStreamTrajectoryMeasure algorithm env nu).map Prod.snd).map g =
        (latentArmStreamTrajectoryMeasure algorithm env nu).map
          (fun sample => g sample.2) := by
    intro gamma _ g hg
    rw [Measure.map_map hg measurable_snd]
    rfl
  induction n with
  | zero =>
      have hsingleton : forall x : (t : Nat) -> Fin K × Real,
          Preorder.frestrictLe 0 x = singletonPairHistory (x 0) := by
        intro x
        funext i
        have : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subsingleton.elim _ _
        subst this
        rfl
      have hnative :
          (nativeStationaryTrajectoryMeasure algorithm nu).map
              (fun x : (t : Nat) -> Fin K × Real => x 0) =
            algorithm.initialAction ⊗ₘ nu := by
        rw [nativeStationaryTrajectoryMeasure, canonicalHistoryTrajectoryMeasure,
          trajMeasure_map_eval_zero]
        rfl
      have hfun :
          (Preorder.frestrictLe 0 :
            ((t : Nat) -> Fin K × Real) ->
              History.FinitePairHistory (Fin K) Real 0) =
            singletonPairHistory ∘ (fun x => x 0) := funext hsingleton
      rw [hfun, ← Measure.map_map measurable_singletonPairHistory
          (measurable_pi_apply 0),
        ← Measure.map_map measurable_singletonPairHistory
          (measurable_pi_apply 0),
        hnative, hmarginal _ (measurable_pi_apply 0),
        latentArmStreamVisibleInitialPair_eq_compProd]
  | succ n ih =>
      have hnativeEq :
          nativeStationaryTrajectoryMeasure algorithm nu =
            Kernel.trajMeasure (algorithm.initialAction ⊗ₘ nu)
              (fun k => historyStepKernel algorithm
                (stationaryRewardHistoryEnvironment nu) k) := rfl
      have hmeasPair :
          Measurable
            (fun x : (t : Nat) -> Fin K × Real =>
              (Preorder.frestrictLe n x, x (n + 1))) :=
        (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
      have hstepNative :=
        Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
          (X := fun _ : Nat => Fin K × Real)
          (μ₀ := algorithm.initialAction ⊗ₘ nu)
          (κ := fun k => historyStepKernel algorithm
            (stationaryRewardHistoryEnvironment nu) k)
          (a := n)
      have hstepVisible :=
        latentArmStreamVisiblePrefixNextPair_eq_compProd algorithm env nu n
      have hjoint :
          ((latentArmStreamTrajectoryMeasure algorithm env nu).map Prod.snd).map
              (fun x : (t : Nat) -> Fin K × Real =>
                (Preorder.frestrictLe n x, x (n + 1))) =
            (nativeStationaryTrajectoryMeasure algorithm nu).map
              (fun x : (t : Nat) -> Fin K × Real =>
                (Preorder.frestrictLe n x, x (n + 1))) := by
        rw [hmarginal _ hmeasPair, hstepVisible,
          ← hmarginal _ (Preorder.measurable_frestrictLe n), ih, hnativeEq,
          ← hstepNative]
      have hfunSucc :
          (Preorder.frestrictLe (n + 1) :
            ((t : Nat) -> Fin K × Real) ->
              History.FinitePairHistory (Fin K) Real (n + 1)) =
            (fun input :
                History.FinitePairHistory (Fin K) Real n × (Fin K × Real) =>
              History.extendPairHistorySucc input.1 input.2) ∘
              (fun x => (Preorder.frestrictLe n x, x (n + 1))) :=
        funext (frestrictLe_succ_eq_extendPairHistorySucc n)
      rw [hfunSucc,
        ← Measure.map_map History.measurable_extendPairHistorySucc hmeasPair,
        ← Measure.map_map History.measurable_extendPairHistorySucc hmeasPair,
        hjoint]

end Thompson
end
end BanditRLProof
