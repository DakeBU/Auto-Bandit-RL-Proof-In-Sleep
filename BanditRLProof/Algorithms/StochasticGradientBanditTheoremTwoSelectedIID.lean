import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoNativePrefix

/-!
# Two-arm SGB Theorem 2: missing-pull-aware selected-block transport

Appendix C of Baudry--Johnson--Vary--Pike-Burke--Rebeschini works with rewards
in optimal-arm pull order.  Adaptive selection makes a naive stopped-value
IID statement false as a proof interface: a requested pull can be absent, and
the event that a block of pulls occurs can itself depend on earlier rewards.

This module therefore transports the exact observable block that the native
process exposes.  Every coordinate records both the `WithTop Nat` nth-pull
time and Mathlib's stopped reward.  On the latent coupling, the reward is
replaced by the corresponding arm-stream coordinate only when the pull time
is finite; at `top` the original stopped-value fallback is retained.  The
result is an exact finite-block law on the native stationary process while
keeping the missing-pull boundary explicit.

The unmasked latent prefix still has the separately compiled product law
`twoArmFixedIIDLatentTrajectoryMeasure_map_optimalPrefix_eq_pi`.  The masked
block below is deliberately not claimed to have that product law, either
unconditionally after totalization or after conditioning on all pulls being
present.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
noncomputable section
universe u

namespace StochasticGradientBandit

private theorem twoArmHistoryEnvironment_ext
    (environment₁ environment₂ :
      Thompson.HistoryEnvironment (Fin 2) Real)
    (hfeedback : environment₁.feedback = environment₂.feedback)
    (hinitial : environment₁.initialFeedback =
      environment₂.initialFeedback) :
    environment₁ = environment₂ := by
  cases environment₁
  cases environment₂
  simp_all

/-- The first `m` optimal-arm pull records on an observable trajectory.

The time coordinate is part of the value, so `top` remains visible.  The
reward coordinate has source semantics only when that time is finite. -/
def twoArmOptimalPullTimeRewardBlock
    {Env : Type u} [MeasurableSpace Env] (m : Nat) :
    Env × ((t : Nat) -> Fin 2 × Real) ->
      ((i : Fin m) -> WithTop Nat × Real) :=
  fun sample i =>
    (twoArmNthOptimalPullTime (Env := Env) (i : Nat) sample,
      twoArmNthOptimalPullReward (Env := Env) (i : Nat) sample)

theorem measurable_twoArmOptimalPullTimeRewardBlock
    {Env : Type u} [MeasurableSpace Env] (m : Nat) :
    Measurable (twoArmOptimalPullTimeRewardBlock (Env := Env) m) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact
    (measurable_twoArmNthOptimalPullTime (Env := Env) (i : Nat)).prod
      (measurable_twoArmNthOptimalPullReward (Env := Env) (i : Nat))

/-- The latent comparison block.  A finite pull reads its corresponding
arm-`0` stream coordinate.  A missing pull retains the stopped-value fallback
rather than silently turning an absent observation into an IID reward. -/
def twoArmLatentMaskedOptimalPullBlock (m : Nat) :
    UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real) ->
      ((i : Fin m) -> WithTop Nat × Real) :=
  fun sample i =>
    let trajectorySample := ((), sample.2)
    let pullTime :=
      twoArmNthOptimalPullTime (Env := Unit) (i : Nat) trajectorySample
    let stoppedReward :=
      twoArmNthOptimalPullReward (Env := Unit) (i : Nat) trajectorySample
    (pullTime,
      if pullTime = (⊤ : WithTop Nat) then
        stoppedReward
      else
        sample.1 (i : Nat) 0)

theorem measurable_twoArmLatentMaskedOptimalPullBlock (m : Nat) :
    Measurable (twoArmLatentMaskedOptimalPullBlock m) := by
  refine measurable_pi_lambda _ fun i => ?_
  let attachUnit := fun sample :
      UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real) =>
    ((), sample.2)
  let pullTime := fun sample :
      UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real) =>
    twoArmNthOptimalPullTime (Env := Unit) (i : Nat) (attachUnit sample)
  let stoppedReward := fun sample :
      UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real) =>
    twoArmNthOptimalPullReward (Env := Unit) (i : Nat) (attachUnit sample)
  let latentReward := fun sample :
      UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real) =>
    sample.1 (i : Nat) 0
  have hattach : Measurable attachUnit :=
    measurable_const.prodMk measurable_snd
  have htime : Measurable pullTime :=
    (measurable_twoArmNthOptimalPullTime
      (Env := Unit) (i : Nat)).comp hattach
  have hstopped : Measurable stoppedReward :=
    (measurable_twoArmNthOptimalPullReward
      (Env := Unit) (i : Nat)).comp hattach
  have hlatent : Measurable latentReward :=
    (measurable_pi_apply 0).comp
      ((measurable_pi_apply (i : Nat)).comp measurable_fst)
  have htop : MeasurableSet {sample | pullTime sample = (⊤ : WithTop Nat)} :=
    measurableSet_eq_fun htime measurable_const
  exact htime.prod (Measurable.ite htop hstopped hlatent)

/-- On the latent coupling, the observable finite pull block agrees almost
surely with the missing-pull-aware latent block. -/
theorem twoArmOptimalPullTimeRewardBlock_eq_latentMasked_ae
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (m : Nat) :
    (fun sample : UCB.ArmRewardStream 2 ×
        ((t : Nat) -> Fin 2 × Real) =>
      twoArmOptimalPullTimeRewardBlock (Env := Unit) m ((), sample.2)) =ᵐ[
        twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta]
      twoArmLatentMaskedOptimalPullBlock m := by
  have hcoordinate : forall i : Fin m,
      (fun sample : UCB.ArmRewardStream 2 ×
          ((t : Nat) -> Fin 2 × Real) =>
        twoArmOptimalPullTimeRewardBlock (Env := Unit) m ((), sample.2) i) =ᵐ[
          twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta]
        (fun sample => twoArmLatentMaskedOptimalPullBlock m sample i) := by
    intro i
    filter_upwards [twoArmNthOptimalPullReward_eq_latentCoordinate_ae
      armLaw hprob eta (i : Nat)] with sample hreadout
    let trajectorySample : Unit × ((t : Nat) -> Fin 2 × Real) :=
      ((), sample.2)
    let pullTime :=
      twoArmNthOptimalPullTime (Env := Unit) (i : Nat) trajectorySample
    change
      (pullTime,
          twoArmNthOptimalPullReward (Env := Unit) (i : Nat)
            trajectorySample) =
        (pullTime,
          if pullTime = (⊤ : WithTop Nat) then
            twoArmNthOptimalPullReward (Env := Unit) (i : Nat)
              trajectorySample
          else
            sample.1 (i : Nat) 0)
    apply Prod.ext
    · rfl
    · by_cases htop : pullTime = (⊤ : WithTop Nat)
      · simp [htop]
      · simp only [htop, ↓reduceIte]
        apply hreadout (pullTime.untop htop)
        exact (WithTop.coe_untop pullTime htop).symm
  filter_upwards [ae_all_iff.2 hcoordinate] with sample hsample
  funext i
  exact hsample i

/-- Exact finite selected-block law on the native stationary fixed-IID SGB
process.  The right side is a masked latent-coupling law, not a product law;
this retained dependence is what makes the statement valid under adaptive
selection and possible missing pulls. -/
theorem twoArmNativeOptimalPullTimeRewardBlock_map_eq_latentMasked
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (m : Nat) :
    letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
      UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
    Measure.map
        (fun trajectory : (t : Nat) -> Fin 2 × Real =>
          twoArmOptimalPullTimeRewardBlock (Env := Unit) m ((), trajectory))
        (Thompson.nativeStationaryTrajectoryMeasure
          (historyAlgorithm (fun _ : Fin 2 => 0) eta)
          (UCB.finiteArmRealRewardKernel armLaw)) =
      Measure.map (twoArmLatentMaskedOptimalPullBlock m)
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta) := by
  letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
    UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
  let algorithm := historyAlgorithm (fun _ : Fin 2 => 0) eta
  let nu := UCB.finiteArmRealRewardKernel armLaw
  let coupling := twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta
  let observable := fun trajectory : (t : Nat) -> Fin 2 × Real =>
    twoArmOptimalPullTimeRewardBlock (Env := Unit) m ((), trajectory)
  have hobservable : Measurable observable :=
    (measurable_twoArmOptimalPullTimeRewardBlock
      (Env := Unit) m).comp (measurable_const.prodMk measurable_id)
  have hnative : coupling.map Prod.snd =
      Thompson.nativeStationaryTrajectoryMeasure algorithm nu := by
    simpa [coupling, algorithm, nu,
      twoArmFixedIIDLatentTrajectoryMeasure] using
      (Thompson.latentArmStreamVisibleTrajectoryMeasure_eq_native
        algorithm () nu)
  have hreadout :
      (fun sample : UCB.ArmRewardStream 2 ×
          ((t : Nat) -> Fin 2 × Real) => observable sample.2) =ᵐ[coupling]
        twoArmLatentMaskedOptimalPullBlock m := by
    simpa [coupling, observable] using
      (twoArmOptimalPullTimeRewardBlock_eq_latentMasked_ae
        armLaw hprob eta m)
  calc
    Measure.map observable
        (Thompson.nativeStationaryTrajectoryMeasure algorithm nu) =
        Measure.map observable (coupling.map Prod.snd) := by rw [hnative]
    _ = Measure.map (fun sample => observable sample.2) coupling := by
      rw [Measure.map_map hobservable measurable_snd]
      rfl
    _ = Measure.map (twoArmLatentMaskedOptimalPullBlock m) coupling :=
      Measure.map_congr hreadout

/-- The source-shaped `Unit`-environment trajectory measure has the same
observable marginal as the native stationary history construction. -/
theorem twoArmFixedIIDTrajectoryMeasure_map_snd_eq_nativeStationary
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) :
    letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
      UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
    (twoArmTrajectoryMeasure (Measure.dirac ()) eta
        (twoArmFixedIIDEnvironment armLaw hprob)).map Prod.snd =
      Thompson.nativeStationaryTrajectoryMeasure
        (historyAlgorithm (fun _ : Fin 2 => 0) eta)
        (UCB.finiteArmRealRewardKernel armLaw) := by
  letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
    UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
  let algorithm := historyAlgorithm (fun _ : Fin 2 => 0) eta
  let nu := UCB.finiteArmRealRewardKernel armLaw
  let environment := twoArmFixedIIDEnvironment armLaw hprob
  have hkernel :
      trajectoryKernel (fun _ : Fin 2 => 0) eta environment () =
        Thompson.canonicalHistoryTrajectoryMeasure algorithm
          (environment.at ()) := by
    simpa [algorithm, trajectoryKernel] using
      (Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical
        algorithm environment ())
  have henvironment : environment.at () =
      Thompson.stationaryRewardHistoryEnvironment nu := by
    apply twoArmHistoryEnvironment_ext
    · funext n
      ext input s hs
      change (twoArmFixedIIDRewardKernel armLaw ((), input.2)) s =
        (UCB.finiteArmRealRewardKernel armLaw input.2) s
      rw [twoArmFixedIIDRewardKernel_apply,
        UCB.finiteArmRealRewardKernel_apply]
    · ext arm s hs
      change (twoArmFixedIIDRewardKernel armLaw ((), arm)) s =
        (UCB.finiteArmRealRewardKernel armLaw arm) s
      rw [twoArmFixedIIDRewardKernel_apply,
        UCB.finiteArmRealRewardKernel_apply]
  calc
    (twoArmTrajectoryMeasure (Measure.dirac ()) eta environment).map Prod.snd =
        (Measure.map (Prod.mk ())
          (trajectoryKernel (fun _ : Fin 2 => 0) eta environment ())).map
            Prod.snd := by
      rw [twoArmTrajectoryMeasure_dirac_eq_map_trajectoryKernel]
    _ = trajectoryKernel (fun _ : Fin 2 => 0) eta environment () := by
      let attachUnit := fun trajectory : (t : Nat) -> Fin 2 × Real =>
        ((), trajectory)
      have hattach : Measurable attachUnit :=
        measurable_const.prodMk measurable_id
      change Measure.map Prod.snd
        (Measure.map attachUnit
          (trajectoryKernel (fun _ : Fin 2 => 0) eta environment ())) = _
      rw [Measure.map_map measurable_snd hattach]
      simp [attachUnit, Function.comp_def]
    _ = Thompson.canonicalHistoryTrajectoryMeasure algorithm
          (environment.at ()) := hkernel
    _ = Thompson.canonicalHistoryTrajectoryMeasure algorithm
          (Thompson.stationaryRewardHistoryEnvironment nu) := by
      rw [henvironment]
    _ = Thompson.nativeStationaryTrajectoryMeasure algorithm nu := rfl

/-- Source-facing finite selected-block transport on the actual generated
two-arm trajectory measure.  Missing pulls remain visible in the `WithTop`
time coordinates; the theorem does not promote the masked block to IID. -/
theorem twoArmFixedIIDTrajectoryMeasure_map_optimalPullTimeRewardBlock_eq_latentMasked
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (m : Nat) :
    Measure.map (twoArmOptimalPullTimeRewardBlock (Env := Unit) m)
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob)) =
      Measure.map (twoArmLatentMaskedOptimalPullBlock m)
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta) := by
  letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
    UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
  let sourceMeasure := twoArmTrajectoryMeasure (Measure.dirac ()) eta
    (twoArmFixedIIDEnvironment armLaw hprob)
  let observable := fun trajectory : (t : Nat) -> Fin 2 × Real =>
    twoArmOptimalPullTimeRewardBlock (Env := Unit) m ((), trajectory)
  have hobservable : Measurable observable :=
    (measurable_twoArmOptimalPullTimeRewardBlock
      (Env := Unit) m).comp (measurable_const.prodMk measurable_id)
  have hfactor :
      twoArmOptimalPullTimeRewardBlock (Env := Unit) m =
        observable ∘ Prod.snd := by
    funext sample
    rcases sample with ⟨envUnit, trajectory⟩
    cases envUnit
    rfl
  calc
    Measure.map (twoArmOptimalPullTimeRewardBlock (Env := Unit) m)
        sourceMeasure =
        Measure.map observable (sourceMeasure.map Prod.snd) := by
      rw [hfactor, Measure.map_map hobservable measurable_snd]
    _ = Measure.map observable
          (Thompson.nativeStationaryTrajectoryMeasure
            (historyAlgorithm (fun _ : Fin 2 => 0) eta)
            (UCB.finiteArmRealRewardKernel armLaw)) := by
      rw [twoArmFixedIIDTrajectoryMeasure_map_snd_eq_nativeStationary]
    _ = Measure.map (twoArmLatentMaskedOptimalPullBlock m)
          (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta) := by
      simpa [observable] using
        (twoArmNativeOptimalPullTimeRewardBlock_map_eq_latentMasked
          armLaw hprob eta m)

/-! ## Appendix-C phase event with an explicit occurrence boundary -/

/-- The running reward sum inside Appendix C's recovery phase.

The index `k : Fin (n1 + 1)` permits every prefix length from `0` through
`n1`.  The ambient reward block contains the unlucky phase of length `n0`
followed by the recovery phase of length `n1`. -/
def twoArmAppendixCPhaseOnePrefixSum (n0 n1 : Nat)
    (rewardBlock : Fin (n0 + n1) -> Real) (k : Fin (n1 + 1)) : Real :=
  ∑ i : Fin (k : Nat),
    rewardBlock ⟨n0 + (i : Nat), by omega⟩

theorem measurable_twoArmAppendixCPhaseOnePrefixSum
    (n0 n1 : Nat) (k : Fin (n1 + 1)) :
    Measurable (fun rewardBlock : Fin (n0 + n1) -> Real =>
      twoArmAppendixCPhaseOnePrefixSum n0 n1 rewardBlock k) := by
  refine Finset.measurable_sum Finset.univ fun i _ => ?_
  let j : Fin (n0 + n1) := ⟨n0 + (i : Nat), by omega⟩
  exact measurable_pi_apply j

/-- The exact finite reward event used by the two phases in Appendix C.

Phase `S0` consists of `n0` rewards equal to `-1`.  Phase `S1` consists only
of `{-1, 1}` rewards, has the specified exact terminal sum, and has running
sum at most zero at every prefix.  The later arithmetic layer will instantiate
`phaseOneTotal` with the rounded Rademacher count selected by the source; this
definition itself contains no probability or IID premise. -/
def twoArmAppendixCRewardPhaseEvent (n0 n1 : Nat)
    (phaseOneTotal : Real) : Set (Fin (n0 + n1) -> Real) :=
  {rewardBlock |
    (forall i : Fin n0,
      rewardBlock (Fin.castAdd n1 i) = -1) /\
    (forall i : Fin n1,
      rewardBlock (Fin.natAdd n0 i) = -1 \/
        rewardBlock (Fin.natAdd n0 i) = 1) /\
    twoArmAppendixCPhaseOnePrefixSum n0 n1 rewardBlock (Fin.last n1) =
      phaseOneTotal /\
    (forall k : Fin (n1 + 1),
      twoArmAppendixCPhaseOnePrefixSum n0 n1 rewardBlock k <= 0)}

theorem measurableSet_twoArmAppendixCRewardPhaseEvent
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    MeasurableSet
      (twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal) := by
  have hphaseZero : MeasurableSet
      {rewardBlock : Fin (n0 + n1) -> Real |
        forall i : Fin n0,
          rewardBlock (Fin.castAdd n1 i) = -1} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_eq_fun (measurable_pi_apply (Fin.castAdd n1 i))
        measurable_const
  have hphaseOneSupport : MeasurableSet
      {rewardBlock : Fin (n0 + n1) -> Real |
        forall i : Fin n1,
          rewardBlock (Fin.natAdd n0 i) = -1 \/
            rewardBlock (Fin.natAdd n0 i) = 1} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun i => ?_
    simpa only [Set.setOf_or] using
      (measurableSet_eq_fun (measurable_pi_apply (Fin.natAdd n0 i))
        measurable_const).union
      (measurableSet_eq_fun (measurable_pi_apply (Fin.natAdd n0 i))
        measurable_const)
  have hphaseOneTotal : MeasurableSet
      {rewardBlock : Fin (n0 + n1) -> Real |
        twoArmAppendixCPhaseOnePrefixSum n0 n1 rewardBlock (Fin.last n1) =
          phaseOneTotal} :=
    measurableSet_eq_fun
      (measurable_twoArmAppendixCPhaseOnePrefixSum n0 n1 (Fin.last n1))
      measurable_const
  have hballot : MeasurableSet
      {rewardBlock : Fin (n0 + n1) -> Real |
        forall k : Fin (n1 + 1),
          twoArmAppendixCPhaseOnePrefixSum n0 n1 rewardBlock k <= 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun k =>
      measurableSet_le
        (measurable_twoArmAppendixCPhaseOnePrefixSum n0 n1 k)
        measurable_const
  simpa only [twoArmAppendixCRewardPhaseEvent, Set.setOf_and] using
    hphaseZero.inter
      (hphaseOneSupport.inter (hphaseOneTotal.inter hballot))

/-- Every requested optimal-arm pull in a finite block has occurred.

This set is kept separate from the reward pattern because occurrence depends
on the adaptive trajectory. -/
def twoArmAppendixCAllPullsPresent (m : Nat) :
    Set ((i : Fin m) -> WithTop Nat × Real) :=
  {block | forall i : Fin m, (block i).1 ≠ (⊤ : WithTop Nat)}

theorem measurableSet_twoArmAppendixCAllPullsPresent (m : Nat) :
    MeasurableSet (twoArmAppendixCAllPullsPresent m) := by
  rw [twoArmAppendixCAllPullsPresent, Set.setOf_forall]
  refine MeasurableSet.iInter fun i => ?_
  have heq : MeasurableSet
      {block : (j : Fin m) -> WithTop Nat × Real |
        (block i).1 = (⊤ : WithTop Nat)} :=
    measurableSet_eq_fun
      (measurable_fst.comp (measurable_pi_apply i)) measurable_const
  simpa only [Set.compl_setOf] using heq.compl

/-- Observable Appendix-C phase event on a pull-time/reward block.

It requires the full block to occur and only then reads the phase reward
pattern. -/
def twoArmAppendixCObservedPhaseEvent (n0 n1 : Nat)
    (phaseOneTotal : Real) :
    Set ((i : Fin (n0 + n1)) -> WithTop Nat × Real) :=
  twoArmAppendixCAllPullsPresent (n0 + n1) ∩
    (fun block i => (block i).2) ⁻¹'
      twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal

theorem measurableSet_twoArmAppendixCObservedPhaseEvent
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    MeasurableSet
      (twoArmAppendixCObservedPhaseEvent n0 n1 phaseOneTotal) := by
  apply (measurableSet_twoArmAppendixCAllPullsPresent (n0 + n1)).inter
  exact (measurableSet_twoArmAppendixCRewardPhaseEvent
    n0 n1 phaseOneTotal).preimage
      (measurable_pi_lambda _ fun i =>
        measurable_snd.comp (measurable_pi_apply i))

/-- The latent Appendix-C event without occurrence conditioning.

The first conjunct still depends on the generated visible trajectory and says
that all requested pulls occur.  The second conjunct reads the unconditional
latent arm-`0` stream.  Keeping both in the same event avoids the invalid step
of declaring the reward block IID after conditioning on occurrence. -/
def twoArmAppendixCLatentPhaseEvent (n0 n1 : Nat)
    (phaseOneTotal : Real) : Set
      (UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real)) :=
  (twoArmLatentMaskedOptimalPullBlock (n0 + n1)) ⁻¹'
      twoArmAppendixCAllPullsPresent (n0 + n1) ∩
    (fun sample : UCB.ArmRewardStream 2 ×
        ((t : Nat) -> Fin 2 × Real) =>
      fun i : Fin (n0 + n1) => sample.1 (i : Nat) 0) ⁻¹'
      twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal

theorem measurableSet_twoArmAppendixCLatentPhaseEvent
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    MeasurableSet
      (twoArmAppendixCLatentPhaseEvent n0 n1 phaseOneTotal) := by
  apply ((measurableSet_twoArmAppendixCAllPullsPresent
    (n0 + n1)).preimage
      (measurable_twoArmLatentMaskedOptimalPullBlock (n0 + n1))).inter
  exact (measurableSet_twoArmAppendixCRewardPhaseEvent
    n0 n1 phaseOneTotal).preimage
      (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply 0).comp
          ((measurable_pi_apply (i : Nat)).comp measurable_fst))

/-- On the all-pulls-present boundary, the masked block reads exactly the
latent arm-`0` prefix. -/
theorem twoArmLatentMaskedOptimalPullBlock_preimage_appendixCObservedPhaseEvent
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    (twoArmLatentMaskedOptimalPullBlock (n0 + n1)) ⁻¹'
        twoArmAppendixCObservedPhaseEvent n0 n1 phaseOneTotal =
      twoArmAppendixCLatentPhaseEvent n0 n1 phaseOneTotal := by
  ext sample
  constructor
  · rintro ⟨hpresent, hphase⟩
    refine ⟨hpresent, ?_⟩
    have hpresent' : forall i : Fin (n0 + n1),
        (twoArmLatentMaskedOptimalPullBlock (n0 + n1) sample i).1 ≠
          (⊤ : WithTop Nat) := by
      simpa only [twoArmAppendixCAllPullsPresent,
        Set.mem_setOf_eq] using hpresent
    have hreadout :
        (fun i : Fin (n0 + n1) =>
          (twoArmLatentMaskedOptimalPullBlock (n0 + n1) sample i).2) =
        (fun i : Fin (n0 + n1) => sample.1 (i : Nat) 0) := by
      funext i
      have htime :
          twoArmNthOptimalPullTime (Env := Unit) (i : Nat) ((), sample.2) ≠
            (⊤ : WithTop Nat) := by
        simpa [twoArmLatentMaskedOptimalPullBlock] using hpresent' i
      simp [twoArmLatentMaskedOptimalPullBlock, htime]
    change (fun i : Fin (n0 + n1) => sample.1 (i : Nat) 0) ∈
      twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal
    change (fun i : Fin (n0 + n1) =>
      (twoArmLatentMaskedOptimalPullBlock (n0 + n1) sample i).2) ∈
        twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal at hphase
    rw [← hreadout]
    exact hphase
  · rintro ⟨hpresent, hphase⟩
    refine ⟨hpresent, ?_⟩
    have hpresent' : forall i : Fin (n0 + n1),
        (twoArmLatentMaskedOptimalPullBlock (n0 + n1) sample i).1 ≠
          (⊤ : WithTop Nat) := by
      simpa only [twoArmAppendixCAllPullsPresent,
        Set.mem_setOf_eq] using hpresent
    have hreadout :
        (fun i : Fin (n0 + n1) =>
          (twoArmLatentMaskedOptimalPullBlock (n0 + n1) sample i).2) =
        (fun i : Fin (n0 + n1) => sample.1 (i : Nat) 0) := by
      funext i
      have htime :
          twoArmNthOptimalPullTime (Env := Unit) (i : Nat) ((), sample.2) ≠
            (⊤ : WithTop Nat) := by
        simpa [twoArmLatentMaskedOptimalPullBlock] using hpresent' i
      simp [twoArmLatentMaskedOptimalPullBlock, htime]
    change (fun i : Fin (n0 + n1) =>
      (twoArmLatentMaskedOptimalPullBlock (n0 + n1) sample i).2) ∈
        twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal
    change (fun i : Fin (n0 + n1) => sample.1 (i : Nat) 0) ∈
      twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal at hphase
    rw [hreadout]
    exact hphase

/-- Source-shaped generated-process event corresponding to the finite
Appendix-C pull-ordered phase. -/
def twoArmAppendixCGeneratedPhaseEvent (n0 n1 : Nat)
    (phaseOneTotal : Real) :
    Set (Unit × ((t : Nat) -> Fin 2 × Real)) :=
  (twoArmOptimalPullTimeRewardBlock (Env := Unit) (n0 + n1)) ⁻¹'
    twoArmAppendixCObservedPhaseEvent n0 n1 phaseOneTotal

theorem measurableSet_twoArmAppendixCGeneratedPhaseEvent
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    MeasurableSet
      (twoArmAppendixCGeneratedPhaseEvent n0 n1 phaseOneTotal) :=
  (measurableSet_twoArmAppendixCObservedPhaseEvent
    n0 n1 phaseOneTotal).preimage
      (measurable_twoArmOptimalPullTimeRewardBlock
        (Env := Unit) (n0 + n1))

/-- Exact transport of the finite Appendix-C phase event to the source-shaped
generated SGB trajectory.

The right side is an intersection of the latent reward pattern with the
adaptive all-pulls-present event.  This theorem does not assert a product law,
selected IID, a probability lower bound, future no-return, or Theorem 2. -/
theorem twoArmFixedIIDTrajectoryMeasure_appendixCGeneratedPhaseEvent_eq_latent
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (n0 n1 : Nat) (phaseOneTotal : Real) :
    (twoArmTrajectoryMeasure (Measure.dirac ()) eta
        (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmAppendixCGeneratedPhaseEvent n0 n1 phaseOneTotal) =
      (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
        (twoArmAppendixCLatentPhaseEvent n0 n1 phaseOneTotal) := by
  let sourceMeasure := twoArmTrajectoryMeasure (Measure.dirac ()) eta
    (twoArmFixedIIDEnvironment armLaw hprob)
  let coupling := twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta
  let observable :=
    twoArmOptimalPullTimeRewardBlock (Env := Unit) (n0 + n1)
  let masked := twoArmLatentMaskedOptimalPullBlock (n0 + n1)
  let event := twoArmAppendixCObservedPhaseEvent n0 n1 phaseOneTotal
  have hobservable : Measurable observable :=
    measurable_twoArmOptimalPullTimeRewardBlock
      (Env := Unit) (n0 + n1)
  have hmasked : Measurable masked :=
    measurable_twoArmLatentMaskedOptimalPullBlock (n0 + n1)
  have hevent : MeasurableSet event :=
    measurableSet_twoArmAppendixCObservedPhaseEvent
      n0 n1 phaseOneTotal
  calc
    sourceMeasure
        (twoArmAppendixCGeneratedPhaseEvent n0 n1 phaseOneTotal) =
        Measure.map observable sourceMeasure event := by
      rw [Measure.map_apply hobservable hevent]
      rfl
    _ = Measure.map masked coupling event := by
      rw [twoArmFixedIIDTrajectoryMeasure_map_optimalPullTimeRewardBlock_eq_latentMasked]
    _ = coupling (masked ⁻¹' event) :=
      Measure.map_apply hmasked hevent
    _ = coupling
        (twoArmAppendixCLatentPhaseEvent n0 n1 phaseOneTotal) := by
      rw [twoArmLatentMaskedOptimalPullBlock_preimage_appendixCObservedPhaseEvent]

/-! ## Missing-pull/all-present probability split -/

/-- The pure latent Appendix-C reward pattern, before intersecting it with the
adaptive event that all requested optimal-arm pulls occur. -/
def twoArmAppendixCPureLatentRewardEvent (n0 n1 : Nat)
    (phaseOneTotal : Real) : Set
      (UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real)) :=
  (fun sample : UCB.ArmRewardStream 2 ×
      ((t : Nat) -> Fin 2 × Real) =>
    fun i : Fin (n0 + n1) => sample.1 (i : Nat) 0) ⁻¹'
    twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal

theorem measurableSet_twoArmAppendixCPureLatentRewardEvent
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    MeasurableSet
      (twoArmAppendixCPureLatentRewardEvent n0 n1 phaseOneTotal) :=
  (measurableSet_twoArmAppendixCRewardPhaseEvent
    n0 n1 phaseOneTotal).preimage
      (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply 0).comp
          ((measurable_pi_apply (i : Nat)).comp measurable_fst))

/-- The pure latent reward pattern together with failure of at least one
requested optimal-arm pull to occur.  This is the complementary branch to the
existing all-present latent phase event, not yet a fixed-cutoff starvation
event. -/
def twoArmAppendixCMissingPullLatentPhaseEvent (n0 n1 : Nat)
    (phaseOneTotal : Real) : Set
      (UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real)) :=
  ((twoArmLatentMaskedOptimalPullBlock (n0 + n1)) ⁻¹'
      twoArmAppendixCAllPullsPresent (n0 + n1))ᶜ ∩
    twoArmAppendixCPureLatentRewardEvent n0 n1 phaseOneTotal

theorem measurableSet_twoArmAppendixCMissingPullLatentPhaseEvent
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    MeasurableSet
      (twoArmAppendixCMissingPullLatentPhaseEvent
        n0 n1 phaseOneTotal) :=
  (((measurableSet_twoArmAppendixCAllPullsPresent
    (n0 + n1)).preimage
      (measurable_twoArmLatentMaskedOptimalPullBlock
        (n0 + n1))).compl).inter
    (measurableSet_twoArmAppendixCPureLatentRewardEvent
      n0 n1 phaseOneTotal)

/-- Membership in the missing branch exposes an actual `WithTop.top` pull-time
coordinate while retaining the pure latent reward pattern. -/
theorem mem_twoArmAppendixCMissingPullLatentPhaseEvent_iff
    (n0 n1 : Nat) (phaseOneTotal : Real)
    (sample : UCB.ArmRewardStream 2 × ((t : Nat) -> Fin 2 × Real)) :
    sample ∈ twoArmAppendixCMissingPullLatentPhaseEvent
        n0 n1 phaseOneTotal ↔
      (fun i : Fin (n0 + n1) => sample.1 (i : Nat) 0) ∈
          twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal ∧
        ∃ i : Fin (n0 + n1),
          twoArmNthOptimalPullTime (Env := Unit) (i : Nat) ((), sample.2) =
            (⊤ : WithTop Nat) := by
  classical
  simp [twoArmAppendixCMissingPullLatentPhaseEvent,
    twoArmAppendixCPureLatentRewardEvent,
    twoArmAppendixCAllPullsPresent,
    twoArmLatentMaskedOptimalPullBlock,
    and_comm]

/-- The unconditional latent reward event is exactly the union of the
all-present phase and the missing-pull phase. -/
theorem twoArmAppendixCPureLatentRewardEvent_eq_union_phase_missing
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    twoArmAppendixCPureLatentRewardEvent n0 n1 phaseOneTotal =
      twoArmAppendixCLatentPhaseEvent n0 n1 phaseOneTotal ∪
        twoArmAppendixCMissingPullLatentPhaseEvent
          n0 n1 phaseOneTotal := by
  ext sample
  by_cases hpresent :
      twoArmLatentMaskedOptimalPullBlock (n0 + n1) sample ∈
        twoArmAppendixCAllPullsPresent (n0 + n1)
  · simp [twoArmAppendixCPureLatentRewardEvent,
      twoArmAppendixCLatentPhaseEvent,
      twoArmAppendixCMissingPullLatentPhaseEvent, hpresent]
  · simp [twoArmAppendixCPureLatentRewardEvent,
      twoArmAppendixCLatentPhaseEvent,
      twoArmAppendixCMissingPullLatentPhaseEvent, hpresent]

theorem disjoint_twoArmAppendixCLatentPhaseEvent_missing
    (n0 n1 : Nat) (phaseOneTotal : Real) :
    Disjoint
      (twoArmAppendixCLatentPhaseEvent n0 n1 phaseOneTotal)
      (twoArmAppendixCMissingPullLatentPhaseEvent
        n0 n1 phaseOneTotal) := by
  rw [Set.disjoint_left]
  intro sample hphase hmissing
  exact hmissing.1 hphase.1

/-- The pure latent phase probability is evaluated under the already compiled
finite arm-0 product law. -/
theorem twoArmFixedIIDLatentTrajectoryMeasure_purePhaseEvent_eq_pi
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (n0 n1 : Nat) (phaseOneTotal : Real) :
    (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
        (twoArmAppendixCPureLatentRewardEvent n0 n1 phaseOneTotal) =
      (Measure.pi (fun _ : Fin (n0 + n1) => armLaw 0) :
          Measure (Fin (n0 + n1) -> Real))
        (twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal) := by
  let latentPrefix := fun sample : UCB.ArmRewardStream 2 ×
      ((t : Nat) -> Fin 2 × Real) =>
    fun i : Fin (n0 + n1) => sample.1 (i : Nat) 0
  have hprefix : Measurable latentPrefix :=
    measurable_pi_lambda _ fun i =>
      (measurable_pi_apply 0).comp
        ((measurable_pi_apply (i : Nat)).comp measurable_fst)
  have hevent : MeasurableSet
      (twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal) :=
    measurableSet_twoArmAppendixCRewardPhaseEvent
      n0 n1 phaseOneTotal
  calc
    (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
        (twoArmAppendixCPureLatentRewardEvent n0 n1 phaseOneTotal) =
        Measure.map latentPrefix
          (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
          (twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal) := by
      rw [Measure.map_apply hprefix hevent]
      rfl
    _ = (Measure.pi (fun _ : Fin (n0 + n1) => armLaw 0) :
            Measure (Fin (n0 + n1) -> Real))
          (twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal) := by
      rw [twoArmFixedIIDLatentTrajectoryMeasure_map_optimalPrefix_eq_pi]

/-- Probability additivity for the disjoint all-present and missing-pull
branches of the pure latent phase event. -/
theorem twoArmFixedIIDLatentTrajectoryMeasure_purePhaseEvent_eq_phase_add_missing
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (n0 n1 : Nat) (phaseOneTotal : Real) :
    (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
        (twoArmAppendixCPureLatentRewardEvent n0 n1 phaseOneTotal) =
      (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
          (twoArmAppendixCLatentPhaseEvent n0 n1 phaseOneTotal) +
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
          (twoArmAppendixCMissingPullLatentPhaseEvent
            n0 n1 phaseOneTotal) := by
  rw [twoArmAppendixCPureLatentRewardEvent_eq_union_phase_missing]
  exact measure_union
    (disjoint_twoArmAppendixCLatentPhaseEvent_missing
      n0 n1 phaseOneTotal)
    (measurableSet_twoArmAppendixCMissingPullLatentPhaseEvent
      n0 n1 phaseOneTotal)

/-- Source-facing missing-pull/all-present dichotomy.

The unconditional product-law probability of the pure finite reward phase is
the sum of the generated all-present phase probability and the latent
missing-pull branch probability.  This theorem does not identify the missing
branch with a fixed-cutoff starvation event, condition rewards on occurrence,
or prove a positive phase bound, future no-return, ballot asymptotics, or
Theorem 2. -/
theorem twoArmAppendixCRewardPhaseProbability_eq_generated_add_missing
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (n0 n1 : Nat) (phaseOneTotal : Real) :
    (Measure.pi (fun _ : Fin (n0 + n1) => armLaw 0) :
        Measure (Fin (n0 + n1) -> Real))
        (twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal) =
      (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
          (twoArmAppendixCGeneratedPhaseEvent n0 n1 phaseOneTotal) +
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
          (twoArmAppendixCMissingPullLatentPhaseEvent
            n0 n1 phaseOneTotal) := by
  calc
    (Measure.pi (fun _ : Fin (n0 + n1) => armLaw 0) :
        Measure (Fin (n0 + n1) -> Real))
        (twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal) =
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
          (twoArmAppendixCPureLatentRewardEvent
            n0 n1 phaseOneTotal) :=
      (twoArmFixedIIDLatentTrajectoryMeasure_purePhaseEvent_eq_pi
        armLaw hprob eta n0 n1 phaseOneTotal).symm
    _ = (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
          (twoArmAppendixCLatentPhaseEvent n0 n1 phaseOneTotal) +
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
          (twoArmAppendixCMissingPullLatentPhaseEvent
            n0 n1 phaseOneTotal) :=
      twoArmFixedIIDLatentTrajectoryMeasure_purePhaseEvent_eq_phase_add_missing
        armLaw hprob eta n0 n1 phaseOneTotal
    _ = (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
          (twoArmAppendixCGeneratedPhaseEvent n0 n1 phaseOneTotal) +
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta)
          (twoArmAppendixCMissingPullLatentPhaseEvent
            n0 n1 phaseOneTotal) := by
      rw [twoArmFixedIIDTrajectoryMeasure_appendixCGeneratedPhaseEvent_eq_latent]

end StochasticGradientBandit
end
end BanditRLProof
