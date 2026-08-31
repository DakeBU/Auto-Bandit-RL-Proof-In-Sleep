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

end StochasticGradientBandit
end
end BanditRLProof
