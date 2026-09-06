import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoNthPull
import BanditRLProof.Algorithms.ThompsonStationaryReward
import BanditRLProof.Algorithms.UCBArmStreamConditionalReward

/-!
# Two-arm SGB Theorem 2: latent reward product bridge

Appendix C of Baudry--Johnson--Vary--Pike-Burke--Rebeschini treats the rewards
collected from the optimal arm in pull order.  This module exposes the safe
part of that reindexing through the existing latent arm-stream coupling.

The first `m` coordinates of one fixed arm have their finite IID product law.
The same law holds for the stream coordinate of the coupled SGB trajectory,
and every finite nth optimal-arm pull reads the corresponding latent
coordinate almost surely.  These results do not identify the coupling's
visible trajectory marginal with the native fixed-IID SGB trajectory.  They
also do not make totalized stopped rewards IID or condition on all requested
pulls occurring.  The native trajectory-law adapter and future-cylinder
producer remain separate obligations.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
noncomputable section
universe u

namespace UCB

/-- A fixed arm's first `m` latent rewards have the finite IID product law. -/
theorem armStreamMeasure_map_fixedArmFinitePrefix_eq_pi
    {K m : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) :
    Measure.map
        (fun stream : ArmRewardStream K =>
          fun i : Fin m => stream (i : Nat) arm)
        (armStreamMeasure nu) =
      Measure.pi (fun _ : Fin m => nu arm) := by
  have hindex : Function.Injective
      (fun i : Fin m => ((i : Nat), arm)) := by
    intro i j hij
    exact Fin.ext (congrArg Prod.fst hij)
  have hindep :
      iIndepFun
        (fun i : Fin m =>
          fun stream : ArmRewardStream K => stream (i : Nat) arm)
        (armStreamMeasure nu) := by
    simpa [armStreamCoordinate] using
      (ProbabilityTheory.iIndepFun.precomp hindex
        (iIndepFun_armStreamMeasure_coordinate nu))
  have hcoord : forall i : Fin m,
      AEMeasurable
        (fun stream : ArmRewardStream K => stream (i : Nat) arm)
        (armStreamMeasure nu) := fun i =>
    ((measurable_pi_apply arm).comp
      (measurable_pi_apply (i : Nat))).aemeasurable
  have hproduct :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hcoord).1 hindep
  calc
    Measure.map
        (fun stream : ArmRewardStream K =>
          fun i : Fin m => stream (i : Nat) arm)
        (armStreamMeasure nu) =
      Measure.pi (fun i : Fin m =>
        Measure.map
          (fun stream : ArmRewardStream K => stream (i : Nat) arm)
          (armStreamMeasure nu)) := by
            simpa only using hproduct
    _ = Measure.pi (fun _ : Fin m => nu arm) := by
      congr 1
      funext i
      exact armStreamMeasure_map_coord nu (i : Nat) arm

end UCB

namespace Thompson

/-- The fixed-arm product law lifted through the exact stream marginal of the
latent trajectory coupling. -/
theorem latentArmStreamTrajectoryMeasure_map_fixedArmFinitePrefix_eq_pi
    {Env : Type u} {K m : Nat} [MeasurableSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) :
    Measure.map
        (fun sample :
            UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real) =>
          fun i : Fin m => sample.1 (i : Nat) arm)
        (latentArmStreamTrajectoryMeasure algorithm env nu) =
      Measure.pi (fun _ : Fin m => nu arm) := by
  let fixedPrefix := fun stream : UCB.ArmRewardStream K =>
    fun i : Fin m => stream (i : Nat) arm
  have hfixedPrefix : Measurable fixedPrefix :=
    measurable_pi_lambda _ fun i =>
      (measurable_pi_apply arm).comp
        (measurable_pi_apply (i : Nat))
  have hfst :
      Measure.map Prod.fst
          (latentArmStreamTrajectoryMeasure algorithm env nu) =
        UCB.armStreamMeasure nu := by
    simpa using
      (identDistrib_fst_latentArmStreamTrajectoryMeasure
        algorithm env nu).map_eq
  calc
    Measure.map
        (fun sample :
            UCB.ArmRewardStream K × ((n : Nat) -> Fin K × Real) =>
          fun i : Fin m => sample.1 (i : Nat) arm)
        (latentArmStreamTrajectoryMeasure algorithm env nu) =
      Measure.map fixedPrefix
        (Measure.map Prod.fst
          (latentArmStreamTrajectoryMeasure algorithm env nu)) := by
            rw [Measure.map_map hfixedPrefix measurable_fst]
            rfl
    _ = Measure.map fixedPrefix (UCB.armStreamMeasure nu) := by
      rw [hfst]
    _ = Measure.pi (fun _ : Fin m => nu arm) := by
      exact UCB.armStreamMeasure_map_fixedArmFinitePrefix_eq_pi nu arm

end Thompson

namespace StochasticGradientBandit

/-- The latent-stream coupling specialized to the zero-initialized two-arm SGB
policy and the fixed arm laws used by the source instance. -/
noncomputable def twoArmFixedIIDLatentTrajectoryMeasure
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) :
    Measure (UCB.ArmRewardStream 2 × ((n : Nat) -> Fin 2 × Real)) := by
  letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
    UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
  exact Thompson.latentArmStreamTrajectoryMeasure
    (historyAlgorithm (fun _ : Fin 2 => 0) eta) ()
    (UCB.finiteArmRealRewardKernel armLaw)

instance instTwoArmFixedIIDLatentTrajectoryMeasureIsProbability
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) :
    IsProbabilityMeasure
      (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta) := by
  letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
    UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
  unfold twoArmFixedIIDLatentTrajectoryMeasure
  infer_instance

/-- The native `Unit`-environment law is its trajectory kernel with the trivial
environment coordinate reattached.  This is normalization for the still-open
latent-to-native trajectory adapter. -/
theorem twoArmTrajectoryMeasure_dirac_eq_map_trajectoryKernel
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) :
    twoArmTrajectoryMeasure (Measure.dirac ()) eta
        (twoArmFixedIIDEnvironment armLaw hprob) =
      Measure.map (Prod.mk ())
        (trajectoryKernel (fun _ : Fin 2 => 0) eta
          (twoArmFixedIIDEnvironment armLaw hprob) ()) := by
  simpa only [twoArmTrajectoryMeasure] using
    (Measure.dirac_unit_compProd
      (trajectoryKernel (fun _ : Fin 2 => 0) eta
        (twoArmFixedIIDEnvironment armLaw hprob)))

/-- Freezing the direct fixed-IID reward kernel at `Unit` gives the same
finite-arm kernel used by the latent-stream construction. -/
theorem stationaryRewardKernelAt_twoArmFixedIIDRewardKernel_eq
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm)) :
    letI : IsMarkovKernel (twoArmFixedIIDRewardKernel armLaw) :=
      twoArmFixedIIDRewardKernel_isMarkov armLaw hprob
    Thompson.stationaryRewardKernelAt
        (twoArmFixedIIDRewardKernel armLaw) () =
      UCB.finiteArmRealRewardKernel armLaw := by
  ext arm s hs
  simp only [Thompson.stationaryRewardKernelAt_apply,
    twoArmFixedIIDRewardKernel_apply,
    UCB.finiteArmRealRewardKernel_apply]

/-- On the specialized coupling, the first `m` latent optimal-arm rewards have
exactly the product of the source arm law. -/
theorem twoArmFixedIIDLatentTrajectoryMeasure_map_optimalPrefix_eq_pi
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (m : Nat) :
    Measure.map
        (fun sample :
            UCB.ArmRewardStream 2 × ((n : Nat) -> Fin 2 × Real) =>
          fun i : Fin m => sample.1 (i : Nat) 0)
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta) =
      Measure.pi (fun _ : Fin m => armLaw 0) := by
  letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
    UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
  simpa only [twoArmFixedIIDLatentTrajectoryMeasure,
    UCB.finiteArmRealRewardKernel_apply] using
    (Thompson.latentArmStreamTrajectoryMeasure_map_fixedArmFinitePrefix_eq_pi
      (historyAlgorithm (fun _ : Fin 2 => 0) eta) ()
      (UCB.finiteArmRealRewardKernel armLaw) (0 : Fin 2) (m := m))

/-- At every finite nth optimal-arm pull, the observed stopped reward is the
corresponding latent arm-`0` coordinate almost surely.  This is pathwise
support, not an IID statement about totalized or occurrence-conditioned
stopped rewards. -/
theorem twoArmNthOptimalPullReward_eq_latentCoordinate_ae
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (pullIndex : Nat) :
    ∀ᵐ sample ∂twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta,
      ∀ t : Nat,
        twoArmNthOptimalPullTime (Env := Unit) pullIndex ((), sample.2) =
            (t : WithTop Nat) ->
          twoArmNthOptimalPullReward (Env := Unit) pullIndex ((), sample.2) =
            sample.1 pullIndex 0 := by
  letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
    UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
  have hsupport :=
    Thompson.latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae
      (historyAlgorithm (fun _ : Fin 2 => 0) eta) ()
      (UCB.finiteArmRealRewardKernel armLaw)
  change ∀ᵐ sample ∂Thompson.latentArmStreamTrajectoryMeasure
      (historyAlgorithm (fun _ : Fin 2 => 0) eta) ()
      (UCB.finiteArmRealRewardKernel armLaw),
    ∀ t : Nat,
      twoArmNthOptimalPullTime (Env := Unit) pullIndex ((), sample.2) =
          (t : WithTop Nat) ->
        twoArmNthOptimalPullReward (Env := Unit) pullIndex ((), sample.2) =
          sample.1 pullIndex 0
  filter_upwards [hsupport] with sample hsample
  intro t htime
  have hspec := twoArmNthOptimalPullTime_spec
    (Env := Unit) pullIndex t ((), sample.2) htime
  rw [twoArmNthOptimalPullReward_eq_of_time_eq pullIndex t ((), sample.2) htime]
  have hrewards := congrFun hsample t
  change (sample.2 t).2 = sample.1 pullIndex 0
  change (sample.2 t).2 = _ at hrewards
  rw [hrewards]
  simp only [Thompson.latentArmStreamTrajectoryAction,
    Thompson.canonicalHistoryTrajectoryAction,
    UCB.rewardFromArmStream]
  have haction : (sample.2 t).1 = 0 := by
    simpa only [twoArmGeneratedAction] using hspec.2.1
  rw [haction]
  have hcount :
      pullCount (fun k => (sample.2 k).1) 0 t = pullIndex := by
    simpa only [twoArmOptimalPullCount, twoArmGeneratedAction] using hspec.1
  change sample.1 (pullCount (fun k => (sample.2 k).1) 0 t) 0 =
    sample.1 pullIndex 0
  rw [hcount]

end StochasticGradientBandit
end
end BanditRLProof
