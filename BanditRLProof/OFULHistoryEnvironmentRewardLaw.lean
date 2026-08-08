import BanditRLProof.OFULGeneratedTrajectoryPredictableConfidence
import BanditRLProof.ConditionalExpectationReward

/-!
# Concrete history-environment reward laws for OFUL

This module connects the Markov kernels stored in `Thompson.HistoryEnvironment`
to the strict-past predictable residual law consumed by the compiled OFUL
confidence route.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u

namespace BanditRLProof
namespace OFUL

/--
For any canonical history algorithm, the time-zero reward marginal is the
environment feedback law at that algorithm's initial action.
-/
theorem
    canonicalHistoryTrajectory_initialReward_map_eq_historyAlgorithmInitialFeedback
    {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (initialAction : Fin K)
    (hinitial : algorithm.initialAction = Measure.dirac initialAction)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) :
    Measure.map (fun trajectory : Nat -> Fin K × Real => trajectory 0 |>.2)
        (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment) =
      environment.initialFeedback initialAction := by
  calc
    Measure.map (fun trajectory : Nat -> Fin K × Real => trajectory 0 |>.2)
        (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment) =
        Measure.snd
          (Measure.map (fun trajectory : Nat -> Fin K × Real => trajectory 0)
            (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment)) := by
          rw [Measure.snd]
          symm
          simpa [Function.comp_def] using
            (Measure.map_map measurable_snd (measurable_pi_apply 0))
    _ = Measure.snd (algorithm.initialAction ⊗ₘ environment.initialFeedback) := by
      congr 1
      simpa [Thompson.canonicalHistoryTrajectoryAction,
        Thompson.canonicalHistoryTrajectoryReward] using
        (Thompson.canonicalHistoryTrajectory_initialPair_map_eq
          algorithm environment)
    _ = environment.initialFeedback initialAction := by
      rw [hinitial]
      rw [Measure.snd_compProd]
      ext s hs
      rw [Measure.bind_apply hs environment.initialFeedback.aemeasurable,
        lintegral_dirac]

/--
For any canonical history algorithm, the successor reward conditioned on its
finite pair prefix has the reward marginal of the history-step kernel.
-/
theorem canonicalHistoryTrajectory_reward_succ_condDistrib_eq_historyStepReward
    {K : Nat}
    (hK : 0 < K)
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun trajectory : Nat -> Fin K × Real => (trajectory (n + 1)).2)
        (Preorder.frestrictLe n)
        (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment) =ᵐ[
      (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment).map
        (Preorder.frestrictLe n)]
      (Thompson.historyStepKernel algorithm environment n).map Prod.snd := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let nextPair : (Nat -> Fin K × Real) -> Fin K × Real :=
    fun trajectory => trajectory (n + 1)
  let history : (Nat -> Fin K × Real) ->
      History.FinitePairHistory (Fin K) Real n :=
    Preorder.frestrictLe n
  have hcomp :
      ProbabilityTheory.condDistrib (Prod.snd ∘ nextPair) history mu =ᵐ[
        mu.map history]
        (ProbabilityTheory.condDistrib nextPair history mu).map Prod.snd :=
    ProbabilityTheory.condDistrib_comp
      (μ := mu) (mβ := inferInstance) (Y := nextPair) history
      (measurable_pi_apply (n + 1)).aemeasurable
      (f := Prod.snd) measurable_snd
  have hpair :
      ProbabilityTheory.condDistrib nextPair history mu =ᵐ[mu.map history]
        Thompson.historyStepKernel algorithm environment n := by
    simpa [mu, nextPair, history,
      Thompson.canonicalHistoryTrajectoryAction,
      Thompson.canonicalHistoryTrajectoryReward] using
      (Thompson.canonicalHistoryTrajectory_step_condDistrib
        algorithm environment n)
  have hresult :
      ProbabilityTheory.condDistrib (Prod.snd ∘ nextPair) history mu =ᵐ[
        mu.map history]
        (Thompson.historyStepKernel algorithm environment n).map Prod.snd := by
    filter_upwards [hcomp, hpair] with historyValue hcompAt hpairAt
    calc
      ProbabilityTheory.condDistrib (Prod.snd ∘ nextPair) history mu
          historyValue =
          ((ProbabilityTheory.condDistrib nextPair history mu).map Prod.snd)
            historyValue := hcompAt
      _ = ((Thompson.historyStepKernel algorithm environment n).map Prod.snd)
          historyValue := by
            simpa [ProbabilityTheory.Kernel.map_apply _ measurable_snd] using
              congrArg (Measure.map Prod.snd) hpairAt
  simpa [mu, nextPair, history, Function.comp_def] using hresult

/--
Algorithm-parametric trimmed conditional-expectation reward law at successor
time for a canonical history trajectory.
-/
theorem
    canonicalHistoryTrajectory_reward_succ_condExpKernel_map_eq_historyStepReward_comap
    {K : Nat}
    (hK : 0 < K)
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    Filter.Eventually
      (fun trajectory : Nat -> Fin K × Real =>
        Measure.map (fun y : Nat -> Fin K × Real => (y (n + 1)).2)
            (ProbabilityTheory.condExpKernel
              (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment)
              ((inferInstance :
                MeasurableSpace
                  (History.FinitePairHistory (Fin K) Real n)).comap
                (Preorder.frestrictLe n))
              trajectory) =
          (Thompson.historyStepKernel algorithm environment n).map Prod.snd
            (Preorder.frestrictLe n trajectory))
      (ae ((Thompson.canonicalHistoryTrajectoryMeasure algorithm environment).trim
        ((History.measurable_finitePairHistoryOfTrace
          Thompson.canonicalHistoryTrajectoryAction
          Thompson.canonicalHistoryTrajectoryReward
          Thompson.measurable_canonicalHistoryTrajectoryAction_apply
          Thompson.measurable_canonicalHistoryTrajectoryReward_apply n).comap_le))) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  letI : ProbabilityTheory.IsMarkovKernel
      ((Thompson.historyStepKernel algorithm environment n).map Prod.snd) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map
      (Thompson.historyStepKernel algorithm environment n) measurable_snd
  have hbridge :=
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      mu
      (fun trajectory : Nat -> Fin K × Real => (trajectory (n + 1)).2)
      (Preorder.frestrictLe n)
      (measurable_snd.comp (measurable_pi_apply (n + 1)))
      (History.measurable_finitePairHistoryOfTrace
        Thompson.canonicalHistoryTrajectoryAction
        Thompson.canonicalHistoryTrajectoryReward
        Thompson.measurable_canonicalHistoryTrajectoryAction_apply
        Thompson.measurable_canonicalHistoryTrajectoryReward_apply n)
      ((Thompson.historyStepKernel algorithm environment n).map Prod.snd)
      (by
        simpa [mu] using
          canonicalHistoryTrajectory_reward_succ_condDistrib_eq_historyStepReward
            hK algorithm environment n)
  simpa only [mu] using hbridge

/--
Algorithm-parametric time-zero conditional reward law on the trivial
sigma-algebra.
-/
theorem
    canonicalHistoryTrajectory_initialReward_condExpKernel_map_eq_historyAlgorithmInitialFeedback_unitComap
    {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (initialAction : Fin K)
    (hinitial : algorithm.initialAction = Measure.dirac initialAction)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) :
    Filter.Eventually
      (fun trajectory : Nat -> Fin K × Real =>
        Measure.map (fun y : Nat -> Fin K × Real => (y 0).2)
            (ProbabilityTheory.condExpKernel
              (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment)
              ((inferInstance : MeasurableSpace Unit).comap
                (fun _trajectory : Nat -> Fin K × Real => ()))
              trajectory) =
          environment.initialFeedback initialAction)
      (ae ((Thompson.canonicalHistoryTrajectoryMeasure algorithm environment).trim
        ((show Measurable
            (fun _trajectory : Nat -> Fin K × Real => ())
          from measurable_const).comap_le))) := by
  letI : Nonempty (Fin K) := ⟨initialAction⟩
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let reward0 : (Nat -> Fin K × Real) -> Real :=
    fun trajectory => (trajectory 0).2
  let condition : (Nat -> Fin K × Real) -> Unit := fun _trajectory => ()
  let Q := environment.initialFeedback initialAction
  let kernel := ProbabilityTheory.Kernel.const Unit Q
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    infer_instance
  letI : ProbabilityTheory.IsMarkovKernel kernel := by
    dsimp [kernel]
    infer_instance
  have hreward : Measure.map reward0 mu = Q := by
    simpa [mu, reward0, Q] using
      canonicalHistoryTrajectory_initialReward_map_eq_historyAlgorithmInitialFeedback
        algorithm initialAction hinitial environment
  have hcondition_map : Measure.map condition mu = Measure.dirac () := by
    simp [condition]
  have hjoint :
      Measure.map (fun trajectory => (condition trajectory, reward0 trajectory)) mu =
        Measure.map condition mu ⊗ₘ kernel := by
    calc
      Measure.map (fun trajectory => (condition trajectory, reward0 trajectory)) mu =
          Measure.map (Prod.mk ())
            (Measure.map reward0 mu) := by
              symm
              simpa [condition, reward0, Function.comp_def] using
                (Measure.map_map measurable_prodMk_left
                  (measurable_snd.comp (measurable_pi_apply 0)))
      _ = Measure.map (Prod.mk ()) Q := by rw [hreward]
      _ = Measure.dirac () ⊗ₘ kernel := by
        simpa [kernel] using (Measure.dirac_unit_compProd_const Q).symm
      _ = Measure.map condition mu ⊗ₘ kernel := by rw [hcondition_map]
  have hcond :
      ProbabilityTheory.condDistrib reward0 condition mu =ᵐ[mu.map condition]
        kernel :=
    ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
      condition
      (measurable_snd.comp (measurable_pi_apply 0)).aemeasurable
      hjoint
  have hbridge :=
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      mu reward0 condition
      (measurable_snd.comp (measurable_pi_apply 0))
      measurable_const kernel hcond
  simpa only [mu, reward0, condition, kernel, Q,
    ProbabilityTheory.Kernel.const_apply] using hbridge

/--
For the deterministic finite-history OFUL policy, the reward marginal of the
next pair kernel is exactly the environment feedback kernel selected by the
current history.
-/
theorem finiteHistoryScalarRidge_historyStepKernel_map_snd
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R algorithmDelta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    (Thompson.historyStepKernel
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R algorithmDelta S)
        environment n).map Prod.snd history =
      environment.feedback n
        (history,
          finiteHistoryScalarRidgeOptimisticAction
            hK lambda actionFeature R algorithmDelta S n history) := by
  ext s hs
  rw [ProbabilityTheory.Kernel.map_apply _ measurable_snd,
    Measure.map_apply measurable_snd hs]
  unfold Thompson.historyStepKernel
  rw [
    ProbabilityTheory.Kernel.compProd_apply (measurable_snd hs)]
  simp only [finiteHistoryScalarRidgeOptimisticAlgorithm,
    finiteHistoryScalarRidgeOptimisticAction,
    finiteHistoryOptimisticAlgorithm_policy_apply]
  rw [lintegral_dirac]
  let selected :=
    finiteHistoryOptimisticAction hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScalarRidgeRadius
        actionFeature R algorithmDelta lambda S)
      (finiteHistoryFixedActionFeature actionFeature) n history
  change environment.feedback n (history, selected)
      (Prod.mk selected ⁻¹' (Prod.snd ⁻¹' s)) =
    environment.feedback n (history, selected) s
  have hpreimage :
      Prod.mk selected ⁻¹' (Prod.snd ⁻¹' s) = s := by
    ext reward
    rfl
  rw [hpreimage]

/-- The initial canonical reward marginal is the initial-arm feedback law. -/
theorem canonicalHistoryTrajectory_initialReward_map_eq_scalarRidgeInitialFeedback
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R algorithmDelta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) :
    Measure.map (fun trajectory : Nat -> Fin K × Real => trajectory 0 |>.2)
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R algorithmDelta S)
          environment) =
      environment.initialFeedback ⟨0, hK⟩ := by
  let algorithm :=
    finiteHistoryScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R algorithmDelta S
  calc
    Measure.map (fun trajectory : Nat -> Fin K × Real => trajectory 0 |>.2)
        (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment) =
        Measure.snd
          (Measure.map (fun trajectory : Nat -> Fin K × Real => trajectory 0)
            (Thompson.canonicalHistoryTrajectoryMeasure algorithm environment)) := by
          rw [Measure.snd]
          symm
          simpa [Function.comp_def] using
            (Measure.map_map measurable_snd (measurable_pi_apply 0))
    _ = Measure.snd (algorithm.initialAction ⊗ₘ environment.initialFeedback) := by
      congr 1
      simpa [Thompson.canonicalHistoryTrajectoryAction,
        Thompson.canonicalHistoryTrajectoryReward] using
        (Thompson.canonicalHistoryTrajectory_initialPair_map_eq
          algorithm environment)
    _ = environment.initialFeedback ⟨0, hK⟩ := by
      rw [Measure.snd_compProd]
      change environment.initialFeedback ∘ₘ Measure.dirac ⟨0, hK⟩ =
        environment.initialFeedback ⟨0, hK⟩
      ext s hs
      rw [Measure.bind_apply hs environment.initialFeedback.aemeasurable,
        lintegral_dirac]

/--
The successor canonical reward conditioned on the finite pair prefix has the
reward marginal of the concrete history step kernel.
-/
theorem canonicalHistoryTrajectory_reward_succ_condDistrib_eq_scalarRidgeStepReward
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R algorithmDelta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun trajectory : Nat -> Fin K × Real => (trajectory (n + 1)).2)
        (Preorder.frestrictLe n)
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R algorithmDelta S)
          environment) =ᵐ[
      (Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R algorithmDelta S)
        environment).map (Preorder.frestrictLe n)]
      (Thompson.historyStepKernel
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R algorithmDelta S)
        environment n).map Prod.snd := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let algorithm :=
    finiteHistoryScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R algorithmDelta S
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let nextPair : (Nat -> Fin K × Real) -> Fin K × Real :=
    fun trajectory => trajectory (n + 1)
  let history : (Nat -> Fin K × Real) ->
      History.FinitePairHistory (Fin K) Real n :=
    Preorder.frestrictLe n
  have hcomp :
      ProbabilityTheory.condDistrib (Prod.snd ∘ nextPair) history mu =ᵐ[
        mu.map history]
        (ProbabilityTheory.condDistrib nextPair history mu).map Prod.snd :=
    ProbabilityTheory.condDistrib_comp
      (μ := mu) (mβ := inferInstance) (Y := nextPair) history
      (measurable_pi_apply (n + 1)).aemeasurable
      (f := Prod.snd) measurable_snd
  have hpair :
      ProbabilityTheory.condDistrib nextPair history mu =ᵐ[mu.map history]
        Thompson.historyStepKernel algorithm environment n := by
    simpa [mu, algorithm, nextPair, history,
      Thompson.canonicalHistoryTrajectoryAction,
      Thompson.canonicalHistoryTrajectoryReward] using
      (Thompson.canonicalHistoryTrajectory_step_condDistrib
        algorithm environment n)
  have hresult :
      ProbabilityTheory.condDistrib (Prod.snd ∘ nextPair) history mu =ᵐ[
        mu.map history]
        (Thompson.historyStepKernel algorithm environment n).map Prod.snd := by
    filter_upwards [hcomp, hpair] with historyValue hcompAt hpairAt
    calc
      ProbabilityTheory.condDistrib (Prod.snd ∘ nextPair) history mu
          historyValue =
          ((ProbabilityTheory.condDistrib nextPair history mu).map Prod.snd)
            historyValue := hcompAt
      _ = ((Thompson.historyStepKernel algorithm environment n).map Prod.snd)
          historyValue := by
            simpa [ProbabilityTheory.Kernel.map_apply _ measurable_snd] using
              congrArg (Measure.map Prod.snd) hpairAt
  simpa [mu, algorithm, nextPair, history, Function.comp_def] using hresult

/--
Trimmed conditional-expectation reward law at successor time for the concrete
canonical OFUL trajectory.
-/
theorem canonicalHistoryTrajectory_reward_succ_condExpKernel_map_eq_scalarRidgeStepReward_comap
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R algorithmDelta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    Filter.Eventually
      (fun trajectory : Nat -> Fin K × Real =>
        Measure.map (fun y : Nat -> Fin K × Real => (y (n + 1)).2)
            (ProbabilityTheory.condExpKernel
              (Thompson.canonicalHistoryTrajectoryMeasure
                (finiteHistoryScalarRidgeOptimisticAlgorithm
                  hK lambda actionFeature R algorithmDelta S)
                environment)
              ((inferInstance :
                MeasurableSpace
                  (History.FinitePairHistory (Fin K) Real n)).comap
                (Preorder.frestrictLe n))
              trajectory) =
          (Thompson.historyStepKernel
            (finiteHistoryScalarRidgeOptimisticAlgorithm
              hK lambda actionFeature R algorithmDelta S)
            environment n).map Prod.snd (Preorder.frestrictLe n trajectory))
      (ae ((Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R algorithmDelta S)
        environment).trim
          ((History.measurable_finitePairHistoryOfTrace
            Thompson.canonicalHistoryTrajectoryAction
            Thompson.canonicalHistoryTrajectoryReward
            Thompson.measurable_canonicalHistoryTrajectoryAction_apply
            Thompson.measurable_canonicalHistoryTrajectoryReward_apply n).comap_le))) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let algorithm :=
    finiteHistoryScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R algorithmDelta S
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  letI : ProbabilityTheory.IsMarkovKernel
      ((Thompson.historyStepKernel algorithm environment n).map Prod.snd) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map
      (Thompson.historyStepKernel algorithm environment n) measurable_snd
  have hbridge :=
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      mu
      (fun trajectory : Nat -> Fin K × Real => (trajectory (n + 1)).2)
      (Preorder.frestrictLe n)
      (measurable_snd.comp (measurable_pi_apply (n + 1)))
      (History.measurable_finitePairHistoryOfTrace
        Thompson.canonicalHistoryTrajectoryAction
        Thompson.canonicalHistoryTrajectoryReward
        Thompson.measurable_canonicalHistoryTrajectoryAction_apply
        Thompson.measurable_canonicalHistoryTrajectoryReward_apply n)
      ((Thompson.historyStepKernel algorithm environment n).map Prod.snd)
      (by
        simpa [mu, algorithm] using
          canonicalHistoryTrajectory_reward_succ_condDistrib_eq_scalarRidgeStepReward
            hK lambda actionFeature R algorithmDelta S environment n)
  simpa only [mu, algorithm] using hbridge

/--
At time zero, conditioning on the trivial sigma-algebra leaves the canonical
initial reward law equal to the initial-arm feedback measure.
-/
theorem canonicalHistoryTrajectory_initialReward_condExpKernel_map_eq_scalarRidgeInitialFeedback_unitComap
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R algorithmDelta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) :
    Filter.Eventually
      (fun trajectory : Nat -> Fin K × Real =>
        Measure.map (fun y : Nat -> Fin K × Real => (y 0).2)
            (ProbabilityTheory.condExpKernel
              (Thompson.canonicalHistoryTrajectoryMeasure
                (finiteHistoryScalarRidgeOptimisticAlgorithm
                  hK lambda actionFeature R algorithmDelta S)
                environment)
              ((inferInstance : MeasurableSpace Unit).comap
                (fun _trajectory : Nat -> Fin K × Real => ()))
              trajectory) =
          environment.initialFeedback ⟨0, hK⟩)
      (ae ((Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R algorithmDelta S)
        environment).trim
          ((show Measurable
              (fun _trajectory : Nat -> Fin K × Real => ())
            from measurable_const).comap_le))) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let algorithm :=
    finiteHistoryScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R algorithmDelta S
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let reward0 : (Nat -> Fin K × Real) -> Real :=
    fun trajectory => (trajectory 0).2
  let condition : (Nat -> Fin K × Real) -> Unit := fun _trajectory => ()
  let Q := environment.initialFeedback ⟨0, hK⟩
  let kernel := ProbabilityTheory.Kernel.const Unit Q
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    infer_instance
  letI : ProbabilityTheory.IsMarkovKernel kernel := by
    dsimp [kernel]
    infer_instance
  have hreward : Measure.map reward0 mu = Q := by
    simpa [mu, algorithm, reward0, Q] using
      canonicalHistoryTrajectory_initialReward_map_eq_scalarRidgeInitialFeedback
        hK lambda actionFeature R algorithmDelta S environment
  have hcondition_map : Measure.map condition mu = Measure.dirac () := by
    simp [condition]
  have hjoint :
      Measure.map (fun trajectory => (condition trajectory, reward0 trajectory)) mu =
        Measure.map condition mu ⊗ₘ kernel := by
    calc
      Measure.map (fun trajectory => (condition trajectory, reward0 trajectory)) mu =
          Measure.map (Prod.mk ())
            (Measure.map reward0 mu) := by
              symm
              simpa [condition, reward0, Function.comp_def] using
                (Measure.map_map measurable_prodMk_left
                  (measurable_snd.comp (measurable_pi_apply 0)))
      _ = Measure.map (Prod.mk ()) Q := by rw [hreward]
      _ = Measure.dirac () ⊗ₘ kernel := by
        simpa [kernel] using (Measure.dirac_unit_compProd_const Q).symm
      _ = Measure.map condition mu ⊗ₘ kernel := by rw [hcondition_map]
  have hcond :
      ProbabilityTheory.condDistrib reward0 condition mu =ᵐ[mu.map condition]
        kernel :=
    ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
      condition
      (measurable_snd.comp (measurable_pi_apply 0)).aemeasurable
      hjoint
  have hbridge :=
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      mu reward0 condition
      (measurable_snd.comp (measurable_pi_apply 0))
      measurable_const kernel hcond
  simpa only [mu, algorithm, reward0, condition, kernel, Q,
    ProbabilityTheory.Kernel.const_apply] using hbridge

/--
A concrete linear reward contract on the kernels of a history environment.

The initial and successor fields are unconditional sub-Gaussian laws of each
kernel section around the linear response of the supplied action.
-/
structure CanonicalLinearSubgaussianEnvironmentLaw
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) : Prop where
  theta_norm_le : euclideanLength thetaStar <= S
  initial_reward_hasSubgaussianMGF :
    ProbabilityTheory.HasSubgaussianMGF
      (fun reward =>
        reward - dotProduct thetaStar (actionFeature ⟨0, hK⟩))
      (constantSquaredVarianceProxy R 0)
      (environment.initialFeedback ⟨0, hK⟩)
  feedback_reward_hasSubgaussianMGF : forall
      (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
      (action : Fin K),
    ProbabilityTheory.HasSubgaussianMGF
      (fun reward =>
        reward - dotProduct thetaStar (actionFeature action))
      (constantSquaredVarianceProxy R (n + 1))
      (environment.feedback n (history, action))

/--
The kernel-level linear sub-Gaussian environment contract constructs the
strict-past predictable residual law required by the OFUL confidence route.
-/
noncomputable def
    canonicalPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R algorithmDelta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    CanonicalPredictableScalarRidgeResidualLaw
      hK lambda thetaStar actionFeature R algorithmDelta S
      environment horizon where
  theta_norm_le := source.theta_norm_le
  residual_hasCondSubgaussianMGF i _hi := by
    let algorithm :=
      finiteHistoryScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R algorithmDelta S
    let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
    cases i with
    | zero =>
        let condition : (Nat -> Fin K × Real) -> Unit := fun _trajectory => ()
        let mcond :=
          (inferInstance : MeasurableSpace Unit).comap condition
        let reward0 : (Nat -> Fin K × Real) -> Real :=
          fun trajectory => (trajectory 0).2
        let center0 : (Nat -> Fin K × Real) -> Real :=
          fun _trajectory =>
            dotProduct thetaStar (actionFeature ⟨0, hK⟩)
        have hmcond :
            mcond <=
              (MeasurableSpace.pi :
                MeasurableSpace (Nat -> Fin K × Real)) := by
          exact measurable_const.comap_le
        have hrewardLaw :
            Filter.Eventually
              (fun trajectory : Nat -> Fin K × Real =>
                @Measure.map (Nat -> Fin K × Real) Real
                    MeasurableSpace.pi inferInstance reward0
                    (@ProbabilityTheory.condExpKernel
                      (Nat -> Fin K × Real) MeasurableSpace.pi _ mu _
                      mcond trajectory) =
                  environment.initialFeedback ⟨0, hK⟩)
              (ae (@Measure.trim (Nat -> Fin K × Real)
                mcond MeasurableSpace.pi mu hmcond)) := by
          simpa [mu, algorithm, mcond, condition, reward0] using
            canonicalHistoryTrajectory_initialReward_condExpKernel_map_eq_scalarRidgeInitialFeedback_unitComap
              hK lambda actionFeature R algorithmDelta S environment
        have htargetLaw :
            Filter.Eventually
              (fun _trajectory : Nat -> Fin K × Real =>
                ProbabilityTheory.HasSubgaussianMGF
                  (fun reward => reward - center0 _trajectory)
                  (constantSquaredVarianceProxy R 0)
                  (environment.initialFeedback ⟨0, hK⟩))
              (ae (@Measure.trim (Nat -> Fin K × Real)
                mcond MeasurableSpace.pi mu hmcond)) :=
          Filter.Eventually.of_forall (fun _trajectory =>
            source.initial_reward_hasSubgaussianMGF)
        have hconditional :=
          ConditionalExpectationReward.hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq
            (mOmega := MeasurableSpace.pi)
            mu mcond hmcond reward0 center0
            (constantSquaredVarianceProxy R 0)
            (measurable_snd.comp (measurable_pi_apply 0))
            measurable_const
            (fun _trajectory => environment.initialFeedback ⟨0, hK⟩)
            hrewardLaw htargetLaw
        simpa [mu, algorithm, mcond, condition, reward0, center0,
          canonicalHistoryTrajectoryPredictableResidual,
          canonicalHistoryTrajectoryResponse,
          canonicalHistoryTrajectoryPredictableFeature,
          MeasurableSpace.comap_const] using hconditional
    | succ n =>
        let history : (Nat -> Fin K × Real) ->
            History.FinitePairHistory (Fin K) Real n :=
          Preorder.frestrictLe n
        let mcond :=
          (inferInstance :
            MeasurableSpace
              (History.FinitePairHistory (Fin K) Real n)).comap history
        let response : (Nat -> Fin K × Real) -> Real :=
          fun trajectory => (trajectory (n + 1)).2
        let center : (Nat -> Fin K × Real) -> Real :=
          fun trajectory =>
            dotProduct thetaStar
              (canonicalHistoryTrajectoryPredictableFeature
                hK lambda actionFeature R algorithmDelta S
                (n + 1) trajectory)
        let stepRewardKernel :=
          (Thompson.historyStepKernel algorithm environment n).map Prod.snd
        let target : (Nat -> Fin K × Real) -> Measure Real :=
          fun trajectory => stepRewardKernel (history trajectory)
        have hmcond :
            mcond <=
              (MeasurableSpace.pi :
                MeasurableSpace (Nat -> Fin K × Real)) := by
          simpa [mcond, history] using
            (Preorder.measurable_frestrictLe
              (X := fun _ : Nat => Fin K × Real) n).comap_le
        have hcenterF :
            @Measurable (Nat -> Fin K × Real) Real
              (canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1))
              inferInstance center := by
          have hcoordinates : forall j,
              StronglyMeasurable[
                canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1)]
                (fun trajectory =>
                  canonicalHistoryTrajectoryPredictableFeature
                    hK lambda actionFeature R algorithmDelta S
                    (n + 1) trajectory j) := by
            intro j
            exact
              canonicalHistoryTrajectoryPredictableFeature_stronglyMeasurable
                hK lambda actionFeature R algorithmDelta S (n + 1) j
          have hsum :=
            Finset.stronglyMeasurable_sum
              (Finset.univ : Finset Feature) fun j _ =>
                (stronglyMeasurable_const :
                  StronglyMeasurable[
                    canonicalHistoryTrajectoryBeforeFiltration
                      (K := K) (n + 1)]
                    (fun _trajectory : Nat -> Fin K × Real =>
                      thetaStar j)).mul
                  (hcoordinates j)
          convert hsum.measurable using 1
          funext trajectory
          simp [center, dotProduct, Finset.sum_apply]
        have hfiltration :
            (canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1) :
                MeasurableSpace (Nat -> Fin K × Real)) = mcond := by
          simp [mcond, history,
            canonicalHistoryTrajectoryBeforeFiltration_succ,
            Filtration.piLE_eq_comap_frestrictLe]
        have hcenter : @Measurable (Nat -> Fin K × Real) Real
            mcond inferInstance center := by
          rw [← hfiltration]
          exact hcenterF
        have hrewardLaw :
            Filter.Eventually
              (fun trajectory : Nat -> Fin K × Real =>
                @Measure.map (Nat -> Fin K × Real) Real
                    MeasurableSpace.pi inferInstance response
                    (@ProbabilityTheory.condExpKernel
                      (Nat -> Fin K × Real) MeasurableSpace.pi _ mu _
                      mcond trajectory) =
                  target trajectory)
              (ae (@Measure.trim (Nat -> Fin K × Real)
                mcond MeasurableSpace.pi mu hmcond)) := by
          simpa [mu, algorithm, mcond, history, response, target,
            stepRewardKernel] using
            canonicalHistoryTrajectory_reward_succ_condExpKernel_map_eq_scalarRidgeStepReward_comap
              hK lambda actionFeature R algorithmDelta S environment n
        have htargetLaw :
            Filter.Eventually
              (fun trajectory : Nat -> Fin K × Real =>
                ProbabilityTheory.HasSubgaussianMGF
                  (fun reward => reward - center trajectory)
                  (constantSquaredVarianceProxy R (n + 1))
                  (target trajectory))
              (ae (@Measure.trim (Nat -> Fin K × Real)
                mcond MeasurableSpace.pi mu hmcond)) := by
          refine Filter.Eventually.of_forall (fun trajectory => ?_)
          rw [show target trajectory =
              environment.feedback n
                (history trajectory,
                  finiteHistoryScalarRidgeOptimisticAction
                    hK lambda actionFeature R algorithmDelta S n
                      (history trajectory)) by
            exact finiteHistoryScalarRidge_historyStepKernel_map_snd
              hK lambda actionFeature R algorithmDelta S environment n
                (history trajectory)]
          simpa [center, history,
            canonicalHistoryTrajectoryPredictableFeature,
            finiteHistoryScalarRidgeSelectedFeature] using
            source.feedback_reward_hasSubgaussianMGF n (history trajectory)
              (finiteHistoryScalarRidgeOptimisticAction
                hK lambda actionFeature R algorithmDelta S n
                  (history trajectory))
        have hconditional :=
          ConditionalExpectationReward.hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq
            (mOmega := MeasurableSpace.pi)
            mu mcond hmcond response center
            (constantSquaredVarianceProxy R (n + 1))
            (measurable_snd.comp (measurable_pi_apply (n + 1)))
            hcenter target hrewardLaw htargetLaw
        have hconditionalF :=
          ConditionalExpectationReward.hasCondSubgaussianMGF_congr_measurableSpace
            (mOmega := MeasurableSpace.pi) mu mcond
            (canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1))
            hmcond
            ((canonicalHistoryTrajectoryBeforeFiltration (K := K)).le (n + 1))
            hfiltration.symm
            (fun trajectory => response trajectory - center trajectory)
            (constantSquaredVarianceProxy R (n + 1)) hconditional
        simpa [mu, algorithm, response, center,
          canonicalHistoryTrajectoryPredictableResidual] using hconditionalF

/--
Concrete successor-gap tail obtained directly from a linear sub-Gaussian
`HistoryEnvironment` contract.
-/
theorem
    measure_canonicalHistoryTrajectorySumRangeSuccGapViolationSet_le_of_linearSubgaussianEnvironment
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat)
    (comparator : Nat -> Fin K)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeSuccGapViolationSet
          lambda thetaStar actionFeature R delta S horizon comparator) <=
      ENNReal.ofReal delta := by
  exact
    measure_canonicalHistoryTrajectorySumRangeSuccGapViolationSet_le_of_predictableResidualLaw
      hK lambda hlambda thetaStar actionFeature R hR delta hdelta hdelta_one
      S environment horizon comparator
      (canonicalPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
        hK lambda thetaStar actionFeature R
          (delta / ((horizon + 1 : Nat) : Real)) S
          environment horizon source)

end OFUL
end BanditRLProof
