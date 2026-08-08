import BanditRLProof.OFULScheduledBlockStartForcedPositiveActionCostBudgetExhaustionExpectedRegret

/-!
# Concrete block-start forced scheduling for telescoping OFUL

This module packages measurable finite-history selectors as deterministic
history algorithms and proves their canonical successor-action graph. It then
defines a modified telescoping OFUL selector that forces one prescribed action
after every block-start history while retaining the ordinary optimistic
selector at all other history indices.

The final theorem constructs the aligned-window positive-action-cost contract
under the modified algorithm's own canonical trajectory measure. No ordinary
OFUL regret theorem is transported to that changed measure here; forced-round
regret accounting remains a separate route.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal ProbabilityTheory

universe u v

namespace Thompson

/-- Package a measurable finite-history selector as a deterministic algorithm. -/
noncomputable def deterministicHistoryAlgorithm
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (initialAction : Action)
    (selector :
      (n : Nat) -> History.FinitePairHistory Action Reward n -> Action)
    (hselector : forall n, Measurable (selector n)) :
    HistoryAlgorithm Action Reward where
  policy n := ProbabilityTheory.Kernel.deterministic (selector n) (hselector n)
  initialAction := Measure.dirac initialAction

/-- Every policy section of a deterministic history algorithm is a Dirac law. -/
@[simp]
theorem deterministicHistoryAlgorithm_policy_apply
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (initialAction : Action)
    (selector :
      (n : Nat) -> History.FinitePairHistory Action Reward n -> Action)
    (hselector : forall n, Measurable (selector n))
    (n : Nat) (history : History.FinitePairHistory Action Reward n) :
    (deterministicHistoryAlgorithm initialAction selector hselector).policy
        n history =
      Measure.dirac (selector n history) := by
  rw [deterministicHistoryAlgorithm,
    ProbabilityTheory.Kernel.deterministic_apply]

/--
The canonical successor action of a deterministic history algorithm lies on
the graph of its measurable selector almost surely.
-/
theorem
    canonicalHistoryTrajectory_action_succ_ae_eq_deterministicHistorySelector
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableEq Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (initialAction : Action)
    (selector :
      (n : Nat) -> History.FinitePairHistory Action Reward n -> Action)
    (hselector : forall n, Measurable (selector n))
    (environment : HistoryEnvironment Action Reward)
    (n : Nat) :
    ∀ᵐ trajectory ∂
        canonicalHistoryTrajectoryMeasure
          (deterministicHistoryAlgorithm initialAction selector hselector)
          environment,
      canonicalHistoryTrajectoryAction trajectory (n + 1) =
        selector n
          (History.finitePairHistoryOfTrace
            (canonicalHistoryTrajectoryAction trajectory)
            (canonicalHistoryTrajectoryReward trajectory) n) := by
  let algorithm :=
    deterministicHistoryAlgorithm initialAction selector hselector
  let mu := canonicalHistoryTrajectoryMeasure algorithm environment
  let history := fun trajectory : (k : Nat) -> Action × Reward =>
    History.finitePairHistoryOfTrace
      (canonicalHistoryTrajectoryAction trajectory)
      (canonicalHistoryTrajectoryReward trajectory) n
  let nextAction := fun trajectory : (k : Nat) -> Action × Reward =>
    canonicalHistoryTrajectoryAction trajectory (n + 1)
  have hhistory : Measurable history :=
    History.measurable_finitePairHistoryOfTrace
      canonicalHistoryTrajectoryAction
      canonicalHistoryTrajectoryReward
      measurable_canonicalHistoryTrajectoryAction_apply
      measurable_canonicalHistoryTrajectoryReward_apply n
  have hnextAction : Measurable nextAction :=
    measurable_canonicalHistoryTrajectoryAction_apply (n + 1)
  have hpolicy :=
    policy_condDistrib_of_historyAlgorithmEnvironmentSequence
      mu
      canonicalHistoryTrajectoryAction
      canonicalHistoryTrajectoryReward
      algorithm environment
      (canonicalHistoryAlgorithmEnvironmentSequence algorithm environment)
      n
  have hjoint :
      mu.map (fun trajectory => (history trajectory, nextAction trajectory)) =
        mu.map history ⊗ₘ algorithm.policy n :=
    (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      history hnextAction.aemeasurable (algorithm.policy n)).mp <| by
        simpa [history, nextAction] using hpolicy
  have hp : MeasurableSet
      {pair : History.FinitePairHistory Action Reward n × Action |
        pair.2 = selector n pair.1} :=
    measurableSet_eq_fun measurable_snd
      ((hselector n).comp measurable_fst)
  have hgraph :
      ∀ᵐ pair ∂ mu.map history ⊗ₘ algorithm.policy n,
        pair.2 = selector n pair.1 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with historyValue
    change ∀ᵐ b ∂
      (deterministicHistoryAlgorithm
        initialAction selector hselector).policy n historyValue,
      b = selector n historyValue
    rw [deterministicHistoryAlgorithm_policy_apply]
    simp
  rw [← hjoint] at hgraph
  exact
    (ae_map_iff
      ((hhistory.prod hnextAction).aemeasurable) hp).mp hgraph

end Thompson

namespace OFUL

/--
Use the forced block action at divisible history indices and the ordinary
telescoping OFUL selector at all other indices.
-/
noncomputable def finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    Fin K :=
  if n % window = 0 then
    forcedAction (n / window)
  else
    finiteHistoryTelescopingScalarRidgeOptimisticAction
      hK lambda actionFeature R delta S n history

/-- The block-start forced selector is measurable in its finite history. -/
theorem measurable_finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window n : Nat) :
    Measurable
      (finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction window n) := by
  by_cases hforced : n % window = 0
  · unfold finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
    simp only [hforced, if_true]
    exact measurable_const
  · unfold finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
    simp only [hforced, if_false]
    simpa only [finiteHistoryTelescopingScalarRidgeOptimisticAction] using
      measurable_finiteHistoryScheduledScalarRidgeOptimisticAction
        hK lambda actionFeature R (allTimeTelescopingDelta delta) S n

/-- The block-start forced selector packaged as a fully specified history algorithm. -/
noncomputable def finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat) :
    Thompson.HistoryAlgorithm (Fin K) Real :=
  Thompson.deterministicHistoryAlgorithm
    (Fin.mk 0 hK)
    (finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction window)
    (measurable_finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction window)

/-- Every policy section is the Dirac law at the modified selector. -/
@[simp]
theorem
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm_policy_apply
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
      hK lambda actionFeature R delta S forcedAction window).policy n history =
        Measure.dirac
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
            hK lambda actionFeature R delta S forcedAction window n history) := by
  exact Thompson.deterministicHistoryAlgorithm_policy_apply
    (Fin.mk 0 hK)
    (finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction window)
    (measurable_finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction window)
    n history

/-- At a block-multiple history index, the modified selector uses that block's forced arm. -/
@[simp]
theorem
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAction_mul_window
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window block : Nat)
    (hwindow : 0 < window)
    (history :
      History.FinitePairHistory (Fin K) Real (block * window)) :
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction window
        (block * window) history =
      forcedAction block := by
  have hdiv : block * window / window = block := by
    rw [Nat.mul_comm, Nat.mul_div_right block hwindow]
  simp [finiteHistoryBlockStartForcedTelescopingScalarRidgeAction, hdiv]

/-- Generated successor actions follow the modified selector almost surely. -/
theorem
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment,
      (trajectory (n + 1)).1 =
        finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
          hK lambda actionFeature R delta S forcedAction window n
          (Preorder.frestrictLe n trajectory) := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  simpa only [
      finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm,
      Thompson.canonicalHistoryTrajectoryAction,
      Thompson.canonicalHistoryTrajectoryReward] using
    (Thompson.canonicalHistoryTrajectory_action_succ_ae_eq_deterministicHistorySelector
      (Fin.mk 0 hK)
      (finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction window)
      (measurable_finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction window)
      environment n)

/-- The generated action after a block-start history is the prescribed forced arm. -/
theorem
    canonicalHistoryTrajectory_action_blockStart_succ_ae_eq_forcedAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (hwindow : 0 < window)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (block : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment,
      (trajectory (block * window + 1)).1 = forcedAction block := by
  filter_upwards [
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction window environment
      (block * window)] with trajectory htrajectory
  rw [htrajectory]
  exact
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAction_mul_window
      hK lambda actionFeature R delta S forcedAction window block hwindow
      (Preorder.frestrictLe (block * window) trajectory)

end OFUL

namespace Budget

/--
Positive forced-arm costs produce one positive selected action in every
aligned block under the modified algorithm's canonical law.
-/
theorem
    alignedWindowPositiveActionCostAE_finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (hwindow : 2 <= window)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (actionCost : Fin K -> Nat)
    (hpositive : forall block, 1 <= actionCost (forcedAction block)) :
    AlignedWindowPositiveActionCostAE
      (Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
          hK lambda actionFeature R delta S forcedAction window)
        environment)
      actionCost window := by
  rw [alignedWindowPositiveActionCostAE_iff_forall_ae]
  intro block
  have hforced :=
    OFUL.canonicalHistoryTrajectory_action_blockStart_succ_ae_eq_forcedAction
      hK lambda actionFeature R delta S forcedAction window (by omega)
      environment block
  filter_upwards [hforced] with trajectory htrajectory
  refine ⟨block * window + 1, ?_, ?_⟩
  · simp only [Finset.mem_Ico]
    constructor
    · omega
    · rw [Nat.add_mul]
      omega
  · rw [htrajectory]
    exact hpositive block

end Budget
end BanditRLProof
