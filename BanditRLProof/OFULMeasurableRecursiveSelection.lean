import BanditRLProof.OFULFiniteActionOptimism
import BanditRLProof.Algorithms.ETCRealEmpiricalMean
import BanditRLProof.Algorithms.ThompsonCanonicalTrajectory

/-!
# Measurable recursive OFUL selection

This module replaces the nonconstructive finite OFUL argmax by the existing
strict finite fold on `Fin K`.  Under measurable score coordinates, the fold
defines a deterministic history policy.  The canonical history trajectory
then realizes that selector at every successor time.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace OFUL

/-- The OFUL score of one action at one inclusive finite pair history. -/
noncomputable def finiteHistoryOptimisticScore
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward]
    [Fintype Feature] [DecidableEq Feature]
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n)
    (action : Fin K) : Real :=
  optimisticScore (thetaHat n history) (V n history) (beta n history)
    (candidateFeature n history action)

/--
Deterministic history OFUL selector with the strict-update finite fold.
The strict comparison gives a fixed deterministic tie behavior.
-/
noncomputable def finiteHistoryOptimisticAction
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward]
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n) :
    Fin K :=
  ETC.realArgmaxCommit hK
    (finiteHistoryOptimisticScore thetaHat V beta candidateFeature n history)

/-- The history selector maximizes the current OFUL score. -/
theorem finiteHistoryOptimisticAction_score_max
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward]
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n)
    (action : Fin K) :
    finiteHistoryOptimisticScore thetaHat V beta candidateFeature
        n history action <=
      finiteHistoryOptimisticScore thetaHat V beta candidateFeature n history
        (finiteHistoryOptimisticAction
          hK thetaHat V beta candidateFeature n history) := by
  exact ETC.realArgmaxCommit_spec hK
    (finiteHistoryOptimisticScore thetaHat V beta candidateFeature n history)
    action

/--
The strict-fold history selector is measurable when each fixed-action score
coordinate is measurable.
-/
theorem measurable_finiteHistoryOptimisticAction
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward]
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (n : Nat)
    (hscores : forall action : Fin K,
      Measurable (fun history : History.FinitePairHistory (Fin K) Reward n =>
        finiteHistoryOptimisticScore thetaHat V beta candidateFeature
          n history action)) :
    Measurable (finiteHistoryOptimisticAction
      hK thetaHat V beta candidateFeature n) := by
  exact ETC.measurable_realArgmaxCommit_of_forall_measurable hK
    (fun history action =>
      finiteHistoryOptimisticScore thetaHat V beta candidateFeature
        n history action)
    hscores

/-- The measurable history selector packaged as a deterministic algorithm. -/
noncomputable def finiteHistoryOptimisticAlgorithm
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward]
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (hscores : forall (n : Nat) (action : Fin K),
      Measurable (fun history : History.FinitePairHistory (Fin K) Reward n =>
        finiteHistoryOptimisticScore thetaHat V beta candidateFeature
          n history action)) :
    Thompson.HistoryAlgorithm (Fin K) Reward where
  policy n :=
    ProbabilityTheory.Kernel.deterministic
      (finiteHistoryOptimisticAction
        hK thetaHat V beta candidateFeature n)
      (measurable_finiteHistoryOptimisticAction
        hK thetaHat V beta candidateFeature n (hscores n))
  initialAction := Measure.dirac (Fin.mk 0 hK)

/-- Every policy section of the history OFUL algorithm is the selector Dirac law. -/
@[simp] theorem finiteHistoryOptimisticAlgorithm_policy_apply
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward]
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (hscores : forall (n : Nat) (action : Fin K),
      Measurable (fun history : History.FinitePairHistory (Fin K) Reward n =>
        finiteHistoryOptimisticScore thetaHat V beta candidateFeature
          n history action))
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n) :
    (finiteHistoryOptimisticAlgorithm
      hK thetaHat V beta candidateFeature hscores).policy n history =
      Measure.dirac
        (finiteHistoryOptimisticAction
          hK thetaHat V beta candidateFeature n history) := by
  rw [finiteHistoryOptimisticAlgorithm,
    ProbabilityTheory.Kernel.deterministic_apply]

/--
Along the canonical recursive trajectory, the successor action is almost
surely the measurable OFUL selector evaluated on the realized finite history.
-/
theorem canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryOptimisticAction
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (hscores : forall (n : Nat) (action : Fin K),
      Measurable (fun history : History.FinitePairHistory (Fin K) Reward n =>
        finiteHistoryOptimisticScore thetaHat V beta candidateFeature
          n history action))
    (environment : Thompson.HistoryEnvironment (Fin K) Reward)
    (n : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryOptimisticAlgorithm
            hK thetaHat V beta candidateFeature hscores)
          environment,
      Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
        finiteHistoryOptimisticAction
          hK thetaHat V beta candidateFeature n
          (History.finitePairHistoryOfTrace
            (Thompson.canonicalHistoryTrajectoryAction trajectory)
            (Thompson.canonicalHistoryTrajectoryReward trajectory) n) := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  let algorithm :=
    finiteHistoryOptimisticAlgorithm
      hK thetaHat V beta candidateFeature hscores
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let history := fun trajectory : (k : Nat) -> Fin K × Reward =>
    History.finitePairHistoryOfTrace
      (Thompson.canonicalHistoryTrajectoryAction trajectory)
      (Thompson.canonicalHistoryTrajectoryReward trajectory) n
  let nextAction := fun trajectory : (k : Nat) -> Fin K × Reward =>
    Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1)
  let selector :=
    finiteHistoryOptimisticAction
      hK thetaHat V beta candidateFeature n
  have hhistory : Measurable history :=
    History.measurable_finitePairHistoryOfTrace
      Thompson.canonicalHistoryTrajectoryAction
      Thompson.canonicalHistoryTrajectoryReward
      Thompson.measurable_canonicalHistoryTrajectoryAction_apply
      Thompson.measurable_canonicalHistoryTrajectoryReward_apply n
  have hnextAction : Measurable nextAction :=
    Thompson.measurable_canonicalHistoryTrajectoryAction_apply (n + 1)
  have hselector : Measurable selector :=
    measurable_finiteHistoryOptimisticAction
      hK thetaHat V beta candidateFeature n (hscores n)
  have hpolicy :=
    Thompson.policy_condDistrib_of_historyAlgorithmEnvironmentSequence
      mu
      Thompson.canonicalHistoryTrajectoryAction
      Thompson.canonicalHistoryTrajectoryReward
      algorithm environment
      (Thompson.canonicalHistoryAlgorithmEnvironmentSequence
        algorithm environment)
      n
  have hjoint :
      mu.map (fun trajectory => (history trajectory, nextAction trajectory)) =
        mu.map history ⊗ₘ algorithm.policy n :=
    (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      history hnextAction.aemeasurable (algorithm.policy n)).mp <| by
        simpa [history, nextAction] using hpolicy
  have hp : MeasurableSet
      {pair : History.FinitePairHistory (Fin K) Reward n × Fin K |
        pair.2 = selector pair.1} :=
    measurableSet_eq_fun measurable_snd
      (hselector.comp measurable_fst)
  have hgraph :
      ∀ᵐ pair ∂ mu.map history ⊗ₘ algorithm.policy n,
        pair.2 = selector pair.1 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with historyValue
    simp [algorithm, selector]
  rw [← hjoint] at hgraph
  exact
    (ae_map_iff
      ((hhistory.prod hnextAction).aemeasurable) hp).mp hgraph

/-- Candidate feature selected by the measurable OFUL history action. -/
noncomputable def finiteHistoryOptimisticSelectedFeature
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward]
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n) :
    Feature -> Real :=
  candidateFeature n history
    (finiteHistoryOptimisticAction
      hK thetaHat V beta candidateFeature n history)

/--
The feature indexed by the actual canonical successor action agrees almost
surely with the feature selected from the realized history.
-/
theorem canonicalHistoryTrajectory_candidateFeature_succ_ae_eq_selectedFeature
    {K : Nat} {Reward : Type u} {Feature : Type v}
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (thetaHat : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Feature -> Real)
    (V : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Matrix Feature Feature Real)
    (beta : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n -> Real)
    (candidateFeature : (n : Nat) ->
      History.FinitePairHistory (Fin K) Reward n ->
        Fin K -> Feature -> Real)
    (hscores : forall (n : Nat) (action : Fin K),
      Measurable (fun history : History.FinitePairHistory (Fin K) Reward n =>
        finiteHistoryOptimisticScore thetaHat V beta candidateFeature
          n history action))
    (environment : Thompson.HistoryEnvironment (Fin K) Reward)
    (n : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryOptimisticAlgorithm
            hK thetaHat V beta candidateFeature hscores)
          environment,
      candidateFeature n
          (History.finitePairHistoryOfTrace
            (Thompson.canonicalHistoryTrajectoryAction trajectory)
            (Thompson.canonicalHistoryTrajectoryReward trajectory) n)
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1)) =
        finiteHistoryOptimisticSelectedFeature
          hK thetaHat V beta candidateFeature n
          (History.finitePairHistoryOfTrace
            (Thompson.canonicalHistoryTrajectoryAction trajectory)
            (Thompson.canonicalHistoryTrajectoryReward trajectory) n) := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  have haction :=
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryOptimisticAction
      hK thetaHat V beta candidateFeature hscores environment n
  filter_upwards [haction] with trajectory htrajectory
  rw [htrajectory]
  rfl

end OFUL
end BanditRLProof
