import BanditRLProof.OFULConcreteHistoryRidgeSelection
import BanditRLProof.OFULUniformTimeConfidence

/-!
# Generated-trajectory confidence and gap transport for OFUL

This module identifies the scalar-ridge state reconstructed from an inclusive
finite pair history with the generic finite-horizon state on the underlying
trajectory. It then transports the measurable strict-fold selector's score
maximality to one-step and finite successor-window optimism-gap bounds.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u

namespace BanditRLProof
namespace OFUL

/--
Any action whose optimistic score dominates a comparator satisfies the usual
two-bonus OFUL gap bound on the confidence ellipsoid.
-/
theorem linearValue_sub_selected_le_two_mul_bonus_of_score_max
    {Feature Action : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (V : Matrix Feature Feature Real) (hV : V.PosDef)
    (thetaHat thetaStar : Feature -> Real) (beta : Real)
    (actionFeature : Action -> Feature -> Real)
    (selected comparator : Action)
    (hconfidence : matrixNorm V (thetaHat - thetaStar) <= beta)
    (hscoreMax :
      optimisticScore thetaHat V beta (actionFeature comparator) <=
        optimisticScore thetaHat V beta (actionFeature selected)) :
    linearValue thetaStar (actionFeature comparator) -
        linearValue thetaStar (actionFeature selected) <=
      2 * beta * confidenceWidth V (actionFeature selected) := by
  have hoptimistic :
      linearValue thetaStar (actionFeature comparator) <=
        optimisticScore thetaHat V beta (actionFeature comparator) :=
    linearValue_le_optimisticScore_of_matrixNorm_sub_le
      V hV thetaHat thetaStar beta (actionFeature comparator) hconfidence
  have hselected :
      optimisticScore thetaHat V beta (actionFeature selected) <=
        linearValue thetaStar (actionFeature selected) +
          2 * beta * confidenceWidth V (actionFeature selected) :=
    optimisticScore_le_linearValue_add_two_mul_bonus_of_matrixNorm_sub_le
      V hV thetaHat thetaStar beta (actionFeature selected) hconfidence
  linarith

/--
The concrete strict-fold history selector has the OFUL one-step gap
certificate. No identification with the nonconstructive finite argmax is used.
-/
theorem finiteHistoryScalarRidgeOptimisticAction_gap_le
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (hconfidence :
      matrixNorm
          (finiteHistoryScalarRidgeDesign lambda actionFeature n history)
          (finiteHistoryScalarRidgeEstimate lambda actionFeature n history -
            thetaStar) <=
        finiteHistoryScalarRidgeRadius
          actionFeature R delta lambda S n history)
    (comparator : Fin K) :
    linearValue thetaStar (actionFeature comparator) -
        linearValue thetaStar
          (actionFeature
            (finiteHistoryScalarRidgeOptimisticAction
              hK lambda actionFeature R delta S n history)) <=
      2 *
        finiteHistoryScalarRidgeRadius
          actionFeature R delta lambda S n history *
        confidenceWidth
          (finiteHistoryScalarRidgeDesign lambda actionFeature n history)
          (actionFeature
            (finiteHistoryScalarRidgeOptimisticAction
              hK lambda actionFeature R delta S n history)) := by
  have hV :
      (finiteHistoryScalarRidgeDesign
        lambda actionFeature n history).PosDef := by
    unfold finiteHistoryScalarRidgeDesign
    exact
      (scalarIdentity_posDef lambda hlambda).add_posSemidef
        (finiteHorizonFeatureGram_posSemidef
          (fun t historyValue =>
            finiteHistoryObservedFeature actionFeature n historyValue t)
          (n + 1) history)
  have hscoreMax :=
    finiteHistoryScalarRidgeOptimisticAction_score_max
      hK lambda actionFeature R delta S n history comparator
  simpa only [finiteHistoryScalarRidgeOptimisticScore,
    finiteHistoryFixedActionFeature] using
    (linearValue_sub_selected_le_two_mul_bonus_of_score_max
      (finiteHistoryScalarRidgeDesign lambda actionFeature n history) hV
      (finiteHistoryScalarRidgeEstimate lambda actionFeature n history)
      thetaStar
      (finiteHistoryScalarRidgeRadius
        actionFeature R delta lambda S n history)
      actionFeature
      (finiteHistoryScalarRidgeOptimisticAction
        hK lambda actionFeature R delta S n history)
      comparator hconfidence hscoreMax)

/-- Feature process obtained by projecting actions from a canonical trajectory. -/
def canonicalHistoryTrajectoryFeature
    {K : Nat} {Feature : Type u}
    (actionFeature : Fin K -> Feature -> Real)
    (t : Nat) (trajectory : (k : Nat) -> Fin K × Real) :
    Feature -> Real :=
  actionFeature (Thompson.canonicalHistoryTrajectoryAction trajectory t)

/-- Response process obtained by projecting rewards from a canonical trajectory. -/
def canonicalHistoryTrajectoryResponse
    {K : Nat}
    (t : Nat) (trajectory : (k : Nat) -> Fin K × Real) : Real :=
  Thompson.canonicalHistoryTrajectoryReward trajectory t

/-- A trace prefix exposes the original action feature at every stored index. -/
@[simp] theorem finiteHistoryObservedFeature_finitePairHistoryOfTrace_of_le
    {K : Nat} {Feature : Type u}
    (actionFeature : Fin K -> Feature -> Real)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (n t : Nat) (ht : t <= n) :
    finiteHistoryObservedFeature actionFeature n
        (History.finitePairHistoryOfTrace action reward n) t =
      actionFeature (action t) := by
  simp [finiteHistoryObservedFeature, ht]

/-- A trace prefix exposes the original response at every stored index. -/
@[simp] theorem finiteHistoryObservedResponse_finitePairHistoryOfTrace_of_le
    {K : Nat}
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (n t : Nat) (ht : t <= n) :
    finiteHistoryObservedResponse n
        (History.finitePairHistoryOfTrace action reward n) t =
      reward t := by
  simp [finiteHistoryObservedResponse, ht]

/--
The feature Gram reconstructed from inclusive history `n` is exactly the
trajectory feature Gram at horizon `n + 1`.
-/
theorem finiteHorizonFeatureGram_finitePairHistoryOfTrace_eq
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (actionFeature : Fin K -> Feature -> Real)
    (trajectory : (k : Nat) -> Fin K × Real) (n : Nat) :
    finiteHorizonFeatureGram
        (fun t historyValue =>
          finiteHistoryObservedFeature actionFeature n historyValue t)
        (n + 1)
        (History.finitePairHistoryOfTrace
          (Thompson.canonicalHistoryTrajectoryAction trajectory)
          (Thompson.canonicalHistoryTrajectoryReward trajectory) n) =
      finiteHorizonFeatureGram
        (canonicalHistoryTrajectoryFeature actionFeature)
        (n + 1) trajectory := by
  ext i j
  unfold finiteHorizonFeatureGram prefixFeatureGram
  apply Finset.sum_congr rfl
  intro t ht
  have htn : t <= n :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  simp [canonicalHistoryTrajectoryFeature, htn]

/--
The response vector reconstructed from inclusive history `n` is exactly the
trajectory response vector at horizon `n + 1`.
-/
theorem finiteHorizonResponseVector_finitePairHistoryOfTrace_eq
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (actionFeature : Fin K -> Feature -> Real)
    (trajectory : (k : Nat) -> Fin K × Real) (n : Nat) :
    finiteHorizonResponseVector
        (fun t historyValue =>
          finiteHistoryObservedFeature actionFeature n historyValue t)
        (fun t historyValue =>
          finiteHistoryObservedResponse n historyValue t)
        (n + 1)
        (History.finitePairHistoryOfTrace
          (Thompson.canonicalHistoryTrajectoryAction trajectory)
          (Thompson.canonicalHistoryTrajectoryReward trajectory) n) =
      finiteHorizonResponseVector
        (canonicalHistoryTrajectoryFeature actionFeature)
        canonicalHistoryTrajectoryResponse
        (n + 1) trajectory := by
  ext j
  unfold finiteHorizonResponseVector
  apply Finset.sum_congr rfl
  intro t ht
  have htn : t <= n :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  simp [canonicalHistoryTrajectoryFeature,
    canonicalHistoryTrajectoryResponse, htn]

/-- Exact design-matrix alignment between finite history and trajectory state. -/
theorem finiteHistoryScalarRidgeDesign_finitePairHistoryOfTrace_eq
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (trajectory : (k : Nat) -> Fin K × Real) (n : Nat) :
    finiteHistoryScalarRidgeDesign lambda actionFeature n
        (History.finitePairHistoryOfTrace
          (Thompson.canonicalHistoryTrajectoryAction trajectory)
          (Thompson.canonicalHistoryTrajectoryReward trajectory) n) =
      finiteHorizonScalarGram lambda
        (canonicalHistoryTrajectoryFeature actionFeature)
        (n + 1) trajectory := by
  unfold finiteHistoryScalarRidgeDesign finiteHorizonScalarGram
  rw [finiteHorizonFeatureGram_finitePairHistoryOfTrace_eq]

/-- Exact ridge-estimate alignment between finite history and trajectory state. -/
theorem finiteHistoryScalarRidgeEstimate_finitePairHistoryOfTrace_eq
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (trajectory : (k : Nat) -> Fin K × Real) (n : Nat) :
    finiteHistoryScalarRidgeEstimate lambda actionFeature n
        (History.finitePairHistoryOfTrace
          (Thompson.canonicalHistoryTrajectoryAction trajectory)
          (Thompson.canonicalHistoryTrajectoryReward trajectory) n) =
      finiteHorizonRidgeEstimate
        (Matrix.scalar Feature lambda)
        (canonicalHistoryTrajectoryFeature actionFeature)
        canonicalHistoryTrajectoryResponse
        (n + 1) trajectory := by
  unfold finiteHistoryScalarRidgeEstimate finiteHorizonRidgeEstimate
  rw [finiteHorizonFeatureGram_finitePairHistoryOfTrace_eq,
    finiteHorizonResponseVector_finitePairHistoryOfTrace_eq]

/-- Exact confidence-radius alignment between finite history and trajectory. -/
theorem finiteHistoryScalarRidgeRadius_finitePairHistoryOfTrace_eq
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (trajectory : (k : Nat) -> Fin K × Real) (n : Nat) :
    finiteHistoryScalarRidgeRadius
        actionFeature R delta lambda S n
        (History.finitePairHistoryOfTrace
          (Thompson.canonicalHistoryTrajectoryAction trajectory)
          (Thompson.canonicalHistoryTrajectoryReward trajectory) n) =
      finiteHorizonScalarConfidenceRadius
        (canonicalHistoryTrajectoryFeature actionFeature)
        R delta lambda S (n + 1) trajectory := by
  unfold finiteHistoryScalarRidgeRadius
    finiteHorizonScalarConfidenceRadius
    finiteHorizonConfidenceRadius
    finiteHorizonConfidenceThreshold
  rw [finiteHorizonFeatureGram_finitePairHistoryOfTrace_eq]

/--
Outside the generic fixed-time confidence failure set, the actual canonical
successor action satisfies the concrete OFUL one-step gap certificate.
-/
theorem
    canonicalHistoryTrajectory_action_succ_gap_le_of_not_mem_confidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) (comparator : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      trajectory ∉
          scalarRidgeConfidenceFailureAt
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse
            R delta (n + 1) ->
        linearValue thetaStar (actionFeature comparator) -
            linearValue thetaStar
              (actionFeature
                (Thompson.canonicalHistoryTrajectoryAction
                  trajectory (n + 1))) <=
          2 *
            finiteHorizonScalarConfidenceRadius
              (canonicalHistoryTrajectoryFeature actionFeature)
              R delta lambda S (n + 1) trajectory *
            confidenceWidth
              (finiteHorizonScalarGram lambda
                (canonicalHistoryTrajectoryFeature actionFeature)
                (n + 1) trajectory)
              (actionFeature
                (Thompson.canonicalHistoryTrajectoryAction
                  trajectory (n + 1))) := by
  filter_upwards [
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryOptimisticAction
      hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScalarRidgeRadius actionFeature R delta lambda S)
      (finiteHistoryFixedActionFeature actionFeature)
      (measurable_finiteHistoryScalarRidgeOptimisticScore
        lambda actionFeature R delta S)
      environment n] with trajectory haction
  intro hgood
  let history :=
    History.finitePairHistoryOfTrace
      (Thompson.canonicalHistoryTrajectoryAction trajectory)
      (Thompson.canonicalHistoryTrajectoryReward trajectory) n
  have hgeneric :
      matrixNorm
          (finiteHorizonScalarGram lambda
            (canonicalHistoryTrajectoryFeature actionFeature)
            (n + 1) trajectory)
          (finiteHorizonRidgeEstimate
              (Matrix.scalar Feature lambda)
              (canonicalHistoryTrajectoryFeature actionFeature)
              canonicalHistoryTrajectoryResponse
              (n + 1) trajectory -
            thetaStar) <=
        finiteHorizonScalarConfidenceRadius
          (canonicalHistoryTrajectoryFeature actionFeature)
          R delta lambda S (n + 1) trajectory := by
    simpa only [scalarRidgeConfidenceFailureAt,
      finiteHorizonScalarGram, Set.mem_setOf_eq, not_lt] using hgood
  have hhistory :
      matrixNorm
          (finiteHistoryScalarRidgeDesign
            lambda actionFeature n history)
          (finiteHistoryScalarRidgeEstimate
              lambda actionFeature n history -
            thetaStar) <=
        finiteHistoryScalarRidgeRadius
          actionFeature R delta lambda S n history := by
    simpa only [history,
      finiteHistoryScalarRidgeDesign_finitePairHistoryOfTrace_eq,
      finiteHistoryScalarRidgeEstimate_finitePairHistoryOfTrace_eq,
      finiteHistoryScalarRidgeRadius_finitePairHistoryOfTrace_eq] using
      hgeneric
  have hgap :=
    finiteHistoryScalarRidgeOptimisticAction_gap_le
      hK lambda hlambda thetaStar actionFeature R delta S n history
      hhistory comparator
  have haction' :
      Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
        finiteHistoryScalarRidgeOptimisticAction
          hK lambda actionFeature R delta S n history := by
    simpa only [history, finiteHistoryScalarRidgeOptimisticAction] using
      haction
  rw [← haction'] at hgap
  simpa only [history,
    finiteHistoryScalarRidgeDesign_finitePairHistoryOfTrace_eq,
    finiteHistoryScalarRidgeRadius_finitePairHistoryOfTrace_eq] using hgap

/--
On the equal-share uniform confidence event, all canonical successor rounds
`1, ..., horizon` satisfy the cumulative OFUL bonus bound. The fixed initial
round `0` is not part of this sum.
-/
theorem
    canonicalHistoryTrajectory_sum_range_succ_gap_le_on_uniformConfidence
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (comparator : Nat -> Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R
              (delta / ((horizon + 1 : Nat) : Real)) S)
          environment,
      trajectory ∉
          finiteHorizonUniformScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse
            R delta horizon ->
        (Finset.range horizon).sum (fun n =>
            linearValue thetaStar (actionFeature (comparator (n + 1))) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1)))) <=
          (Finset.range horizon).sum (fun n =>
            2 *
              finiteHorizonScalarConfidenceRadius
                (canonicalHistoryTrajectoryFeature actionFeature)
                R (delta / ((horizon + 1 : Nat) : Real))
                lambda S (n + 1) trajectory *
              confidenceWidth
                (finiteHorizonScalarGram lambda
                  (canonicalHistoryTrajectoryFeature actionFeature)
                  (n + 1) trajectory)
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1)))) := by
  have hsteps : forall n : Nat,
      ∀ᵐ trajectory ∂
          Thompson.canonicalHistoryTrajectoryMeasure
            (finiteHistoryScalarRidgeOptimisticAlgorithm
              hK lambda actionFeature R
                (delta / ((horizon + 1 : Nat) : Real)) S)
            environment,
        trajectory ∉
            scalarRidgeConfidenceFailureAt
              lambda thetaStar S
              (canonicalHistoryTrajectoryFeature actionFeature)
              canonicalHistoryTrajectoryResponse
              R (delta / ((horizon + 1 : Nat) : Real)) (n + 1) ->
          linearValue thetaStar
                (actionFeature (comparator (n + 1))) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1))) <=
            2 *
              finiteHorizonScalarConfidenceRadius
                (canonicalHistoryTrajectoryFeature actionFeature)
                R (delta / ((horizon + 1 : Nat) : Real))
                lambda S (n + 1) trajectory *
              confidenceWidth
                (finiteHorizonScalarGram lambda
                  (canonicalHistoryTrajectoryFeature actionFeature)
                  (n + 1) trajectory)
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1))) := by
    intro n
    exact
      canonicalHistoryTrajectory_action_succ_gap_le_of_not_mem_confidenceFailure
        hK lambda hlambda thetaStar actionFeature R
        (delta / ((horizon + 1 : Nat) : Real)) S environment n
        (comparator (n + 1))
  filter_upwards [ae_all_iff.2 hsteps] with trajectory htrajectory
  intro hgood
  apply Finset.sum_le_sum
  intro n hn
  have hnlt : n < horizon := Finset.mem_range.mp hn
  have hnsucc : n + 1 <= horizon := Nat.succ_le_iff.mpr hnlt
  have hscheduled :
      trajectory ∉
        finiteHorizonScheduledScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R
          (fun _ => delta / ((horizon + 1 : Nat) : Real)) horizon := by
    simpa only [finiteHorizonUniformScalarRidgeConfidenceFailureSet] using
      hgood
  have hconfidence :=
    (not_mem_finiteHorizonScheduledScalarRidgeConfidenceFailureSet_iff
      lambda thetaStar S
      (canonicalHistoryTrajectoryFeature actionFeature)
      canonicalHistoryTrajectoryResponse R
      (fun _ => delta / ((horizon + 1 : Nat) : Real))
      horizon trajectory).mp hscheduled
  have hnotAt :
      trajectory ∉
        scalarRidgeConfidenceFailureAt
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse
          R (delta / ((horizon + 1 : Nat) : Real)) (n + 1) := by
    simpa only [scalarRidgeConfidenceFailureAt,
      Set.mem_setOf_eq, not_lt] using hconfidence (n + 1) hnsucc
  exact htrajectory n hnotAt

end OFUL
end BanditRLProof
