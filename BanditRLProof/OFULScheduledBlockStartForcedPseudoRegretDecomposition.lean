import BanditRLProof.OFULScheduledBlockStartForcedHistoryAlgorithm

/-!
# Pseudo-regret decomposition for block-start forced telescoping OFUL

This module separates the complete finite-horizon pseudo-regret of the
block-start forced policy into the initial action, forced successor actions,
and ordinary optimistic successor actions. The successor index `n` denotes the
history used to select action `n + 1`.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal ProbabilityTheory

universe u

namespace OFUL

/-- Away from block starts, the modified selector is the telescoping OFUL selector. -/
theorem
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAction_eq_of_mod_ne_zero
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (hnonforced : n % window ≠ 0) :
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction window n history =
      finiteHistoryTelescopingScalarRidgeOptimisticAction
        hK lambda actionFeature R delta S n history := by
  simp [finiteHistoryBlockStartForcedTelescopingScalarRidgeAction, hnonforced]

/-- At a forced index, the modified selector is the prescribed block action. -/
theorem
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAction_eq_forcedAction_of_mod_eq_zero
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (hforced : n % window = 0) :
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction window n history =
      forcedAction (n / window) := by
  simp [finiteHistoryBlockStartForcedTelescopingScalarRidgeAction, hforced]

/--
Under the modified policy's own trajectory law, every nonforced successor
action agrees almost surely with the ordinary telescoping OFUL selector.
-/
theorem
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryTelescopingScalarRidgeOptimisticAction_of_mod_ne_zero
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat)
    (hnonforced : n % window ≠ 0) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment,
      (trajectory (n + 1)).1 =
        finiteHistoryTelescopingScalarRidgeOptimisticAction
          hK lambda actionFeature R delta S n
          (Preorder.frestrictLe n trajectory) := by
  filter_upwards [
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction window environment n] with
    trajectory htrajectory
  rw [htrajectory]
  exact
    finiteHistoryBlockStartForcedTelescopingScalarRidgeAction_eq_of_mod_ne_zero
      hK lambda actionFeature R delta S forcedAction window n
      (Preorder.frestrictLe n trajectory) hnonforced

/-- Successor pseudo-regret charged to block-start forced actions. -/
noncomputable def blockStartForcedSuccessorPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (window horizon : Nat)
    (trajectory : Nat -> Fin K × Real) : Real :=
  ((Finset.range horizon).filter (fun n => n % window = 0)).sum (fun n =>
    linearValue thetaStar (actionFeature best) -
      linearValue thetaStar
        (actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1))))

/-- Deterministic successor charge of the prescribed forced actions. -/
noncomputable def blockStartForcedActionSuccessorPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (forcedAction : Nat -> Fin K)
    (window horizon : Nat) : Real :=
  ((Finset.range horizon).filter (fun n => n % window = 0)).sum (fun n =>
    linearValue thetaStar (actionFeature best) -
      linearValue thetaStar (actionFeature (forcedAction (n / window))))

/-- Successor pseudo-regret charged to nonforced optimistic actions. -/
noncomputable def blockStartOptimisticSuccessorPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (window horizon : Nat)
    (trajectory : Nat -> Fin K × Real) : Real :=
  ((Finset.range horizon).filter (fun n => n % window ≠ 0)).sum (fun n =>
    linearValue thetaStar (actionFeature best) -
      linearValue thetaStar
        (actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1))))

/-- Scheduled radius-width charge over the nonforced successor actions. -/
noncomputable def blockStartOptimisticSuccessorRadiusWidthCharge
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (window horizon : Nat)
    (trajectory : Nat -> Fin K × Real) : Real :=
  ((Finset.range horizon).filter (fun n => n % window ≠ 0)).sum (fun n =>
    2 *
      finiteHorizonScalarConfidenceRadius
        (canonicalHistoryTrajectoryFeature actionFeature)
        R (allTimeTelescopingDelta delta (n + 1))
        lambda S (n + 1) trajectory *
      confidenceWidth
        (finiteHorizonScalarGram lambda
          (canonicalHistoryTrajectoryFeature actionFeature)
          (n + 1) trajectory)
        (actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1))))

/--
Pathwise one-step optimism transport. The policy-specific input is only the
equality between the observed successor action and the telescoping selector.
-/
theorem
    canonicalHistoryTrajectory_action_succ_gap_le_of_eq_telescopingAction_of_not_mem_confidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (trajectory : Nat -> Fin K × Real)
    (n : Nat) (comparator : Fin K)
    (haction :
      Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
        finiteHistoryTelescopingScalarRidgeOptimisticAction
          hK lambda actionFeature R delta S n
          (History.finitePairHistoryOfTrace
            (Thompson.canonicalHistoryTrajectoryAction trajectory)
            (Thompson.canonicalHistoryTrajectoryReward trajectory) n))
    (hgood :
      trajectory ∉
        scalarRidgeConfidenceFailureAt
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R
          (allTimeTelescopingDelta delta (n + 1)) (n + 1)) :
    linearValue thetaStar (actionFeature comparator) -
        linearValue thetaStar
          (actionFeature
            (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1))) <=
      2 *
        finiteHorizonScalarConfidenceRadius
          (canonicalHistoryTrajectoryFeature actionFeature)
          R (allTimeTelescopingDelta delta (n + 1))
          lambda S (n + 1) trajectory *
        confidenceWidth
          (finiteHorizonScalarGram lambda
            (canonicalHistoryTrajectoryFeature actionFeature)
            (n + 1) trajectory)
          (actionFeature
            (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1))) := by
  let history :=
    History.finitePairHistoryOfTrace
      (Thompson.canonicalHistoryTrajectoryAction trajectory)
      (Thompson.canonicalHistoryTrajectoryReward trajectory) n
  let deltaN := allTimeTelescopingDelta delta (n + 1)
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
          R deltaN lambda S (n + 1) trajectory := by
    simpa only [deltaN, scalarRidgeConfidenceFailureAt,
      finiteHorizonScalarGram, Set.mem_setOf_eq, not_lt] using hgood
  have hhistory :
      matrixNorm
          (finiteHistoryScalarRidgeDesign
            lambda actionFeature n history)
          (finiteHistoryScalarRidgeEstimate
              lambda actionFeature n history -
            thetaStar) <=
        finiteHistoryScalarRidgeRadius
          actionFeature R deltaN lambda S n history := by
    simpa only [history,
      finiteHistoryScalarRidgeDesign_finitePairHistoryOfTrace_eq,
      finiteHistoryScalarRidgeEstimate_finitePairHistoryOfTrace_eq,
      finiteHistoryScalarRidgeRadius_finitePairHistoryOfTrace_eq] using
      hgeneric
  have hgap :=
    finiteHistoryScalarRidgeOptimisticAction_gap_le
      hK lambda hlambda thetaStar actionFeature R deltaN S n history
      hhistory comparator
  have haction' :
      Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
        finiteHistoryScalarRidgeOptimisticAction
          hK lambda actionFeature R deltaN S n history := by
    simpa only [history, deltaN,
      finiteHistoryTelescopingScalarRidgeOptimisticAction,
      finiteHistoryScheduledScalarRidgeOptimisticAction_eq] using haction
  rw [← haction'] at hgap
  simpa only [history, deltaN,
    finiteHistoryScalarRidgeDesign_finitePairHistoryOfTrace_eq,
    finiteHistoryScalarRidgeRadius_finitePairHistoryOfTrace_eq] using hgap

/--
The complete pseudo-regret through action `horizon` is the initial gap plus
the forced and nonforced successor charges. This identity is pathwise and does
not require a probability or confidence assumption.
-/
theorem canonicalStandardHighProbabilityPseudoRegret_eq_initial_add_blockStartForced_add_optimistic
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (window horizon : Nat)
    (trajectory : Nat -> Fin K × Real) :
    canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory =
      (linearValue thetaStar (actionFeature best) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction trajectory 0))) +
        blockStartForcedSuccessorPseudoRegret
          thetaStar actionFeature best window horizon trajectory +
        blockStartOptimisticSuccessorPseudoRegret
          thetaStar actionFeature best window horizon trajectory := by
  unfold canonicalStandardHighProbabilityPseudoRegret
    canonicalHistoryTrajectorySumRangeAllGap
    blockStartForcedSuccessorPseudoRegret
    blockStartOptimisticSuccessorPseudoRegret
  rw [Finset.sum_range_succ']
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.range horizon) (fun n => n % window = 0)]
  ring

/--
Under the modified policy, the trajectory-valued forced successor charge is
almost surely the deterministic charge of `forcedAction (n / window)`.
-/
theorem
    blockStartForcedSuccessorPseudoRegret_ae_eq_forcedActionCharge
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (best : Fin K) :
    blockStartForcedSuccessorPseudoRegret
        thetaStar actionFeature best window horizon =ᵐ[
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
          hK lambda actionFeature R delta S forcedAction window)
        environment]
      fun _trajectory =>
        blockStartForcedActionSuccessorPseudoRegret
          thetaStar actionFeature best forcedAction window horizon := by
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
        hK lambda actionFeature R delta S forcedAction window)
      environment
  have hselectors :
      ∀ᵐ trajectory ∂mu, ∀ n,
        n < horizon ->
        n % window = 0 ->
        Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
          forcedAction (n / window) := by
    rw [ae_all_iff]
    intro n
    by_cases hn : n < horizon
    · by_cases hforced : n % window = 0
      · filter_upwards [
          canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryBlockStartForcedTelescopingScalarRidgeAction
            hK lambda actionFeature R delta S forcedAction window environment n] with
          trajectory htrajectory
        intro _hn _hforced
        rw [show Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
            (trajectory (n + 1)).1 by rfl]
        rw [htrajectory]
        exact
          finiteHistoryBlockStartForcedTelescopingScalarRidgeAction_eq_forcedAction_of_mod_eq_zero
            hK lambda actionFeature R delta S forcedAction window n
            (Preorder.frestrictLe n trajectory) hforced
      · exact Filter.Eventually.of_forall (fun _trajectory _hn hcontra =>
          (hforced hcontra).elim)
    · exact Filter.Eventually.of_forall (fun _trajectory hcontra =>
        (hn hcontra).elim)
  filter_upwards [hselectors] with trajectory hselector
  unfold blockStartForcedSuccessorPseudoRegret
    blockStartForcedActionSuccessorPseudoRegret
  apply Finset.sum_congr rfl
  intro n hn
  have hn_range : n < horizon :=
    Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hforced : n % window = 0 :=
    Finset.mem_filter.mp hn |>.2
  rw [hselector n hn_range hforced]

/--
On the all-time confidence event, the modified policy's nonforced successor
pseudo-regret is bounded by its matching scheduled radius-width charge.
-/
theorem
    blockStartOptimisticSuccessorPseudoRegret_le_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (best : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment,
      trajectory ∉
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta ->
        blockStartOptimisticSuccessorPseudoRegret
            thetaStar actionFeature best window horizon trajectory <=
          blockStartOptimisticSuccessorRadiusWidthCharge
            lambda actionFeature R delta S window horizon trajectory := by
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
        hK lambda actionFeature R delta S forcedAction window)
      environment
  have hselectors :
      ∀ᵐ trajectory ∂mu, ∀ n,
        n < horizon ->
        n % window ≠ 0 ->
        Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
          finiteHistoryTelescopingScalarRidgeOptimisticAction
            hK lambda actionFeature R delta S n
            (History.finitePairHistoryOfTrace
              (Thompson.canonicalHistoryTrajectoryAction trajectory)
              (Thompson.canonicalHistoryTrajectoryReward trajectory) n) := by
    rw [ae_all_iff]
    intro n
    by_cases hn : n < horizon
    · by_cases hnonforced : n % window ≠ 0
      · filter_upwards [
          canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryTelescopingScalarRidgeOptimisticAction_of_mod_ne_zero
            hK lambda actionFeature R delta S forcedAction window environment n
            hnonforced] with trajectory htrajectory
        intro _hn _hnonforced
        simpa only [
          Thompson.canonicalHistoryTrajectoryAction,
          Thompson.canonicalHistoryTrajectoryReward] using htrajectory
      · exact Filter.Eventually.of_forall (fun _trajectory _hn hcontra =>
          (hnonforced hcontra).elim)
    · exact Filter.Eventually.of_forall (fun _trajectory hcontra =>
        (hn hcontra).elim)
  filter_upwards [hselectors] with trajectory hselector
  intro hgood
  unfold blockStartOptimisticSuccessorPseudoRegret
    blockStartOptimisticSuccessorRadiusWidthCharge
  apply Finset.sum_le_sum
  intro n hn
  have hn_range : n < horizon :=
    Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hnonforced : n % window ≠ 0 :=
    Finset.mem_filter.mp hn |>.2
  apply
    canonicalHistoryTrajectory_action_succ_gap_le_of_eq_telescopingAction_of_not_mem_confidenceFailure
      hK lambda hlambda thetaStar actionFeature R delta S trajectory n best
      (hselector n hn_range hnonforced)
  intro hfixed
  apply hgood
  unfold allTimeTelescopingScalarRidgeConfidenceFailureSet
  rw [mem_allTimeScheduledScalarRidgeConfidenceFailureSet_iff]
  exact ⟨n + 1, hfixed⟩

/--
Complete finite-horizon pseudo-regret bound for the modified policy on the
all-time confidence event. Forced-round regret remains an explicit charge.
-/
theorem
    canonicalStandardHighProbabilityPseudoRegret_le_initial_add_blockStartForced_add_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (best : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment,
      trajectory ∉
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta ->
        canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory <=
          (linearValue thetaStar (actionFeature best) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction trajectory 0))) +
            blockStartForcedSuccessorPseudoRegret
              thetaStar actionFeature best window horizon trajectory +
            blockStartOptimisticSuccessorRadiusWidthCharge
              lambda actionFeature R delta S window horizon trajectory := by
  filter_upwards [
    blockStartOptimisticSuccessorPseudoRegret_le_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
      hK lambda hlambda thetaStar actionFeature R delta S forcedAction window
      environment horizon best] with trajectory htrajectory
  intro hgood
  rw [
    canonicalStandardHighProbabilityPseudoRegret_eq_initial_add_blockStartForced_add_optimistic
      thetaStar actionFeature best window horizon trajectory]
  gcongr
  exact htrajectory hgood

/--
The modified-policy confidence-event bound with the forced successor charge
written directly in terms of the prescribed forced actions.
-/
theorem
    canonicalStandardHighProbabilityPseudoRegret_le_initial_add_forcedActionCharge_add_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (window : Nat)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (best : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryBlockStartForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction window)
          environment,
      trajectory ∉
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta ->
        canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory <=
          (linearValue thetaStar (actionFeature best) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction trajectory 0))) +
            blockStartForcedActionSuccessorPseudoRegret
              thetaStar actionFeature best forcedAction window horizon +
            blockStartOptimisticSuccessorRadiusWidthCharge
              lambda actionFeature R delta S window horizon trajectory := by
  filter_upwards [
    canonicalStandardHighProbabilityPseudoRegret_le_initial_add_blockStartForced_add_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
      hK lambda hlambda thetaStar actionFeature R delta S forcedAction window
      environment horizon best,
    blockStartForcedSuccessorPseudoRegret_ae_eq_forcedActionCharge
      hK lambda thetaStar actionFeature R delta S forcedAction window
      environment horizon best] with trajectory htrajectory hforced
  intro hgood
  simpa only [hforced] using htrajectory hgood

end OFUL

end BanditRLProof
