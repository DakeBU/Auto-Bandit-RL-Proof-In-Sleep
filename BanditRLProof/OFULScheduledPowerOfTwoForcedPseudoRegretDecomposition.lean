import BanditRLProof.OFULScheduledPowerOfTwoForcedHistoryAlgorithm

/-!
# Pseudo-regret decomposition for power-of-two forced telescoping OFUL

This module separates the complete finite-horizon pseudo-regret of the
horizon-independent power-of-two forced policy into the initial action,
power-of-two forced successor actions, and ordinary optimistic successor
actions. The successor index `n` denotes the history used to select action
`n + 1`.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal ProbabilityTheory

universe u

namespace OFUL

/-- Away from forced indices, the modified selector is the telescoping selector. -/
theorem
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction_eq_of_not_forced
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (hnonforced : ¬ isPowerOfTwoForcedIndex n) :
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction n history =
      finiteHistoryTelescopingScalarRidgeOptimisticAction
        hK lambda actionFeature R delta S n history := by
  simp [
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction,
    hnonforced]

/-- At a forced index, the selector uses the action indexed by its exponent. -/
theorem
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction_eq_forcedAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (hforced : isPowerOfTwoForcedIndex n) :
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction n history =
      forcedAction (Nat.log2 (n + 1)) := by
  simp [
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction,
    hforced]

/--
Under the modified policy's own trajectory law, every nonforced successor
action agrees almost surely with the ordinary telescoping OFUL selector.
-/
theorem
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryTelescopingScalarRidgeOptimisticAction_of_not_powerOfTwoForced
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat)
    (hnonforced : ¬ isPowerOfTwoForcedIndex n) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      (trajectory (n + 1)).1 =
        finiteHistoryTelescopingScalarRidgeOptimisticAction
          hK lambda actionFeature R delta S n
          (Preorder.frestrictLe n trajectory) := by
  filter_upwards [
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction environment n] with
    trajectory htrajectory
  rw [htrajectory]
  exact
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction_eq_of_not_forced
      hK lambda actionFeature R delta S forcedAction n
      (Preorder.frestrictLe n trajectory) hnonforced

/-- At any forced successor index, the generated action is the indexed arm. -/
theorem
    canonicalHistoryTrajectory_action_succ_ae_eq_forcedAction_of_powerOfTwoForced
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat)
    (hforced : isPowerOfTwoForcedIndex n) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      (trajectory (n + 1)).1 =
        forcedAction (Nat.log2 (n + 1)) := by
  filter_upwards [
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction environment n] with
    trajectory htrajectory
  rw [htrajectory]
  exact
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction_eq_forcedAction
      hK lambda actionFeature R delta S forcedAction n
      (Preorder.frestrictLe n trajectory) hforced

/-- Successor pseudo-regret charged at power-of-two forced indices. -/
noncomputable def powerOfTwoForcedSuccessorPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (horizon : Nat)
    (trajectory : Nat -> Fin K × Real) : Real :=
  (powerOfTwoForcedIndexSet horizon).sum (fun n =>
    linearValue thetaStar (actionFeature best) -
      linearValue thetaStar
        (actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1))))

/-- Deterministic successor charge of the prescribed forced actions. -/
noncomputable def powerOfTwoForcedActionSuccessorPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (forcedAction : Nat -> Fin K)
    (horizon : Nat) : Real :=
  (powerOfTwoForcedIndexSet horizon).sum (fun n =>
    linearValue thetaStar (actionFeature best) -
      linearValue thetaStar
        (actionFeature (forcedAction (Nat.log2 (n + 1)))))

/-- Successor pseudo-regret charged to nonforced optimistic actions. -/
noncomputable def powerOfTwoOptimisticSuccessorPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (horizon : Nat)
    (trajectory : Nat -> Fin K × Real) : Real :=
  ((Finset.range horizon).filter
      (fun n => ¬ isPowerOfTwoForcedIndex n)).sum (fun n =>
    linearValue thetaStar (actionFeature best) -
      linearValue thetaStar
        (actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1))))

/--
Complete pseudo-regret through action `horizon` is the initial gap plus the
power-of-two forced and nonforced optimistic successor charges.
-/
theorem
    canonicalStandardHighProbabilityPseudoRegret_eq_initial_add_powerOfTwoForced_add_optimistic
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (horizon : Nat)
    (trajectory : Nat -> Fin K × Real) :
    canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory =
      (linearValue thetaStar (actionFeature best) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction trajectory 0))) +
        powerOfTwoForcedSuccessorPseudoRegret
          thetaStar actionFeature best horizon trajectory +
        powerOfTwoOptimisticSuccessorPseudoRegret
          thetaStar actionFeature best horizon trajectory := by
  unfold canonicalStandardHighProbabilityPseudoRegret
    canonicalHistoryTrajectorySumRangeAllGap
    powerOfTwoForcedSuccessorPseudoRegret
    powerOfTwoOptimisticSuccessorPseudoRegret
    powerOfTwoForcedIndexSet
  rw [Finset.sum_range_succ']
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.range horizon) (fun n => isPowerOfTwoForcedIndex n)]
  ring

/--
Under the power-of-two forced policy, its trajectory-valued forced successor
charge is almost surely the deterministic prescribed-action charge.
-/
theorem
    powerOfTwoForcedSuccessorPseudoRegret_ae_eq_forcedActionCharge
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat)
    (best : Fin K) :
    powerOfTwoForcedSuccessorPseudoRegret
        thetaStar actionFeature best horizon =ᵐ[
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
          hK lambda actionFeature R delta S forcedAction)
        environment]
      fun _trajectory =>
        powerOfTwoForcedActionSuccessorPseudoRegret
          thetaStar actionFeature best forcedAction horizon := by
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
        hK lambda actionFeature R delta S forcedAction)
      environment
  have hselectors :
      ∀ᵐ trajectory ∂mu, ∀ n,
        n < horizon ->
        isPowerOfTwoForcedIndex n ->
        Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
          forcedAction (Nat.log2 (n + 1)) := by
    rw [ae_all_iff]
    intro n
    by_cases hn : n < horizon
    · by_cases hforced : isPowerOfTwoForcedIndex n
      · filter_upwards [
          canonicalHistoryTrajectory_action_succ_ae_eq_forcedAction_of_powerOfTwoForced
            hK lambda actionFeature R delta S forcedAction environment n
            hforced] with trajectory htrajectory
        intro _hn _hforced
        simpa only [Thompson.canonicalHistoryTrajectoryAction] using htrajectory
      · exact Filter.Eventually.of_forall (fun _trajectory _hn hcontra =>
          (hforced hcontra).elim)
    · exact Filter.Eventually.of_forall (fun _trajectory hcontra =>
        (hn hcontra).elim)
  filter_upwards [hselectors] with trajectory hselector
  unfold powerOfTwoForcedSuccessorPseudoRegret
    powerOfTwoForcedActionSuccessorPseudoRegret
  apply Finset.sum_congr rfl
  intro n hn
  have hn_range : n < horizon :=
    Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hforced : isPowerOfTwoForcedIndex n :=
    Finset.mem_filter.mp hn |>.2
  rw [hselector n hn_range hforced]

/--
The complete pathwise decomposition with its forced term already replaced by
the deterministic prescribed-action charge almost surely.
-/
theorem
    canonicalStandardHighProbabilityPseudoRegret_ae_eq_initial_add_powerOfTwoForcedAction_add_optimistic
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat)
    (best : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory =
        (linearValue thetaStar (actionFeature best) -
            linearValue thetaStar
              (actionFeature
                (Thompson.canonicalHistoryTrajectoryAction trajectory 0))) +
          powerOfTwoForcedActionSuccessorPseudoRegret
            thetaStar actionFeature best forcedAction horizon +
          powerOfTwoOptimisticSuccessorPseudoRegret
            thetaStar actionFeature best horizon trajectory := by
  filter_upwards [
    powerOfTwoForcedSuccessorPseudoRegret_ae_eq_forcedActionCharge
      hK lambda thetaStar actionFeature R delta S forcedAction
      environment horizon best] with trajectory hforced
  rw [
    canonicalStandardHighProbabilityPseudoRegret_eq_initial_add_powerOfTwoForced_add_optimistic
      thetaStar actionFeature best horizon trajectory,
    hforced]

end OFUL
end BanditRLProof
