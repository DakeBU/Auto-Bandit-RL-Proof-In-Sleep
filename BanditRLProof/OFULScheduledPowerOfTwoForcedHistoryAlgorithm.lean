import BanditRLProof.OFULScheduledBlockStartForcedHistoryAlgorithm
import BanditRLProof.OFULScheduledPowerOfTwoForcedIndexCount

/-!
# Power-of-two forced scheduling for telescoping OFUL

This module packages one horizon-independent deterministic history algorithm.
At history indices one below a power of two it selects the arm indexed by that
power's exponent; at every other index it uses the ordinary telescoping OFUL
selector.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal ProbabilityTheory

universe u

namespace OFUL

/--
Use the exponent-indexed forced action at power-of-two successor indices and
the ordinary telescoping OFUL selector at all other history indices.
-/
noncomputable def finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    Fin K :=
  if isPowerOfTwoForcedIndex n then
    forcedAction (Nat.log2 (n + 1))
  else
    finiteHistoryTelescopingScalarRidgeOptimisticAction
      hK lambda actionFeature R delta S n history

/-- The power-of-two forced selector is measurable in its finite history. -/
theorem measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (n : Nat) :
    Measurable
      (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction n) := by
  by_cases hforced : isPowerOfTwoForcedIndex n
  · unfold finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
    simp only [hforced, if_true]
    exact measurable_const
  · unfold finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
    simp only [hforced, if_false]
    simpa only [finiteHistoryTelescopingScalarRidgeOptimisticAction] using
      measurable_finiteHistoryScheduledScalarRidgeOptimisticAction
        hK lambda actionFeature R (allTimeTelescopingDelta delta) S n

/-- The power-of-two forced selector as one deterministic history algorithm. -/
noncomputable def finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K) :
    Thompson.HistoryAlgorithm (Fin K) Real :=
  Thompson.deterministicHistoryAlgorithm
    (Fin.mk 0 hK)
    (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction)
    (measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction)

/-- Every policy section is the Dirac law at the power-of-two selector. -/
@[simp]
theorem
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm_policy_apply
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
      hK lambda actionFeature R delta S forcedAction).policy n history =
        Measure.dirac
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
            hK lambda actionFeature R delta S forcedAction n history) := by
  exact Thompson.deterministicHistoryAlgorithm_policy_apply
    (Fin.mk 0 hK)
    (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction)
    (measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction)
    n history

/--
At history index `2 ^ exponent - 1`, the selector uses the action prescribed
for that exponent.
-/
@[simp]
theorem finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction_pow_sub_one
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (exponent : Nat)
    (history :
      History.FinitePairHistory (Fin K) Real (2 ^ exponent - 1)) :
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction
        (2 ^ exponent - 1) history =
      forcedAction exponent := by
  have hpow : 0 < 2 ^ exponent := pow_pos (by omega) exponent
  have hsucc : 2 ^ exponent - 1 + 1 = 2 ^ exponent := by omega
  have hforced : isPowerOfTwoForcedIndex (2 ^ exponent - 1) :=
    isPowerOfTwoForcedIndex_iff.mpr ⟨exponent, hsucc⟩
  unfold finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
  rw [if_pos hforced, hsucc, Nat.log2_eq_log_two,
    Nat.log_pow Nat.one_lt_two]

/-- Generated successor actions follow the power-of-two selector almost surely. -/
theorem
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      (trajectory (n + 1)).1 =
        finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
          hK lambda actionFeature R delta S forcedAction n
          (Preorder.frestrictLe n trajectory) := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  simpa only [
      finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm,
      Thompson.canonicalHistoryTrajectoryAction,
      Thompson.canonicalHistoryTrajectoryReward] using
    (Thompson.canonicalHistoryTrajectory_action_succ_ae_eq_deterministicHistorySelector
      (Fin.mk 0 hK)
      (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      (measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      environment n)

/-- At successor round `2 ^ exponent`, the generated action is prescribed. -/
theorem
    canonicalHistoryTrajectory_action_pow_ae_eq_forcedAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (exponent : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      (trajectory (2 ^ exponent)).1 = forcedAction exponent := by
  have hpow : 0 < 2 ^ exponent := pow_pos (by omega) exponent
  have hsucc : 2 ^ exponent - 1 + 1 = 2 ^ exponent := by omega
  filter_upwards [
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction environment
      (2 ^ exponent - 1)] with trajectory htrajectory
  rw [← hsucc, htrajectory]
  exact
    finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction_pow_sub_one
      hK lambda actionFeature R delta S forcedAction exponent
      (Preorder.frestrictLe (2 ^ exponent - 1) trajectory)

end OFUL
end BanditRLProof
