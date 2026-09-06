import BanditRLProof.Exp3PredictableMoments

/-!
# Pathwise Hedge control for the concrete sampled EXP3 score

This module identifies the recursively accumulated `sampledHistoryScore` with
the deterministic cumulative-loss surface used by `Exp3HedgeRegret`.  It also
identifies the corresponding pure exponential-weights distribution and the
exploration-mixed trajectory probability.  The final theorem specializes the
deterministic second-order Hedge bound to one concrete sampled trajectory.

The result is pathwise.  Its scalar-feedback nonnegativity premise is intended
to be discharged almost surely by the predictable `[0,1]` reward law before
integrating the bound.
-/

namespace BanditRLProof
namespace Exp3

universe u v

/-- The complete importance-weighted loss vector observed at an actual time. -/
noncomputable def sampledTrajectoryObservedLoss
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    Nat -> Action -> Real :=
  fun t action =>
    observedImportanceWeightedLossAt arms eta gamma t sample action

@[simp]
theorem previousPairHistory_frestrictLe
    {Action : Type v} (n : Nat)
    (trajectory : (k : Nat) -> Action × Real) :
    previousPairHistory (Preorder.frestrictLe (n + 1) trajectory) =
      Preorder.frestrictLe n trajectory := by
  funext i
  rfl

/-- The inclusive sampled score through `n` is Hedge cumulative loss at `n+1`. -/
theorem sampledHistoryScore_frestrictLe_eq_cumulativeLoss
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (sample : Env × ((k : Nat) -> Action × Real))
    (n : Nat) (action : Action) :
    sampledHistoryScore arms eta gamma n
        (Preorder.frestrictLe n sample.2) action =
      cumulativeLoss (sampledTrajectoryObservedLoss arms eta gamma sample)
        (n + 1) action := by
  induction n with
  | zero =>
      simp [sampledTrajectoryObservedLoss, cumulativeLoss,
        observedImportanceWeightedLossAt, sampledTrajectoryProbabilityAt]
  | succ n ih =>
      rw [sampledHistoryScore_succ, previousPairHistory_frestrictLe, ih]
      rw [show cumulativeLoss
            (sampledTrajectoryObservedLoss arms eta gamma sample) (n + 1 + 1) action =
          cumulativeLoss (sampledTrajectoryObservedLoss arms eta gamma sample)
              (n + 1) action +
            sampledTrajectoryObservedLoss arms eta gamma sample (n + 1) action by
        exact cumulativeLoss_succ
          (sampledTrajectoryObservedLoss arms eta gamma sample) (n + 1) action]
      rfl

/-- At a successor time, the Hedge distribution is the normalized sampled score. -/
theorem distribution_sampledTrajectoryObservedLoss_succ
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (sample : Env × ((k : Nat) -> Action × Real))
    (n : Nat) (action : Action) :
    distribution arms eta (sampledTrajectoryObservedLoss arms eta gamma sample)
        (n + 1) action =
      normalizedHistoryDistribution arms eta
        (sampledHistoryScore arms eta gamma n)
        (Preorder.frestrictLe n sample.2) action := by
  unfold distribution weight totalWeight normalizedHistoryDistribution
    historyWeight historyTotalWeight
  rw [sampledHistoryScore_frestrictLe_eq_cumulativeLoss]
  congr 1
  apply Finset.sum_congr rfl
  intro candidate _hcandidate
  unfold weight historyWeight
  rw [sampledHistoryScore_frestrictLe_eq_cumulativeLoss]

/-- The concrete sampling law is uniform exploration mixed with the Hedge law. -/
theorem sampledTrajectoryProbabilityAt_eq_mix_distribution
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) (action : Action) :
    sampledTrajectoryProbabilityAt arms eta gamma t sample action =
      (1 - gamma) *
          distribution arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t action +
        gamma / (arms.card : Real) := by
  cases t with
  | zero =>
      rfl
  | succ n =>
      rw [sampledTrajectoryProbabilityAt]
      unfold sampledHistoryDistribution exploredHistoryDistribution
      rw [← distribution_sampledTrajectoryObservedLoss_succ]

theorem sampledTrajectoryProbabilityAt_nonneg
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) (action : Action) :
    0 <= sampledTrajectoryProbabilityAt arms eta gamma t sample action := by
  cases t with
  | zero =>
      simpa [sampledTrajectoryProbabilityAt, initialExploredDistribution] using
        (exploredHistoryDistribution_nonneg arms harms eta gamma
          (fun _ : Unit => fun _ => 0) hgamma_nonneg hgamma_le_one () action)
  | succ n =>
      simpa [sampledTrajectoryProbabilityAt, sampledHistoryDistribution] using
        (exploredHistoryDistribution_nonneg arms harms eta gamma
          (sampledHistoryScore arms eta gamma n) hgamma_nonneg hgamma_le_one
          (Preorder.frestrictLe n sample.2) action)

theorem sampledTrajectoryObservedLoss_nonneg
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (sample : Env × ((k : Nat) -> Action × Real))
    (t : Nat) (action : Action) (hreward : 0 <= (sample.2 t).2) :
    0 <= sampledTrajectoryObservedLoss arms eta gamma sample t action := by
  apply importanceWeightedLoss_nonneg
  · exact sampledTrajectoryProbabilityAt_nonneg arms harms eta gamma
      hgamma_nonneg hgamma_le_one t sample action
  · exact hreward

/-- Concrete finite-horizon sampled-trajectory specialization of Hedge. -/
theorem sampledTrajectory_hedge_regret_le
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (sample : Env × ((k : Nat) -> Action × Real)) (horizon : Nat)
    (hreward_nonneg : forall t, t < horizon -> 0 <= (sample.2 t).2)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    (Finset.range horizon).sum (fun t =>
        mixedLoss arms eta
          (sampledTrajectoryObservedLoss arms eta gamma sample) t) -
        cumulativeLoss (sampledTrajectoryObservedLoss arms eta gamma sample)
          horizon comparator <=
      Real.log arms.card / eta +
        eta * (Finset.range horizon).sum (fun t =>
          mixedSquaredLoss arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t) := by
  apply hedge_regret_le_log_card_div_add_eta_mul_mixedSquaredLoss_of_nonneg
    arms harms eta heta
      (sampledTrajectoryObservedLoss arms eta gamma sample) horizon
  · intro t ht action _haction
    exact sampledTrajectoryObservedLoss_nonneg arms harms eta gamma
      hgamma_nonneg hgamma_le_one sample t action (hreward_nonneg t ht)
  · exact hcomparator

/-- The same pathwise Hedge bound with its comparator term exposed as the
concrete inclusive `sampledHistoryScore`. -/
theorem sampledHistoryScore_hedge_regret_le
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (sample : Env × ((k : Nat) -> Action × Real)) (n : Nat)
    (hreward_nonneg : forall t, t < n + 1 -> 0 <= (sample.2 t).2)
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    (Finset.range (n + 1)).sum (fun t =>
        mixedLoss arms eta
          (sampledTrajectoryObservedLoss arms eta gamma sample) t) -
        sampledHistoryScore arms eta gamma n
          (Preorder.frestrictLe n sample.2) comparator <=
      Real.log arms.card / eta +
        eta * (Finset.range (n + 1)).sum (fun t =>
          mixedSquaredLoss arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t) := by
  rw [sampledHistoryScore_frestrictLe_eq_cumulativeLoss]
  exact sampledTrajectory_hedge_regret_le arms harms eta gamma heta
    hgamma_nonneg hgamma_le_one sample (n + 1) hreward_nonneg
      comparator hcomparator

end Exp3
end BanditRLProof
