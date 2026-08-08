import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import BanditRLProof.Exp3HedgeRegret

/-!
# Finite-action importance-weighted loss identities

This module supplies the finite-distribution algebra immediately above the
deterministic Hedge theorem and below the probabilistic EXP3 process.  It proves
the estimator's armwise weighted-sum cancellation and exact mixed-square identity on
an explicit finite action set.

These statements are deterministic finite sums.  Calling them conditional
expectation facts requires a later law-transport theorem identifying the
conditional action law with the supplied probabilities.
-/

namespace BanditRLProof
namespace Exp3

universe u

/-- Loss estimate that reveals only the loss of the sampled action. -/
noncomputable def importanceWeightedLoss {Action : Type u}
    (prob loss : Action -> Real) (chosen action : Action) : Real := by
  classical
  exact if chosen = action then loss action / prob action else 0

/-- The loss mixed by `prob` after replacing losses by one sampled estimate. -/
noncomputable def mixedImportanceWeightedLoss {Action : Type u}
    (arms : Finset Action) (prob loss : Action -> Real) (chosen : Action) : Real :=
  arms.sum (fun action =>
    prob action * importanceWeightedLoss prob loss chosen action)

/-- An importance-weighted estimate mixed by weights that may differ from the
sampling probabilities used in the estimator denominator. -/
noncomputable def weightedImportanceWeightedLoss {Action : Type u}
    (arms : Finset Action) (prob weight loss : Action -> Real)
    (chosen : Action) : Real :=
  arms.sum (fun action =>
    weight action * importanceWeightedLoss prob loss chosen action)

/-- The mixed square of one sampled importance-weighted loss vector. -/
noncomputable def mixedSquaredImportanceWeightedLoss {Action : Type u}
    (arms : Finset Action) (prob loss : Action -> Real) (chosen : Action) : Real :=
  arms.sum (fun action =>
    prob action * (importanceWeightedLoss prob loss chosen action) ^ 2)

theorem importanceWeightedLoss_nonneg {Action : Type u} [DecidableEq Action]
    {prob loss : Action -> Real} {chosen action : Action}
    (hprob : 0 <= prob action) (hloss : 0 <= loss action) :
    0 <= importanceWeightedLoss prob loss chosen action := by
  unfold importanceWeightedLoss
  split_ifs
  · exact div_nonneg hloss hprob
  · exact le_refl 0

/-- The probability-weighted finite sum of one coordinate recovers its loss. -/
theorem sum_prob_mul_importanceWeightedLoss_eq_loss {Action : Type u}
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (action : Action) (haction : action ∈ arms)
    (hprob : prob action ≠ 0) :
    arms.sum (fun chosen =>
        prob chosen * importanceWeightedLoss prob loss chosen action) =
      loss action := by
  rw [Finset.sum_eq_single action]
  · simp [importanceWeightedLoss]
    rw [mul_comm]
    exact div_mul_cancel₀ _ hprob
  · intro chosen hchosen hne
    simp [importanceWeightedLoss, hne]
  · exact fun hnotmem => (hnotmem haction).elim

/-- Pathwise cancellation: the mixed estimate is the sampled loss. -/
theorem mixedImportanceWeightedLoss_eq_selectedLoss {Action : Type u}
    [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (chosen : Action) (hchosen : chosen ∈ arms)
    (hprob : prob chosen ≠ 0) :
    mixedImportanceWeightedLoss arms prob loss chosen = loss chosen := by
  unfold mixedImportanceWeightedLoss
  rw [Finset.sum_eq_single chosen]
  · simp [importanceWeightedLoss]
    rw [mul_comm]
    exact div_mul_cancel₀ _ hprob
  · intro action haction hne
    simp [importanceWeightedLoss, Ne.symm hne]
  · exact fun hnotmem => (hnotmem hchosen).elim

/-- Averaging the pathwise mixed estimate recovers the true mixed loss. -/
theorem sum_prob_mul_mixedImportanceWeightedLoss_eq_mixedLoss
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hprob : forall action, action ∈ arms -> prob action ≠ 0) :
    arms.sum (fun chosen =>
        prob chosen * mixedImportanceWeightedLoss arms prob loss chosen) =
      arms.sum (fun action => prob action * loss action) := by
  apply Finset.sum_congr rfl
  intro chosen hchosen
  rw [mixedImportanceWeightedLoss_eq_selectedLoss arms prob loss chosen hchosen
    (hprob chosen hchosen)]

/-- Averaging an estimator mixed by arbitrary predictable weights recovers
the same weighted true loss. -/
theorem sum_prob_mul_weightedImportanceWeightedLoss_eq_weightedLoss
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob weight loss : Action -> Real)
    (hprob : forall action, action ∈ arms -> prob action ≠ 0) :
    arms.sum (fun chosen =>
        prob chosen *
          weightedImportanceWeightedLoss arms prob weight loss chosen) =
      arms.sum (fun action => weight action * loss action) := by
  unfold weightedImportanceWeightedLoss
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro action haction
  calc
    arms.sum (fun chosen =>
        prob chosen *
          (weight action * importanceWeightedLoss prob loss chosen action)) =
        weight action * arms.sum (fun chosen =>
          prob chosen * importanceWeightedLoss prob loss chosen action) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chosen _hchosen
      ring
    _ = weight action * loss action := by
      rw [sum_prob_mul_importanceWeightedLoss_eq_loss
        arms prob loss action haction (hprob action haction)]

/-- Exact pathwise mixed-square formula for a sampled action. -/
theorem mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (chosen : Action) (hchosen : chosen ∈ arms)
    (hprob : prob chosen ≠ 0) :
    mixedSquaredImportanceWeightedLoss arms prob loss chosen =
      (loss chosen) ^ 2 / prob chosen := by
  unfold mixedSquaredImportanceWeightedLoss
  rw [Finset.sum_eq_single chosen]
  · simp [importanceWeightedLoss]
    field_simp
  · intro action haction hne
    simp [importanceWeightedLoss, Ne.symm hne]
  · exact fun hnotmem => (hnotmem hchosen).elim

/-- Exact probability-weighted finite sum of the mixed estimator's square. -/
theorem sum_prob_mul_mixedSquaredImportanceWeightedLoss_eq_sum_loss_sq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hprob : forall action, action ∈ arms -> prob action ≠ 0) :
    arms.sum (fun chosen =>
        prob chosen *
          mixedSquaredImportanceWeightedLoss arms prob loss chosen) =
      arms.sum (fun action => (loss action) ^ 2) := by
  apply Finset.sum_congr rfl
  intro chosen hchosen
  rw [mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div
    arms prob loss chosen hchosen (hprob chosen hchosen)]
  exact mul_div_cancel₀ _ (hprob chosen hchosen)

/-- For losses in `[0,1]`, the probability-weighted mixed square is at most the arm count. -/
theorem sum_prob_mul_mixedSquaredImportanceWeightedLoss_le_card
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hprob : forall action, action ∈ arms -> prob action ≠ 0)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    arms.sum (fun chosen =>
        prob chosen *
          mixedSquaredImportanceWeightedLoss arms prob loss chosen) <=
      arms.card := by
  rw [sum_prob_mul_mixedSquaredImportanceWeightedLoss_eq_sum_loss_sq
    arms prob loss hprob]
  calc
    arms.sum (fun action => (loss action) ^ 2) <=
        arms.sum (fun _action => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro action haction
      nlinarith [(hloss action haction).1, (hloss action haction).2]
    _ = arms.card := by simp

end Exp3
end BanditRLProof
