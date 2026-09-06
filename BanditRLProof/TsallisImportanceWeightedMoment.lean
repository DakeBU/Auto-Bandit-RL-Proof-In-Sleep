import BanditRLProof.Exp3ImportanceWeighted
import BanditRLProof.TsallisRegularizer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tsallis importance-weighted power moments

This module isolates the finite-sum power-moment calculation used by the
Tsallis-INF stability analysis.  The sampled importance-weighted loss is
weighted by the inverse Hessian scale `p^(2 - alpha)`.  Taking the finite sum
weighted by the sampling masses gives exactly the power-weighted second moment
`sum_i loss_i^2 * p_i^(1 - alpha)`.

The result is deterministic finite-sum algebra.  It does not prove the
preceding Hessian/conjugate-potential stability inequality, identify a
conditional action law, or establish a regret theorem.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- The inverse-Hessian-weighted square of one sampled loss estimate. -/
noncomputable def powerWeightedSquaredImportanceWeightedLoss
    {Action : Type u}
    (arms : Finset Action) (alpha : Real)
    (prob loss : Action -> Real) (chosen : Action) : Real :=
  arms.sum (fun action =>
    (prob action) ^ (2 - alpha) *
      (Exp3.importanceWeightedLoss prob loss chosen action) ^ 2)

/--
Pathwise power-moment identity: only the sampled coordinate remains.
-/
theorem powerWeightedSquaredImportanceWeightedLoss_eq_selected
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (alpha : Real)
    (prob loss : Action -> Real) (chosen : Action)
    (hchosen : chosen ∈ arms) (hprob : 0 < prob chosen) :
    powerWeightedSquaredImportanceWeightedLoss
        arms alpha prob loss chosen =
      (loss chosen) ^ 2 * (prob chosen) ^ (-alpha) := by
  unfold powerWeightedSquaredImportanceWeightedLoss
  rw [Finset.sum_eq_single chosen]
  · simp only [Exp3.importanceWeightedLoss]
    have hpow :
        (prob chosen) ^ (2 - alpha) =
          (prob chosen) ^ (2 : Real) * (prob chosen) ^ (-alpha) := by
      rw [← Real.rpow_add hprob]
      congr 1
    rw [hpow, Real.rpow_two]
    simp only [if_true]
    field_simp [ne_of_gt hprob]
  · intro action _haction hne
    simp [Exp3.importanceWeightedLoss, Ne.symm hne]
  · exact fun hnotmem => (hnotmem hchosen).elim

/--
The sampling-mass-weighted finite sum equals the power-weighted loss square.
-/
theorem sum_prob_mul_powerWeightedSquaredImportanceWeightedLoss_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (alpha : Real)
    (prob loss : Action -> Real)
    (hprob : forall action, action ∈ arms -> 0 < prob action) :
    arms.sum (fun chosen =>
        prob chosen *
          powerWeightedSquaredImportanceWeightedLoss
            arms alpha prob loss chosen) =
      arms.sum (fun action =>
        (loss action) ^ 2 * (prob action) ^ (1 - alpha)) := by
  apply Finset.sum_congr rfl
  intro chosen hchosen
  rw [powerWeightedSquaredImportanceWeightedLoss_eq_selected
    arms alpha prob loss chosen hchosen (hprob chosen hchosen)]
  rw [show (1 - alpha : Real) = 1 + (-alpha) by ring,
    Real.rpow_add (hprob chosen hchosen), Real.rpow_one]
  ring

/--
For losses in `[0,1]`, the Tsallis importance-weighted power moment is bounded
by the finite power sum with exponent `1 - alpha`.
-/
theorem sum_prob_mul_powerWeightedSquaredImportanceWeightedLoss_le_powerSum
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (alpha : Real)
    (prob loss : Action -> Real)
    (hprob : forall action, action ∈ arms -> 0 < prob action)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    arms.sum (fun chosen =>
        prob chosen *
          powerWeightedSquaredImportanceWeightedLoss
            arms alpha prob loss chosen) <=
      powerSum arms (1 - alpha) prob := by
  rw [sum_prob_mul_powerWeightedSquaredImportanceWeightedLoss_eq
    arms alpha prob loss hprob]
  unfold powerSum
  apply Finset.sum_le_sum
  intro action haction
  have hl := hloss action haction
  have hpow : 0 <= (prob action) ^ (1 - alpha) :=
    Real.rpow_nonneg (le_of_lt (hprob action haction)) (1 - alpha)
  nlinarith [sq_nonneg (loss action), mul_self_le_mul_self hl.1 hl.2]

end Tsallis
end BanditRLProof
