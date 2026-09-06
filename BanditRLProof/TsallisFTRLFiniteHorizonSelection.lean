import BanditRLProof.TsallisFTRLMinimizerExistence

/-!
# Canonical half-Tsallis finite-horizon minimizers

This module applies the fixed half-Tsallis minimizer choice to cumulative loss
vectors.  It removes the caller-supplied minimizer certificates from the
deterministic finite-horizon FTRL decomposition and records the successor
indexing needed by importance-weighted updates.

The selected minimizer uses `Classical.choose`.  No measurability of the
history-dependent selector, conditional expectation identity, or bound on the
finite-horizon stability sum is claimed here.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- The fixed half-Tsallis minimizer for losses accumulated before round `t`. -/
noncomputable def halfTsallisCumulativeMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (loss : Nat -> Action -> Real) (t : Nat) : Action -> Real :=
  halfTsallisMinimizer arms harms eta (FTRL.cumulativeLoss loss t)

/-- Every canonical cumulative selector carries the minimizer certificate
required by the finite-horizon FTRL decomposition. -/
theorem halfTsallisCumulativeMinimizer_isRegularizedMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (loss : Nat -> Action -> Real) (t : Nat) :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real))
      (FTRL.cumulativeLoss loss t)
      (halfTsallisCumulativeMinimizer arms harms eta loss t) :=
  halfTsallisMinimizer_isRegularizedMinimizer
    arms harms eta (FTRL.cumulativeLoss loss t)

/-- The selector at `t + 1` is the fixed minimizer after appending round `t`'s
loss vector. -/
theorem halfTsallisCumulativeMinimizer_succ
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (loss : Nat -> Action -> Real) (t : Nat) :
    halfTsallisCumulativeMinimizer arms harms eta loss (t + 1) =
      halfTsallisMinimizer arms harms eta (fun action =>
        FTRL.cumulativeLoss loss t action + loss t action) := by
  rw [halfTsallisCumulativeMinimizer, FTRL.cumulativeLoss_succ]

/-- If the realized round loss is the importance-weighted estimator generated
from the current selector, the successor selector is exactly the canonical
one-step updated minimizer. -/
theorem halfTsallisCumulativeMinimizer_succ_eq_updated
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (loss : Nat -> Action -> Real)
    (rawLoss : Action -> Real) (chosen : Action) (t : Nat)
    (hloss : loss t =
      Exp3.importanceWeightedLoss
        (halfTsallisCumulativeMinimizer arms harms eta loss t)
        rawLoss chosen) :
    halfTsallisCumulativeMinimizer arms harms eta loss (t + 1) =
      halfTsallisUpdatedMinimizer arms harms eta
        (FTRL.cumulativeLoss loss t) rawLoss chosen := by
  rw [halfTsallisCumulativeMinimizer, FTRL.cumulativeLoss_succ, hloss]
  rfl

/-- Finite-horizon half-Tsallis FTRL decomposition with the cumulative
minimizer sequence selected internally.  The remaining first term on the
right is the pathwise stability sum. -/
theorem cumulativeLinearLoss_sub_comparator_le_stability_add_powerSumPenalty_half_canonical
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (loss : Nat -> Action -> Real)
    (q : Action -> Real) (T : Nat)
    (heta : 0 < eta) (hq : FTRL.finiteSimplex arms q) :
    let p := halfTsallisCumulativeMinimizer arms harms eta loss
    (Finset.range T).sum (fun t =>
        FTRL.linearLoss arms (p t) (loss t) -
          FTRL.linearLoss arms q (loss t)) <=
      (Finset.range T).sum (fun t =>
          FTRL.linearLoss arms (p t) (loss t) -
            FTRL.linearLoss arms (p (t + 1)) (loss t)) +
        ((powerSum arms (1 / 2 : Real) (p 0) -
            powerSum arms (1 / 2 : Real) q) /
          (1 - (1 / 2 : Real))) / eta := by
  dsimp only
  exact cumulativeLinearLoss_sub_comparator_le_stability_add_powerSumPenalty
    arms (1 / 2 : Real) eta loss
      (halfTsallisCumulativeMinimizer arms harms eta loss) q T
      (by norm_num) heta
      (fun t _ =>
        halfTsallisCumulativeMinimizer_isRegularizedMinimizer
          arms harms eta loss t)
      hq

end Tsallis
end BanditRLProof
