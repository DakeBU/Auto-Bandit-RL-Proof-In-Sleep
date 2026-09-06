import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import BanditRLProof.FTRLOneStep

/-!
# Tsallis finite-simplex regularizer wrappers

This module records the first deterministic `Real.rpow` surface for
Tsallis-INF/FTRL routes.  It defines the finite-action Tsallis power sum,
Tsallis entropy, and the negative-entropy regularizer used as an FTRL
regularizer, then packages the small well-definedness side conditions over the
finite simplex.

It does not prove convexity, stability/penalty bounds, self-bounding
conversion, learning-rate optimization, or regret.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- Finite Tsallis power sum `sum_a p_a^alpha`. -/
noncomputable def powerSum {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real) : Real :=
  arms.sum (fun a => (p a) ^ alpha)

/-- Tsallis entropy on a finite action set, with denominator left explicit. -/
noncomputable def entropy {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real) : Real :=
  (powerSum arms alpha p - 1) / (1 - alpha)

/-- Negative Tsallis entropy as the FTRL regularizer convention. -/
noncomputable def negEntropyRegularizer {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real) : Real :=
  - entropy arms alpha p

/-- The Tsallis denominator is nonzero when `alpha != 1`. -/
theorem one_sub_exponent_ne_zero {alpha : Real}
    (halpha : alpha ≠ 1) :
    1 - alpha ≠ 0 := by
  intro h
  apply halpha
  linarith

/-- The Tsallis power sum is nonnegative on the finite simplex. -/
theorem powerSum_nonneg_of_finiteSimplex {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real)
    (hp : FTRL.finiteSimplex arms p) :
    0 <= powerSum arms alpha p := by
  exact Finset.sum_nonneg (fun a ha =>
    Real.rpow_nonneg (hp.1 a ha) alpha)

/--
Well-definedness package for the finite-simplex Tsallis regularizer.

The two facts exposed here are the local obligations needed before later
Tsallis/FTRL leaves can use `Real.rpow` algebra and division by `1 - alpha`.
-/
theorem negEntropyRegularizer_wellDefined_on_finiteSimplex
    {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real)
    (hp : FTRL.finiteSimplex arms p) (halpha : alpha ≠ 1) :
    0 <= powerSum arms alpha p ∧
      1 - alpha ≠ 0 ∧
      negEntropyRegularizer arms alpha p =
        - ((powerSum arms alpha p - 1) / (1 - alpha)) := by
  exact ⟨
    powerSum_nonneg_of_finiteSimplex arms alpha p hp,
    one_sub_exponent_ne_zero halpha,
    rfl⟩

end Tsallis
end BanditRLProof
