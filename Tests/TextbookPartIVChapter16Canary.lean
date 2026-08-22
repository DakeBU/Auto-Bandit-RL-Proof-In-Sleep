import BanditRLProof

/-!
# Typed public canary for Part IV, Chapter 16

The examples below exercise only the compiled dependency slice.  They do not
claim the source terminals Theorem 16.2, Lemma 16.3, or Theorem 16.4.
-/

namespace BanditRLProof
namespace LowerBounds

open Filter MeasureTheory
open scoped ENNReal Topology

example {first second : Nat -> Real}
    (hfirst : IsConsistentRegret first)
    (hsecond : IsConsistentRegret second) :
    IsConsistentRegret (fun n => first n + second n) :=
  hfirst.add hsecond

example {first second : Nat -> Real}
    (hfirst : IsConsistentRegret first)
    (hsecond : IsConsistentRegret second) :
    ∀ᶠ n : Nat in atTop,
      first n + second n <= (n : Real) ^ (1 / 2 : Real) := by
  exact hfirst.eventually_add_le_rpow hsecond (by norm_num)

example :
    unitGaussianDivergenceInfimum 0 1 <=
      ENNReal.ofReal (((1 : Real) + 1 / 4) ^ 2 / 2) := by
  simpa using unitGaussianDivergenceInfimum_le_perturbed
    (0 : Real) 1 (1 / 4) (by norm_num)

example :
    unitGaussianDivergenceInfimum 0 1 = ENNReal.ofReal (1 / 2 : Real) := by
  simpa using unitGaussianDivergenceInfimum_eq (0 : Real) 1 (by norm_num)

example {K : Nat} {Reward : Type*} [MeasurableSpace Reward]
    (changedArm : Fin K) (lastRound : Nat) :
    MeasurableSet
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound) :=
  measurableSet_oneArmMajorityPullEvent changedArm lastRound

#check banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed
#check bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
#check bretagnolleHuberScale_mul_eq_exp
#check exp_testing_bound_of_majority_regret_bounds
#check expectedPullCount_ge_log_regret_of_exp_testing_bound

#print axioms LowerBounds.IsConsistentRegret.add
#print axioms LowerBounds.IsConsistentRegret.eventually_add_le_rpow
#print axioms LowerBounds.IsConsistentRegret.eventually_log_add_div_log_le
#print axioms LowerBounds.divergenceInfimum_le
#print axioms LowerBounds.parametricDivergenceInfimum_le
#print axioms LowerBounds.unitGaussianDivergenceInfimum_le_perturbed
#print axioms LowerBounds.unitGaussianDivergenceInfimum_ge
#print axioms LowerBounds.unitGaussianDivergenceInfimum_eq
#print axioms LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed
#print axioms LowerBounds.measurableSet_oneArmMajorityPullEvent
#print axioms LowerBounds.bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
#print axioms LowerBounds.bretagnolleHuberScale_mul_eq_exp
#print axioms LowerBounds.exp_testing_bound_of_majority_regret_bounds
#print axioms LowerBounds.expectedPullCount_ge_log_regret_of_exp_testing_bound

end LowerBounds
end BanditRLProof
