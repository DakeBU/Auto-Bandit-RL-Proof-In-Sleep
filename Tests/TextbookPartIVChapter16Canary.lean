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

example {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (hchanged : 0 < gap changedArm)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound)
    (hA : history ∈ oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound) :
    ENNReal.ofReal
        (((lastRound + 1 : Nat) : Real) * gap changedArm / 2) <=
      finiteHistoryGapPseudoRegret gap lastRound history :=
  oneArmMajority_forces_gapPseudoRegret
    gap hgap changedArm hchanged lastRound history hA

example {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (changedMargin : Real)
    (hmargin : 0 < changedMargin)
    (hother : forall arm, arm ≠ changedArm -> changedMargin <= gap arm)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound)
    (hAc : history ∈ (oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound)ᶜ) :
    ENNReal.ofReal
        (((lastRound + 1 : Nat) : Real) * changedMargin / 2) <=
      finiteHistoryGapPseudoRegret gap lastRound history :=
  oneArmMajority_compl_forces_gapPseudoRegret
    gap hgap changedArm changedMargin hmargin hother lastRound history hAc

#check banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed
#check finiteHistoryGapPseudoRegret
#check canonicalGapExpectedPseudoRegret
#check canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls
#check oneArmMajority_probability_charge_le_expectedPseudoRegret
#check oneArmMajority_compl_probability_charge_le_expectedPseudoRegret
#check bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
#check bretagnolleHuberScale_mul_eq_exp
#check exp_testing_bound_of_majority_regret_bounds
#check expectedPullCount_ge_log_regret_of_exp_testing_bound
#check expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed

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
#print axioms LowerBounds.canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls
#print axioms LowerBounds.oneArmMajority_forces_gapPseudoRegret
#print axioms LowerBounds.oneArmMajority_compl_forces_gapPseudoRegret
#print axioms LowerBounds.oneArmMajority_probability_charge_le_expectedPseudoRegret
#print axioms LowerBounds.oneArmMajority_compl_probability_charge_le_expectedPseudoRegret
#print axioms LowerBounds.bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
#print axioms LowerBounds.bretagnolleHuberScale_mul_eq_exp
#print axioms LowerBounds.exp_testing_bound_of_majority_regret_bounds
#print axioms LowerBounds.expectedPullCount_ge_log_regret_of_exp_testing_bound
#print axioms LowerBounds.expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed

end LowerBounds
end BanditRLProof
