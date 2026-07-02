import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Real.Basic
import BanditRLProof.Algorithms.ETCTraceCountLemmas

/-!
# ETC empirical means

This module defines the deterministic empirical mean for a fixed-commit ETC
trace at the configured exploration horizon. It deliberately stays below
probability, measurability, and concentration assumptions.
-/

namespace BanditRLProof
namespace ETC

/--
Empirical mean of arm `a` at the configured ETC exploration horizon for a
fixed-commit trace.

This is the `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` project-local leaf.
-/
def empMeanAtExploration {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) : Rat :=
  sumRewards (ETC.actionWithCommit spec commitArm) reward a
      (spec.explorationPulls * K) /
    (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)

/--
The empirical-mean denominator at the ETC exploration horizon rewrites to the
configured number of exploration pulls per arm.
-/
theorem empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat) := by
  simp [ETC.empMeanAtExploration,
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]

/--
At a positive exploration count, comparing two fixed-commit ETC empirical
means is equivalent to comparing their fixed-horizon reward sums.

This is the `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` deterministic algebra
leaf.  It only removes the common positive denominator from two empirical
means; it does not introduce probability, concentration, filtration, or final
ETC regret.
-/
theorem empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a b : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    ETC.empMeanAtExploration spec commitArm reward b <=
      ETC.empMeanAtExploration spec commitArm reward a ↔
    sumRewards (ETC.actionWithCommit spec commitArm) reward b
        (spec.explorationPulls * K) <=
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
        (spec.explorationPulls * K) := by
  have hc : (0 : Rat) < ((spec.explorationPulls : Nat) : Rat) := by
    exact_mod_cast hexplorationPulls_pos
  rw [ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls]
  rw [ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls]
  exact div_le_div_iff_of_pos_right hc

/--
At a positive exploration count, a pointwise implication from the fixed-horizon
reward-sum comparison into a real finite-sum tail event yields the matching
event inclusion from the non-best empirical-mean comparison event.

This is the `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT` bridge.  It is
only an event-shape adapter; it does not instantiate centered reward
differences, prove sub-Gaussianity, introduce filtrations, or prove final ETC
regret.
-/
theorem empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    {Idx : Type v}
    (idx : Finset Idx)
    (X : Idx -> Omega -> Real)
    (eps : Real)
    (himp :
      forall omega : Omega,
        sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            model.bestArm (spec.explorationPulls * K) <=
          sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            a (spec.explorationPulls * K) ->
        eps <= idx.sum (fun i => X i omega)) :
    Set.Subset
      {omega : Omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm (reward omega)
            model.bestArm}
      {omega : Omega | eps <= idx.sum (fun i => X i omega)} := by
  intro omega hmean
  exact himp omega
    ((ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos
      spec commitArm (reward omega) a model.bestArm
      hexplorationPulls_pos).1 hmean)

end ETC
end BanditRLProof
