import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import BanditRLProof.Algorithms.ETCEmpiricalMean
import BanditRLProof.MathlibWrappers

/-!
# ETC reward-difference finite-sum bridge

This module bridges the fixed-horizon `sumRewards` comparison produced by the
ETC empirical-mean algebra layer to a centered pairwise finite-sum event.  It
stays deterministic: no probability measure, independence, sub-Gaussianity,
filtration, conditional expectation, or final ETC result is introduced here.
-/

namespace BanditRLProof
namespace ETC

/--
Real-valued centered pairwise reward-difference summand for arm `a` against
the model's selected best arm at one ETC exploration-horizon time index.

The expression remains deterministic and pointwise.  Future probability
leaves may impose independence or sub-Gaussian contracts on this function.
-/
noncomputable def centeredPairwiseRewardDiff
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat) (omega : Omega) : Real :=
  (((if ETC.actionWithCommit spec commitArm t = a then
      reward omega t - model.mean a else 0) +
    (if ETC.actionWithCommit spec commitArm t = model.bestArm then
      model.mean model.bestArm - reward omega t else 0) : Rat) : Real)

/--
Real-valued threshold corresponding to `explorationPulls` copies of the
mean gap between the selected best arm and arm `a`.
-/
noncomputable def centeredPairwiseGapThreshold
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (a : Fin K) : Real :=
  (((spec.explorationPulls : Rat) *
    (model.mean model.bestArm - model.mean a) : Rat) : Real)

/--
The selected centered reward sum for one arm equals its selected reward total
minus its pull count times the supplied mean.

This helper is part of the `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET` bridge.  It
uses the existing Mathlib-backed `sumRewards` and `pullCount` Finset wrappers.
-/
theorem selectedSubMean_sum_eq_sumRewards_sub_pullCount_mul
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Rat)
    (a : Action) (n : Nat) (mu : Rat) :
    (Finset.range n).sum
      (fun t : Nat => if action t = a then reward t - mu else 0) =
      sumRewards action reward a n - (pullCount action a n : Rat) * mu := by
  classical
  calc
    (Finset.range n).sum
        (fun t : Nat => if action t = a then reward t - mu else 0)
        = ((Finset.range n).filter (fun t : Nat => action t = a)).sum
            (fun t : Nat => reward t - mu) := by
          rw [Finset.sum_filter]
    _ = ((Finset.range n).filter (fun t : Nat => action t = a)).sum
            (fun t : Nat => reward t) -
          ((Finset.range n).filter (fun t : Nat => action t = a)).sum
            (fun _t : Nat => mu) := by
          rw [Finset.sum_sub_distrib]
    _ = sumRewards action reward a n -
          (((Finset.range n).filter
            (fun t : Nat => action t = a)).card : Rat) * mu := by
          have hsum :
              ((Finset.range n).filter
                (fun t : Nat => action t = a)).sum
                (fun t : Nat => reward t) =
                sumRewards action reward a n := by
            exact
              (sumRewards_eq_finset_filter_sum
                (action := action) (reward := reward) (a := a)
                (t := n)).symm
          rw [hsum]
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, mul_comm]
    _ = sumRewards action reward a n - (pullCount action a n : Rat) * mu := by
          have hcount :=
            pullCount_eq_finset_filter_card
              (action := action) (a := a) (t := n)
          rw [hcount.symm]

/--
The selected negative centered reward sum for one arm equals its pull count
times the supplied mean minus its selected reward total.

This is the best-arm companion to
`selectedSubMean_sum_eq_sumRewards_sub_pullCount_mul`.
-/
theorem meanSubSelected_sum_eq_pullCount_mul_sub_sumRewards
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Rat)
    (a : Action) (n : Nat) (mu : Rat) :
    (Finset.range n).sum
      (fun t : Nat => if action t = a then mu - reward t else 0) =
      (pullCount action a n : Rat) * mu - sumRewards action reward a n := by
  classical
  calc
    (Finset.range n).sum
        (fun t : Nat => if action t = a then mu - reward t else 0)
        = ((Finset.range n).filter (fun t : Nat => action t = a)).sum
            (fun t : Nat => mu - reward t) := by
          rw [Finset.sum_filter]
    _ = ((Finset.range n).filter (fun t : Nat => action t = a)).sum
            (fun _t : Nat => mu) -
          ((Finset.range n).filter (fun t : Nat => action t = a)).sum
            (fun t : Nat => reward t) := by
          rw [Finset.sum_sub_distrib]
    _ = (((Finset.range n).filter
            (fun t : Nat => action t = a)).card : Rat) * mu -
          sumRewards action reward a n := by
          have hsum :
              ((Finset.range n).filter
                (fun t : Nat => action t = a)).sum
                (fun t : Nat => reward t) =
                sumRewards action reward a n := by
            exact
              (sumRewards_eq_finset_filter_sum
                (action := action) (reward := reward) (a := a)
                (t := n)).symm
          rw [hsum]
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, mul_comm]
    _ = (pullCount action a n : Rat) * mu -
          sumRewards action reward a n := by
          have hcount :=
            pullCount_eq_finset_filter_card
              (action := action) (a := a) (t := n)
          rw [hcount.symm]

/--
If two arms have the same pull count by a horizon and the fixed-horizon reward
sum of `b` is at most that of `a`, then the centered pairwise reward-difference
finite sum is at least `m * (muB - muA)`.

This is the deterministic algebra core of
`ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET`.  The equal-count assumptions are kept
explicit so ETC can discharge them with its exploration-horizon count theorem.
-/
theorem sumRewards_le_imp_centered_pairwise_sum_ge
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Rat)
    (a b : Action) (n m : Nat) (muA muB : Rat)
    (hcount_a : pullCount action a n = m)
    (hcount_b : pullCount action b n = m)
    (hraw : sumRewards action reward b n <=
      sumRewards action reward a n) :
    (m : Rat) * (muB - muA) <=
      (Finset.range n).sum (fun t : Nat =>
        (if action t = a then reward t - muA else 0) +
        (if action t = b then muB - reward t else 0)) := by
  classical
  rw [Finset.sum_add_distrib]
  rw [selectedSubMean_sum_eq_sumRewards_sub_pullCount_mul]
  rw [meanSubSelected_sum_eq_pullCount_mul_sub_sumRewards]
  rw [hcount_a, hcount_b]
  have hdiff :
      (0 : Rat) <=
        sumRewards action reward a n - sumRewards action reward b n :=
    sub_nonneg.mpr hraw
  calc
    (m : Rat) * (muB - muA)
        = 0 + (m : Rat) * (muB - muA) := by
          simp
    _ <= (sumRewards action reward a n -
            sumRewards action reward b n) +
          (m : Rat) * (muB - muA) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hdiff ((m : Rat) * (muB - muA))
    _ = (sumRewards action reward a n - (m : Rat) * muA) +
          ((m : Rat) * muB - sumRewards action reward b n) := by
          ring

/--
Concrete ETC event inclusion from the empirical-mean comparison event to the
centered pairwise reward-difference finite-sum event over the configured
exploration horizon.

This leaf instantiates the earlier abstract event-shape adapter with
`idx := Finset.range (spec.explorationPulls * K)` and the centered
non-best-minus-best reward-difference summands.  It still does not prove
independence, sub-Gaussianity, filtration, or final ETC regret.
-/
theorem empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Set.Subset
      {omega : Omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm (reward omega)
            model.bestArm}
      {omega : Omega |
        ETC.centeredPairwiseGapThreshold spec model a <=
          (Finset.range (spec.explorationPulls * K)).sum (fun t : Nat =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)} := by
  apply
    ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp
      (spec := spec)
      (model := model)
      (commitArm := commitArm)
      (reward := reward)
      (a := a)
      (hexplorationPulls_pos := hexplorationPulls_pos)
      (idx := Finset.range (spec.explorationPulls * K))
      (X := fun t omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      (eps := ETC.centeredPairwiseGapThreshold spec model a)
  intro omega hraw
  let term : Nat -> Rat := fun t : Nat =>
    (if ETC.actionWithCommit spec commitArm t = a then
      reward omega t - model.mean a else 0) +
    (if ETC.actionWithCommit spec commitArm t = model.bestArm then
      model.mean model.bestArm - reward omega t else 0)
  have hrat :
      (spec.explorationPulls : Rat) *
          (model.mean model.bestArm - model.mean a) <=
        (Finset.range (spec.explorationPulls * K)).sum term :=
    ETC.sumRewards_le_imp_centered_pairwise_sum_ge
      (action := ETC.actionWithCommit spec commitArm)
      (reward := reward omega)
      (a := a)
      (b := model.bestArm)
      (n := spec.explorationPulls * K)
      (m := spec.explorationPulls)
      (muA := model.mean a)
      (muB := model.mean model.bestArm)
      (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
        spec commitArm a)
      (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
        spec commitArm model.bestArm)
      hraw
  have hreal :
      ETC.centeredPairwiseGapThreshold spec model a <=
        (((Finset.range (spec.explorationPulls * K)).sum term : Rat) :
          Real) := by
    exact (Rat.cast_le (K := Real)).2 hrat
  have hcast :
      (((Finset.range (spec.explorationPulls * K)).sum term : Rat) :
          Real) =
        (Finset.range (spec.explorationPulls * K)).sum
          (fun t : Nat => (term t : Real)) := by
    exact
      map_sum (Rat.castHom Real) term
        (Finset.range (spec.explorationPulls * K))
  simpa [term, hcast, ETC.centeredPairwiseRewardDiff,
    ETC.centeredPairwiseGapThreshold] using hreal

end ETC
end BanditRLProof
