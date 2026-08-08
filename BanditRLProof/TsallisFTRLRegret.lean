import BanditRLProof.TsallisRegularizer
import Mathlib.Tactic.Ring

/-!
# Finite-horizon FTRL stability and Tsallis penalty decomposition

This module lifts the one-step explicit-minimizer API to a finite-horizon
regularized be-the-leader theorem and the standard FTRL stability/penalty
regret decomposition. It then specializes the regularizer to negative Tsallis
entropy and exposes the penalty as a difference of finite power sums.

The route is deterministic. It consumes explicit minimizer certificates and
does not prove minimizer existence, a Tsallis stability bound, unbiased loss
estimation, self-bounding conversion, or a final Tsallis-INF regret theorem.
-/

namespace BanditRLProof
namespace FTRL

universe u

/-- Coordinatewise cumulative loss before round `t`. -/
noncomputable def cumulativeLoss {Action : Type u}
    (loss : Nat -> Action -> Real) (t : Nat) : Action -> Real :=
  fun action => (Finset.range t).sum (fun s => loss s action)

@[simp] theorem cumulativeLoss_zero {Action : Type u}
    (loss : Nat -> Action -> Real) :
    cumulativeLoss loss 0 = 0 := by
  funext action
  simp [cumulativeLoss]

/-- Adding one round appends its loss vector to the cumulative loss. -/
theorem cumulativeLoss_succ {Action : Type u}
    (loss : Nat -> Action -> Real) (t : Nat) :
    cumulativeLoss loss (t + 1) =
      fun action => cumulativeLoss loss t action + loss t action := by
  funext action
  simp [cumulativeLoss, Finset.sum_range_succ]

/-- Finite-action linear loss is additive in its loss-vector argument. -/
theorem linearLoss_add_right {Action : Type u}
    (arms : Finset Action) (p x y : Action -> Real) :
    linearLoss arms p (fun action => x action + y action) =
      linearLoss arms p x + linearLoss arms p y := by
  simp [linearLoss, mul_add, Finset.sum_add_distrib]

/-- A linear loss against the cumulative vector is the sum of round losses. -/
theorem linearLoss_cumulativeLoss {Action : Type u}
    (arms : Finset Action) (p : Action -> Real)
    (loss : Nat -> Action -> Real) (T : Nat) :
    linearLoss arms p (cumulativeLoss loss T) =
      (Finset.range T).sum (fun t => linearLoss arms p (loss t)) := by
  simp only [linearLoss, cumulativeLoss, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The cumulative regularized objective has the expected successor update. -/
theorem regularizedObjective_cumulativeLoss_succ {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Nat -> Action -> Real) (p : Action -> Real) (t : Nat) :
    regularizedObjective arms eta regularizer (cumulativeLoss loss (t + 1)) p =
      regularizedObjective arms eta regularizer (cumulativeLoss loss t) p +
        eta * linearLoss arms p (loss t) := by
  rw [cumulativeLoss_succ, regularizedObjective, regularizedObjective,
    linearLoss_add_right]
  ring

/--
Scaled regularized be-the-leader inequality for cumulative-loss minimizers.

The point `p t` minimizes the objective built from losses before round `t`.
Consequently the shifted choices `p (t + 1)` can be compared to the terminal
cumulative objective while retaining the initial regularizer value.
-/
theorem eta_mul_sum_next_linearLoss_add_regularizer_zero_le_objective
    {Action : Type u}
    (feasible : (Action -> Real) -> Prop)
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Nat -> Action -> Real) (p : Nat -> Action -> Real)
    (T : Nat)
    (hp : forall t, t <= T ->
      IsRegularizedMinimizer feasible arms eta regularizer
        (cumulativeLoss loss t) (p t)) :
    eta * (Finset.range T).sum
        (fun t => linearLoss arms (p (t + 1)) (loss t)) +
      regularizer (p 0) <=
        regularizedObjective arms eta regularizer
          (cumulativeLoss loss T) (p T) := by
  induction T with
  | zero =>
      simp [regularizedObjective, cumulativeLoss, linearLoss]
  | succ T ih =>
      have hprefix : forall t, t <= T ->
          IsRegularizedMinimizer feasible arms eta regularizer
            (cumulativeLoss loss t) (p t) := by
        intro t ht
        exact hp t (ht.trans (Nat.le_succ T))
      have hih := ih hprefix
      have hpT := hp T (Nat.le_succ T)
      have hpNext := hp (T + 1) (by rfl)
      have hmin :
          regularizedObjective arms eta regularizer
              (cumulativeLoss loss T) (p T) <=
            regularizedObjective arms eta regularizer
              (cumulativeLoss loss T) (p (T + 1)) :=
        hpT.2 (p (T + 1)) hpNext.1
      calc
        eta * (Finset.range (T + 1)).sum
              (fun t => linearLoss arms (p (t + 1)) (loss t)) +
            regularizer (p 0) =
            (eta * (Finset.range T).sum
                (fun t => linearLoss arms (p (t + 1)) (loss t)) +
              regularizer (p 0)) +
                eta * linearLoss arms (p (T + 1)) (loss T) := by
          rw [Finset.sum_range_succ]
          ring
        _ <= regularizedObjective arms eta regularizer
              (cumulativeLoss loss T) (p (T + 1)) +
                eta * linearLoss arms (p (T + 1)) (loss T) :=
          by
            simpa [add_comm] using
              add_le_add_right (hih.trans hmin)
                (eta * linearLoss arms (p (T + 1)) (loss T))
        _ = regularizedObjective arms eta regularizer
              (cumulativeLoss loss (T + 1)) (p (T + 1)) :=
          (regularizedObjective_cumulativeLoss_succ
            arms eta regularizer loss (p (T + 1)) T).symm

/--
Regularized be-the-leader bound against any feasible comparator.
-/
theorem sum_next_linearLoss_sub_comparator_le_regularizer_penalty
    {Action : Type u}
    (feasible : (Action -> Real) -> Prop)
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Nat -> Action -> Real) (p : Nat -> Action -> Real)
    (q : Action -> Real) (T : Nat)
    (heta : 0 < eta)
    (hp : forall t, t <= T ->
      IsRegularizedMinimizer feasible arms eta regularizer
        (cumulativeLoss loss t) (p t))
    (hq : feasible q) :
    (Finset.range T).sum (fun t =>
        linearLoss arms (p (t + 1)) (loss t) -
          linearLoss arms q (loss t)) <=
      (regularizer q - regularizer (p 0)) / eta := by
  have hleader :=
    eta_mul_sum_next_linearLoss_add_regularizer_zero_le_objective
      feasible arms eta regularizer loss p T hp
  have hpT := hp T (by rfl)
  have hcompare :
      regularizedObjective arms eta regularizer
          (cumulativeLoss loss T) (p T) <=
        regularizedObjective arms eta regularizer
          (cumulativeLoss loss T) q :=
    hpT.2 q hq
  have htotal := hleader.trans hcompare
  rw [Finset.sum_sub_distrib, le_div_iff₀ heta]
  rw [regularizedObjective, linearLoss_cumulativeLoss] at htotal
  calc
    ((Finset.range T).sum
        (fun t => linearLoss arms (p (t + 1)) (loss t)) -
      (Finset.range T).sum
        (fun t => linearLoss arms q (loss t))) * eta =
        eta * (Finset.range T).sum
            (fun t => linearLoss arms (p (t + 1)) (loss t)) -
          eta * (Finset.range T).sum
            (fun t => linearLoss arms q (loss t)) := by ring
    _ <= regularizer q - regularizer (p 0) := by linarith

/--
Finite-horizon FTRL stability/penalty regret decomposition.

The first sum on the right is the stability term. The second term is the
regularizer penalty. No convexity or minimizer-existence theorem is hidden:
all cumulative minimizer certificates are explicit inputs.
-/
theorem cumulativeLinearLoss_sub_comparator_le_stability_add_penalty
    {Action : Type u}
    (feasible : (Action -> Real) -> Prop)
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Nat -> Action -> Real) (p : Nat -> Action -> Real)
    (q : Action -> Real) (T : Nat)
    (heta : 0 < eta)
    (hp : forall t, t <= T ->
      IsRegularizedMinimizer feasible arms eta regularizer
        (cumulativeLoss loss t) (p t))
    (hq : feasible q) :
    (Finset.range T).sum (fun t =>
        linearLoss arms (p t) (loss t) - linearLoss arms q (loss t)) <=
      (Finset.range T).sum (fun t =>
          linearLoss arms (p t) (loss t) -
            linearLoss arms (p (t + 1)) (loss t)) +
        (regularizer q - regularizer (p 0)) / eta := by
  have hleader :=
    sum_next_linearLoss_sub_comparator_le_regularizer_penalty
      feasible arms eta regularizer loss p q T heta hp hq
  calc
    (Finset.range T).sum (fun t =>
        linearLoss arms (p t) (loss t) - linearLoss arms q (loss t)) =
      (Finset.range T).sum (fun t =>
          linearLoss arms (p t) (loss t) -
            linearLoss arms (p (t + 1)) (loss t)) +
        (Finset.range T).sum (fun t =>
          linearLoss arms (p (t + 1)) (loss t) -
            linearLoss arms q (loss t)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ <= (Finset.range T).sum (fun t =>
          linearLoss arms (p t) (loss t) -
            linearLoss arms (p (t + 1)) (loss t)) +
        (regularizer q - regularizer (p 0)) / eta :=
      by
        simpa [add_comm] using
          add_le_add_right hleader
            ((Finset.range T).sum (fun t =>
              linearLoss arms (p t) (loss t) -
                linearLoss arms (p (t + 1)) (loss t)))

/-- Finite-simplex specialization of the FTRL decomposition. -/
theorem cumulativeLinearLoss_sub_comparator_le_stability_add_penalty_simplex
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Nat -> Action -> Real) (p : Nat -> Action -> Real)
    (q : Action -> Real) (T : Nat)
    (heta : 0 < eta)
    (hp : forall t, t <= T ->
      IsRegularizedMinimizer (finiteSimplex arms) arms eta regularizer
        (cumulativeLoss loss t) (p t))
    (hq : finiteSimplex arms q) :
    (Finset.range T).sum (fun t =>
        linearLoss arms (p t) (loss t) - linearLoss arms q (loss t)) <=
      (Finset.range T).sum (fun t =>
          linearLoss arms (p t) (loss t) -
            linearLoss arms (p (t + 1)) (loss t)) +
        (regularizer q - regularizer (p 0)) / eta := by
  exact cumulativeLinearLoss_sub_comparator_le_stability_add_penalty
    (finiteSimplex arms) arms eta regularizer loss p q T heta hp hq

end FTRL

namespace Tsallis

universe u

/-- Difference of negative Tsallis entropies as a power-sum difference. -/
theorem negEntropyRegularizer_sub_eq_powerSum_sub_div
    {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p q : Action -> Real)
    (halpha : Ne alpha 1) :
    negEntropyRegularizer arms alpha q -
        negEntropyRegularizer arms alpha p =
      (powerSum arms alpha p - powerSum arms alpha q) / (1 - alpha) := by
  have hdenom : Ne (1 - alpha) 0 := one_sub_exponent_ne_zero halpha
  simp only [negEntropyRegularizer, entropy]
  field_simp [hdenom]
  ring

/--
Finite-horizon Tsallis-FTRL stability/penalty regret decomposition.

The penalty is explicit in the finite power sums. The remaining algorithmic
obligation is to bound the stability sum for the chosen Tsallis exponent and
loss estimator, then supply minimizer existence and any stochastic contracts.
-/
theorem cumulativeLinearLoss_sub_comparator_le_stability_add_powerSumPenalty
    {Action : Type u}
    (arms : Finset Action) (alpha eta : Real)
    (loss : Nat -> Action -> Real) (p : Nat -> Action -> Real)
    (q : Action -> Real) (T : Nat)
    (halpha : Ne alpha 1) (heta : 0 < eta)
    (hp : forall t, t <= T ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms) arms eta
        (negEntropyRegularizer arms alpha)
        (FTRL.cumulativeLoss loss t) (p t))
    (hq : FTRL.finiteSimplex arms q) :
    (Finset.range T).sum (fun t =>
        FTRL.linearLoss arms (p t) (loss t) -
          FTRL.linearLoss arms q (loss t)) <=
      (Finset.range T).sum (fun t =>
          FTRL.linearLoss arms (p t) (loss t) -
            FTRL.linearLoss arms (p (t + 1)) (loss t)) +
        ((powerSum arms alpha (p 0) - powerSum arms alpha q) /
          (1 - alpha)) / eta := by
  have hregret :=
    FTRL.cumulativeLinearLoss_sub_comparator_le_stability_add_penalty_simplex
      arms eta (negEntropyRegularizer arms alpha) loss p q T heta hp hq
  rw [negEntropyRegularizer_sub_eq_powerSum_sub_div
    arms alpha (p 0) q halpha] at hregret
  exact hregret

end Tsallis
end BanditRLProof
