import BanditRLProof.Algorithms.StochasticGradientBanditTrajectoryAudit

/-!
# Two-arm stochastic-gradient-bandit rate identities

This module starts the source-facing rate layer for Theorem 1 of
Baudry--Johnson--Vary--Pike-Burke--Rebeschini (NeurIPS 2025).  It proves that
Algorithm 1 preserves the zero sum of its parameter vector on every generated
finite history, then specializes the two-arm softmax law to the exact odds
identities used as Equation (11) in the source proof.

These pathwise identities are inputs to the exponential-moment and
telescoping arguments.  They do not by themselves prove Equation (8), the
failure-mass estimate, or Theorem 1's regret bound.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open scoped BigOperators

noncomputable section

universe u

/-- Algorithm 1 preserves the sum of an arbitrary initial parameter vector
on every inclusive finite action/reward history. -/
theorem historyParameter_sum_eq_initial
    {Action : Type u} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (initialTheta : Action -> Real) (eta : Real) :
    forall n (history : History.FinitePairHistory Action Real n),
      (∑ coordinate, historyParameter initialTheta eta n history coordinate) =
        ∑ coordinate, initialTheta coordinate := by
  classical
  intro n
  induction n with
  | zero =>
      intro history
      rw [show (∑ coordinate,
          historyParameter initialTheta eta 0 history coordinate) =
          ∑ coordinate,
            (initialTheta coordinate + eta *
              sourceIncrement (softmaxProbability initialTheta)
                (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2
                (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 coordinate) by
        apply Finset.sum_congr rfl
        intro coordinate _
        rw [historyParameter_zero]]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_sourceIncrement]
      · ring
      · exact softmaxProbability_sum initialTheta
  | succ n ih =>
      intro history
      rw [show (∑ coordinate,
          historyParameter initialTheta eta (n + 1) history coordinate) =
          ∑ coordinate,
            (historyParameter initialTheta eta n
                (Exp3.previousPairHistory history) coordinate +
              eta * sourceIncrement
                (softmaxProbability
                  (historyParameter initialTheta eta n
                    (Exp3.previousPairHistory history)))
                (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2
                (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 coordinate) by
        apply Finset.sum_congr rfl
        intro coordinate _
        rw [historyParameter_succ]]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_sourceIncrement]
      · simpa using ih (Exp3.previousPairHistory history)
      · exact softmaxProbability_sum
          (historyParameter initialTheta eta n
            (Exp3.previousPairHistory history))

/-- The source initialization `theta = 0` therefore stays zero-sum pathwise. -/
theorem historyParameter_zeroInitialization_sum
    {Action : Type u} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (eta : Real) (n : Nat)
    (history : History.FinitePairHistory Action Real n) :
    ∑ coordinate,
      historyParameter (fun _ : Action => 0) eta n history coordinate = 0 := by
  rw [historyParameter_sum_eq_initial]
  simp

/-- Source-time parameter adapter for one infinite two-arm action/reward trace.
Lean time `0` is the pre-action source parameter `theta_{.,1} = 0`; Lean time
`n + 1` is the parameter after consuming trace pair `n`, namely source
`theta_{.,n+2}`. -/
noncomputable def twoArmParameterAt (eta : Real)
    (trace : Nat -> Fin 2 × Real) : Nat -> Fin 2 -> Real
  | 0 => fun _ => 0
  | n + 1 =>
      historyParameter (fun _ : Fin 2 => 0) eta n
        (Preorder.frestrictLe n trace)

/-- The two-arm softmax law generated from the source-time parameter adapter. -/
def twoArmProbabilityAt (eta : Real) (trace : Nat -> Fin 2 × Real)
    (time : Nat) : Fin 2 -> Real :=
  softmaxProbability (twoArmParameterAt eta trace time)

@[simp]
theorem twoArmParameterAt_zero (eta : Real)
    (trace : Nat -> Fin 2 × Real) (arm : Fin 2) :
    twoArmParameterAt eta trace 0 arm = 0 := rfl

@[simp]
theorem twoArmParameterAt_succ (eta : Real)
    (trace : Nat -> Fin 2 × Real) (n : Nat) (arm : Fin 2) :
    twoArmParameterAt eta trace (n + 1) arm =
      historyParameter (fun _ : Fin 2 => 0) eta n
        (Preorder.frestrictLe n trace) arm := rfl

/-- The source-time two-arm parameter stays zero-sum on every path. -/
theorem twoArmParameterAt_sum_eq_zero (eta : Real)
    (trace : Nat -> Fin 2 × Real) (time : Nat) :
    ∑ arm, twoArmParameterAt eta trace time arm = 0 := by
  cases time with
  | zero => simp
  | succ n =>
      simpa using historyParameter_zeroInitialization_sum eta n
        (Preorder.frestrictLe n trace)

/-- Hence source arm `2` has the negative parameter of source arm `1`. -/
theorem twoArmParameterAt_one_eq_neg_zero (eta : Real)
    (trace : Nat -> Fin 2 × Real) (time : Nat) :
    twoArmParameterAt eta trace time 1 =
      -twoArmParameterAt eta trace time 0 := by
  have hsum := twoArmParameterAt_sum_eq_zero eta trace time
  simp only [Fin.sum_univ_two] at hsum
  linarith

/-- Algorithm 1's zero initialization gives the uniform two-arm law before
the first action. -/
@[simp]
theorem twoArmProbabilityAt_zero (eta : Real)
    (trace : Nat -> Fin 2 × Real) (arm : Fin 2) :
    twoArmProbabilityAt eta trace 0 arm = 1 / 2 := by
  fin_cases arm <;>
    norm_num [twoArmProbabilityAt, softmaxProbability,
      softmaxDenominator, Fin.sum_univ_two]

/-- On two arms, normalization identifies the second softmax probability with
the failure probability of the first arm. -/
theorem softmaxProbability_one_eq_one_sub_zero (theta : Fin 2 -> Real) :
    softmaxProbability theta 1 = 1 - softmaxProbability theta 0 := by
  have hsum := softmaxProbability_sum theta
  simp only [Fin.sum_univ_two] at hsum
  linarith

/-- The exact two-arm softmax odds before using the zero-sum invariant. -/
theorem softmaxProbability_zero_div_one (theta : Fin 2 -> Real) :
    softmaxProbability theta 0 / softmaxProbability theta 1 =
      Real.exp (theta 0 - theta 1) := by
  have hden : softmaxDenominator theta ≠ 0 :=
    ne_of_gt (softmaxDenominator_pos theta)
  have hexpOne : Real.exp (theta 1) ≠ 0 := ne_of_gt (Real.exp_pos _)
  calc
    softmaxProbability theta 0 / softmaxProbability theta 1 =
        Real.exp (theta 0) / Real.exp (theta 1) := by
      simp only [softmaxProbability]
      field_simp
    _ = Real.exp (theta 0 - theta 1) := by rw [Real.exp_sub]

/-- A zero-sum two-arm parameter has opposite coordinates. -/
theorem finTwo_one_eq_neg_zero_of_sum_eq_zero
    (theta : Fin 2 -> Real) (hsum : ∑ coordinate, theta coordinate = 0) :
    theta 1 = -theta 0 := by
  simp only [Fin.sum_univ_two] at hsum
  linarith

/-- The printed division form of Equation (11). Lean arm `0` is source arm
`1`, and strict softmax positivity makes the denominator nonzero. -/
theorem softmaxProbability_zero_div_one_sub_zero_eq_exp_two_mul
    (theta : Fin 2 -> Real) (hsum : ∑ coordinate, theta coordinate = 0) :
    softmaxProbability theta 0 / (1 - softmaxProbability theta 0) =
      Real.exp (2 * theta 0) := by
  rw [← softmaxProbability_one_eq_one_sub_zero]
  rw [softmaxProbability_zero_div_one,
    finTwo_one_eq_neg_zero_of_sum_eq_zero theta hsum, sub_neg_eq_add,
    ← two_mul]

/-- The multiplication form of Equation (11) used in the source Theorem 1
proof: `exp(2 theta_1) (1 - p_1) = p_1`. Lean arm `0` is source arm `1`. -/
theorem exp_two_mul_zero_mul_one_sub_softmaxProbability_zero
    (theta : Fin 2 -> Real) (hsum : ∑ coordinate, theta coordinate = 0) :
    Real.exp (2 * theta 0) * (1 - softmaxProbability theta 0) =
      softmaxProbability theta 0 := by
  rw [← softmaxProbability_one_eq_one_sub_zero]
  have hprobOne : softmaxProbability theta 1 ≠ 0 :=
    ne_of_gt (softmaxProbability_pos theta 1)
  have hodds := softmaxProbability_zero_div_one theta
  rw [finTwo_one_eq_neg_zero_of_sum_eq_zero theta hsum] at hodds
  rw [sub_neg_eq_add, ← two_mul] at hodds
  exact ((div_eq_iff hprobOne).mp hodds).symm

/-- The inverse-odds form used for the failure-mass telescoping potential in
the second half of the source Theorem 1 proof. -/
theorem exp_neg_two_mul_zero_mul_softmaxProbability_zero
    (theta : Fin 2 -> Real) (hsum : ∑ coordinate, theta coordinate = 0) :
    Real.exp (-2 * theta 0) * softmaxProbability theta 0 =
      1 - softmaxProbability theta 0 := by
  rw [← softmaxProbability_one_eq_one_sub_zero]
  have heq :=
    exp_two_mul_zero_mul_one_sub_softmaxProbability_zero theta hsum
  rw [← softmaxProbability_one_eq_one_sub_zero] at heq
  rw [← heq, ← mul_assoc, ← Real.exp_add]
  ring_nf
  simp

/-- Source-time Equation (11) on every infinite action/reward trace. -/
theorem twoArmProbabilityAt_exp_two_mul_failure_eq_success
    (eta : Real) (trace : Nat -> Fin 2 × Real) (time : Nat) :
    Real.exp (2 * twoArmParameterAt eta trace time 0) *
        (1 - twoArmProbabilityAt eta trace time 0) =
      twoArmProbabilityAt eta trace time 0 := by
  exact exp_two_mul_zero_mul_one_sub_softmaxProbability_zero
    (twoArmParameterAt eta trace time)
    (twoArmParameterAt_sum_eq_zero eta trace time)

/-- The printed Equation (11) on the explicitly fenced source-time trace. -/
theorem twoArmProbabilityAt_zero_div_failure_eq_exp_two_mul
    (eta : Real) (trace : Nat -> Fin 2 × Real) (time : Nat) :
    twoArmProbabilityAt eta trace time 0 /
        (1 - twoArmProbabilityAt eta trace time 0) =
      Real.exp (2 * twoArmParameterAt eta trace time 0) := by
  exact softmaxProbability_zero_div_one_sub_zero_eq_exp_two_mul
    (twoArmParameterAt eta trace time)
    (twoArmParameterAt_sum_eq_zero eta trace time)

/-- Finite-history multiplication form of Equation (11) under Algorithm 1's
source initialization. -/
theorem historyParameter_exp_two_mul_zero_eq_odds
    (eta : Real) (n : Nat)
    (history : History.FinitePairHistory (Fin 2) Real n) :
    Real.exp
        (2 * historyParameter (fun _ : Fin 2 => 0) eta n history 0) *
        (1 - softmaxProbability
          (historyParameter (fun _ : Fin 2 => 0) eta n history) 0) =
      softmaxProbability
        (historyParameter (fun _ : Fin 2 => 0) eta n history) 0 := by
  apply exp_two_mul_zero_mul_one_sub_softmaxProbability_zero
  exact historyParameter_zeroInitialization_sum eta n history

end

end StochasticGradientBandit
end BanditRLProof
