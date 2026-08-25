import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmRecurrence

/-!
# Two-arm stochastic-gradient-bandit initial recurrences

This module closes the source-round `t = 1` base case for the two exponential
recurrences used in Theorem 1 of
Baudry--Johnson--Vary--Pike-Burke--Rebeschini (NeurIPS 2025).  The generated
initial pair kernel samples from the untouched source parameter
`theta_1 = 0`, hence its action law is uniform on `Fin 2`; consuming that pair
produces `theta_2`.

Probability / Equation-(8) ledger:

* the random object is the initial `(selected action, reward)` pair drawn from
  `Thompson.measurableEnvironmentInitialPairKernel`;
* the action law is the exact two-arm softmax law at the zero vector, so each
  arm has probability `1 / 2`;
* `hreward` supplies the source support `|reward| <= 1` almost everywhere on
  each initial reward fiber, while `hmean` fixes its mean;
* no independence or filtration premise is needed at this base step;
* measurability and exponential integrability are discharged by
  `integral_measurableEnvironmentInitialPairKernel_exp_actionReward_le_sourceEqEight_of_mean`;
* `twoArmForwardEqEightRemainder_le` and
  `twoArmInverseEqEightRemainder_le` specialize the two action-dependent
  Equation-(8) coefficients at `p_1 = 1 / 2`.

The inverse bound is algebraically valid without assuming
`Delta > eta * sourceC eta`; that strict gap condition is needed only by later
summation/division consumers.  These declarations establish the two base
moments, not the tower-property iteration, expected failure-mass summation,
or the finite-horizon regret theorem.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe v

/-- Zero initialization gives the exact source probability `p_1 = 1 / 2` on
both arms. -/
@[simp]
theorem softmaxProbability_zeroInitialization_finTwo (selected : Fin 2) :
    softmaxProbability (fun _ : Fin 2 => 0) selected = (1 : Real) / 2 := by
  fin_cases selected <;>
    norm_num [softmaxProbability, softmaxDenominator, Fin.sum_univ_two]

/-- Source-round `t = 1` forward exponential base recurrence.  The left side
is `E[exp(2 * theta_{1,2})]`, because `theta_{1,1} = 0` and the initial pair
contributes exactly `eta * sourceIncrement`. -/
theorem integral_twoArmInitialPairKernel_exp_forwardIncrement_le
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment :
      Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (env : Env) (mean : Fin 2 -> Real)
    (hreward : forall selected,
      ∀ᵐ reward ∂environment.initialFeedback (env, selected),
        |reward| <= 1)
    (hmean : forall selected,
      integral (environment.initialFeedback (env, selected)) id =
        mean selected)
    (hgap : mean 0 - mean 1 = Delta) :
    integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        (fun pair : Fin 2 × Real =>
          Real.exp
            (2 * eta *
              sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
                pair.2 pair.1 0)) <=
      1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2 := by
  let prob : Fin 2 -> Real :=
    softmaxProbability (fun _ : Fin 2 => 0)
  let q : Fin 2 -> Real := twoArmForwardQ eta prob
  have hp_nonneg : 0 <= prob 0 := softmaxProbability_nonneg _ _
  have hp_le_one : prob 0 <= 1 := softmaxProbability_le_one _ _
  have hEqEight :
      integral
          (Thompson.measurableEnvironmentInitialPairKernel
            (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
          (fun pair : Fin 2 × Real => Real.exp (q pair.1 * pair.2)) <=
        1 + ∑ selected, prob selected *
          (q selected * mean selected +
            q selected ^ 2 / 2 * sourceC (|q selected| / 2)) := by
    simpa [prob] using
      integral_measurableEnvironmentInitialPairKernel_exp_actionReward_le_sourceEqEight_of_mean
        (fun _ : Fin 2 => 0) eta environment env q mean hreward hmean
  have hprobOne : prob 1 = 1 - prob 0 := by
    simpa [prob] using
      softmaxProbability_one_eq_one_sub_zero
        (fun _ : Fin 2 => (0 : Real))
  have hrem :
      (∑ selected, prob selected *
        (q selected * mean selected +
          q selected ^ 2 / 2 * sourceC (|q selected| / 2))) <=
        2 * prob 0 * (1 - prob 0) *
          (eta * Delta + eta ^ 2 * sourceC eta) := by
    simp only [Fin.sum_univ_two]
    rw [hprobOne]
    simpa [q, twoArmForwardQ] using
      twoArmForwardEqEightRemainder_le eta (prob 0)
        (mean 0) (mean 1) Delta heta hp_nonneg hp_le_one hgap
  have hbase :
      integral
          (Thompson.measurableEnvironmentInitialPairKernel
            (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
          (fun pair : Fin 2 × Real => Real.exp (q pair.1 * pair.2)) <=
        1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2 := by
    calc
      _ <= 1 + ∑ selected, prob selected *
          (q selected * mean selected +
            q selected ^ 2 / 2 * sourceC (|q selected| / 2)) := hEqEight
      _ <= 1 + 2 * prob 0 * (1 - prob 0) *
          (eta * Delta + eta ^ 2 * sourceC eta) :=
        add_le_add_right hrem 1
      _ = 1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2 := by
        rw [show prob 0 = (1 : Real) / 2 by
          exact softmaxProbability_zeroInitialization_finTwo 0]
        ring
  have hintegrand :
      (fun pair : Fin 2 × Real =>
          Real.exp
            (2 * eta *
              sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
                pair.2 pair.1 0)) =
        (fun pair : Fin 2 × Real =>
          Real.exp (q pair.1 * pair.2)) := by
    funext pair
    apply congrArg Real.exp
    rw [twoArmForwardQ_mul_reward_eq_sourceIncrement]
    congr 2
    funext selected
    exact (softmaxProbability_zeroInitialization_finTwo selected).symm
  rw [hintegrand]
  exact hbase

/-- Source-round `t = 1` inverse exponential base recurrence.  This is the
initial value of the inverse-odds potential used to telescope the expected
squared failure mass. -/
theorem integral_twoArmInitialPairKernel_exp_inverseIncrement_le
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment :
      Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (env : Env) (mean : Fin 2 -> Real)
    (hreward : forall selected,
      ∀ᵐ reward ∂environment.initialFeedback (env, selected),
        |reward| <= 1)
    (hmean : forall selected,
      integral (environment.initialFeedback (env, selected)) id =
        mean selected)
    (hgap : mean 0 - mean 1 = Delta) :
    integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        (fun pair : Fin 2 × Real =>
          Real.exp
            (-2 * eta *
              sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
                pair.2 pair.1 0)) <=
      1 - eta / 2 * (Delta - eta * sourceC eta) := by
  let prob : Fin 2 -> Real :=
    softmaxProbability (fun _ : Fin 2 => 0)
  let q : Fin 2 -> Real := twoArmInverseQ eta prob
  have hp_nonneg : 0 <= prob 0 := softmaxProbability_nonneg _ _
  have hp_le_one : prob 0 <= 1 := softmaxProbability_le_one _ _
  have hEqEight :
      integral
          (Thompson.measurableEnvironmentInitialPairKernel
            (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
          (fun pair : Fin 2 × Real => Real.exp (q pair.1 * pair.2)) <=
        1 + ∑ selected, prob selected *
          (q selected * mean selected +
            q selected ^ 2 / 2 * sourceC (|q selected| / 2)) := by
    simpa [prob] using
      integral_measurableEnvironmentInitialPairKernel_exp_actionReward_le_sourceEqEight_of_mean
        (fun _ : Fin 2 => 0) eta environment env q mean hreward hmean
  have hprobOne : prob 1 = 1 - prob 0 := by
    simpa [prob] using
      softmaxProbability_one_eq_one_sub_zero
        (fun _ : Fin 2 => (0 : Real))
  have hrem :
      (∑ selected, prob selected *
        (q selected * mean selected +
          q selected ^ 2 / 2 * sourceC (|q selected| / 2))) <=
        -2 * eta * prob 0 * (1 - prob 0) *
          (Delta - eta * sourceC eta) := by
    simp only [Fin.sum_univ_two]
    rw [hprobOne]
    simpa [q, twoArmInverseQ, twoArmForwardQ] using
      twoArmInverseEqEightRemainder_le eta (prob 0)
        (mean 0) (mean 1) Delta heta hp_nonneg hp_le_one hgap
  have hbase :
      integral
          (Thompson.measurableEnvironmentInitialPairKernel
            (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
          (fun pair : Fin 2 × Real => Real.exp (q pair.1 * pair.2)) <=
        1 - eta / 2 * (Delta - eta * sourceC eta) := by
    calc
      _ <= 1 + ∑ selected, prob selected *
          (q selected * mean selected +
            q selected ^ 2 / 2 * sourceC (|q selected| / 2)) := hEqEight
      _ <= 1 + -2 * eta * prob 0 * (1 - prob 0) *
          (Delta - eta * sourceC eta) :=
        add_le_add_right hrem 1
      _ = 1 - eta / 2 * (Delta - eta * sourceC eta) := by
        rw [show prob 0 = (1 : Real) / 2 by
          exact softmaxProbability_zeroInitialization_finTwo 0]
        ring
  have hintegrand :
      (fun pair : Fin 2 × Real =>
          Real.exp
            (-2 * eta *
              sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
                pair.2 pair.1 0)) =
        (fun pair : Fin 2 × Real =>
          Real.exp (q pair.1 * pair.2)) := by
    funext pair
    apply congrArg Real.exp
    rw [twoArmInverseQ_mul_reward_eq_sourceIncrement]
    congr 2
    funext selected
    exact (softmaxProbability_zeroInitialization_finTwo selected).symm
  rw [hintegrand]
  exact hbase

end

end StochasticGradientBandit
end BanditRLProof
