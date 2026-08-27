import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmTheoremOne

/-!
# Two-arm stochastic-gradient bandit: Corollary 1 companion

This module closes the bounded Corollary-1 companion from Baudry, Johnson,
Vary, Pike-Burke, and Rebeschini, *Does Stochastic Gradient really succeed
for Bandits?* (NeurIPS 2025).  It remains on the generated Algorithm-1
trajectory and uses a separate fixed learning rate
`sqrt (log T / T)` for each source horizon `T`.

The proof has the source's two branches.  When
`2 * eta * C_eta <= Delta`, the already compiled Theorem 1 applies and its
constant term is at most `1 / eta`.  Otherwise the pathwise regret of the
actually sampled actions is at most `Delta * T`.  The final theorem combines
the branches into an explicit absolute-constant multiple of
`sqrt (T * log T)`.

This is a direct consumer of Theorem 1.  It is not evidence for the paper's
polynomial-regret Theorem 2, a time-varying learning-rate policy, or a
general-`K` result.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe v

/-- Every realized two-arm gap is at most `Delta` when `Delta` is
nonnegative. -/
theorem twoArmActionGap_le_gap (Delta : Real) (hDelta : 0 <= Delta)
    (action : Fin 2) :
    twoArmActionGap Delta action <= Delta := by
  by_cases haction : action = 0
  · simp [twoArmActionGap, haction, hDelta]
  · simp [twoArmActionGap, haction]

/-- Pathwise trivial regret bound for the actions actually sampled by the
generated process. -/
theorem twoArmSampledPseudoRegret_le_gap_mul_horizon
    {Env : Type v} (Delta : Real) (hDelta : 0 <= Delta) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmSampledPseudoRegret Delta horizon sample <=
      Delta * (horizon : Real) := by
  rw [twoArmSampledPseudoRegret]
  calc
    (Finset.range horizon).sum (fun t =>
        twoArmActionGap Delta (sample.2 t).1) <=
        (Finset.range horizon).sum (fun _ => Delta) := by
      apply Finset.sum_le_sum
      intro t _ht
      exact twoArmActionGap_le_gap Delta hDelta (sample.2 t).1
    _ = Delta * (horizon : Real) := by simp [mul_comm]

theorem measurable_twoArmSampledPseudoRegret
    {Env : Type v} [MeasurableSpace Env] (Delta : Real) (horizon : Nat) :
    Measurable (twoArmSampledPseudoRegret (Env := Env) Delta horizon) := by
  unfold twoArmSampledPseudoRegret
  fun_prop

theorem integrable_twoArmSampledPseudoRegret
    {Env : Type v} [MeasurableSpace Env]
    (mu : Measure (Env × ((k : Nat) -> Fin 2 × Real))) [IsFiniteMeasure mu]
    (Delta : Real) (horizon : Nat) :
    Integrable (twoArmSampledPseudoRegret (Env := Env) Delta horizon) mu := by
  apply Integrable.of_bound
    (measurable_twoArmSampledPseudoRegret Delta horizon).aestronglyMeasurable
    ((horizon : Real) * |Delta|)
  filter_upwards [] with sample
  rw [Real.norm_eq_abs, twoArmSampledPseudoRegret]
  calc
    |(Finset.range horizon).sum (fun t =>
        twoArmActionGap Delta (sample.2 t).1)| <=
        (Finset.range horizon).sum (fun t =>
          |twoArmActionGap Delta (sample.2 t).1|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.range horizon).sum (fun _ => |Delta|) := by
      apply Finset.sum_le_sum
      intro t _ht
      by_cases haction : (sample.2 t).1 = 0
      · simp [twoArmActionGap, haction]
      · simp [twoArmActionGap, haction]
    _ = (horizon : Real) * |Delta| := by simp

/-- Integral form of the pathwise `Delta * T` bound.  The measure is the
actual generated trajectory measure in the Corollary-1 consumer below. -/
theorem integral_twoArmSampledPseudoRegret_le_gap_mul_horizon
    {Env : Type v} [MeasurableSpace Env]
    (mu : Measure (Env × ((k : Nat) -> Fin 2 × Real)))
    [IsProbabilityMeasure mu]
    (Delta : Real) (hDelta : 0 <= Delta) (horizon : Nat) :
    integral mu (twoArmSampledPseudoRegret (Env := Env) Delta horizon) <=
      Delta * (horizon : Real) := by
  calc
    integral mu (twoArmSampledPseudoRegret (Env := Env) Delta horizon) <=
        integral mu (fun _ => Delta * (horizon : Real)) := by
      exact integral_mono
        (integrable_twoArmSampledPseudoRegret mu Delta horizon)
        (integrable_const (Delta * (horizon : Real)))
        (fun sample =>
          twoArmSampledPseudoRegret_le_gap_mul_horizon
            Delta hDelta horizon sample)
    _ = Delta * (horizon : Real) := by simp

/-- The horizon-indexed fixed learning rate used in Corollary 1. -/
noncomputable def corollaryOneEta (horizon : Nat) : Real :=
  Real.sqrt (Real.log (horizon : Real) / (horizon : Real))

/-- The source small-learning-rate branch implies the strict Theorem-1
margin. -/
theorem sourceTheoremOne_margin_of_two_mul_eta_sourceC_le
    (eta Delta : Real) (heta : 0 < eta) (hDelta : 0 < Delta)
    (hsmall : 2 * eta * sourceC eta <= Delta) :
    eta * sourceC eta < Delta := by
  have hC : 0 <= sourceC eta := sourceC_nonneg eta heta.le
  nlinarith

/-- Under the Corollary-1 small-learning-rate branch, the constant term in
Theorem 1 is at most `1 / eta`. -/
theorem sourceTheoremOne_constant_le_inv_eta
    (eta Delta : Real) (heta : 0 < eta) (hDelta : 0 < Delta)
    (hsmall : 2 * eta * sourceC eta <= Delta) :
    Delta / (2 * eta * (Delta - eta * sourceC eta)) <= 1 / eta := by
  have hmargin := sourceTheoremOne_margin_of_two_mul_eta_sourceC_le
    eta Delta heta hDelta hsmall
  have hsub : 0 < Delta - eta * sourceC eta := sub_pos.mpr hmargin
  have hden : 0 < 2 * eta * (Delta - eta * sourceC eta) :=
    mul_pos (mul_pos (by norm_num) heta) hsub
  rw [div_le_iff₀ hden]
  have heta0 : eta ≠ 0 := ne_of_gt heta
  field_simp [heta0]
  nlinarith

theorem corollaryOneEta_pos (horizon : Nat) (hhorizon : 2 <= horizon) :
    0 < corollaryOneEta horizon := by
  have hx : (1 : Real) < (horizon : Real) := by exact_mod_cast hhorizon
  have hx0 : (0 : Real) < (horizon : Real) := zero_lt_one.trans hx
  unfold corollaryOneEta
  exact Real.sqrt_pos.2 (div_pos (Real.log_pos hx) hx0)

theorem corollaryOneEta_sq (horizon : Nat) (hhorizon : 2 <= horizon) :
    corollaryOneEta horizon ^ 2 =
      Real.log (horizon : Real) / (horizon : Real) := by
  have hhorizon_one : 1 <= horizon := by omega
  have hx1 : (1 : Real) <= (horizon : Real) := by
    exact_mod_cast hhorizon_one
  have hx0 : (0 : Real) <= (horizon : Real) := by positivity
  unfold corollaryOneEta
  exact Real.sq_sqrt (div_nonneg (Real.log_nonneg hx1) hx0)

/-- The Corollary-1 learning rate stays in the range where
`C_eta <= exp 2` is available. -/
theorem corollaryOneEta_le_one (horizon : Nat) (hhorizon : 2 <= horizon) :
    corollaryOneEta horizon <= 1 := by
  have hx : (0 : Real) < (horizon : Real) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  have hquotient :
      Real.log (horizon : Real) / (horizon : Real) <= 1 := by
    rw [div_le_one hx]
    linarith
  have heta0 : 0 <= corollaryOneEta horizon := Real.sqrt_nonneg _
  have hetasq := corollaryOneEta_sq horizon hhorizon
  nlinarith

/-- The square-root rate appearing in the explicit Corollary-1 endpoint. -/
noncomputable def corollaryOneRate (horizon : Nat) : Real :=
  Real.sqrt ((horizon : Real) * Real.log (horizon : Real))

theorem corollaryOneRate_nonneg (horizon : Nat) :
    0 <= corollaryOneRate horizon := Real.sqrt_nonneg _

/-- The horizon-indexed learning rate times the horizon is exactly the
square-root rate. -/
theorem corollaryOneEta_mul_horizon_eq_rate
    (horizon : Nat) (hhorizon : 2 <= horizon) :
    corollaryOneEta horizon * (horizon : Real) =
      corollaryOneRate horizon := by
  have hx : (0 : Real) < (horizon : Real) := by positivity
  have hlog0 : 0 <= Real.log (horizon : Real) := by
    have hhorizon_one : 1 <= horizon := by omega
    exact Real.log_nonneg (by exact_mod_cast hhorizon_one)
  have hetasq := corollaryOneEta_sq horizon hhorizon
  have hratesq : corollaryOneRate horizon ^ 2 =
      (horizon : Real) * Real.log (horizon : Real) := by
    unfold corollaryOneRate
    exact Real.sq_sqrt (mul_nonneg hx.le hlog0)
  have hleft0 : 0 <= corollaryOneEta horizon * (horizon : Real) :=
    mul_nonneg (Real.sqrt_nonneg _) hx.le
  have hright0 := corollaryOneRate_nonneg horizon
  have hsq :
      (corollaryOneEta horizon * (horizon : Real)) ^ 2 =
        corollaryOneRate horizon ^ 2 := by
    rw [mul_pow, hetasq, hratesq]
    field_simp
  nlinarith

theorem corollaryOneEta_mul_rate_eq_log
    (horizon : Nat) (hhorizon : 2 <= horizon) :
    corollaryOneEta horizon * corollaryOneRate horizon =
      Real.log (horizon : Real) := by
  have hx0 : (horizon : Real) ≠ 0 := by positivity
  rw [← corollaryOneEta_mul_horizon_eq_rate horizon hhorizon]
  calc
    corollaryOneEta horizon *
          (corollaryOneEta horizon * (horizon : Real)) =
        corollaryOneEta horizon ^ 2 * (horizon : Real) := by ring
    _ = Real.log (horizon : Real) := by
      rw [corollaryOneEta_sq horizon hhorizon]
      field_simp

/-- The inverse learning-rate term is an absolute-constant multiple of the
square-root rate.  We keep the exact constant `1 / log 2`, avoiding a hidden
asymptotic threshold. -/
theorem corollaryOne_inv_eta_le_inv_log_two_mul_rate
    (horizon : Nat) (hhorizon : 2 <= horizon) :
    1 / corollaryOneEta horizon <=
      (1 / Real.log 2) * corollaryOneRate horizon := by
  have heta := corollaryOneEta_pos horizon hhorizon
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwoCast : (2 : Real) <= (horizon : Real) := by
    exact_mod_cast hhorizon
  have hlogMono : Real.log 2 <= Real.log (horizon : Real) :=
    Real.log_le_log (by norm_num) htwoCast
  rw [div_le_iff₀ heta]
  calc
    1 <= Real.log (horizon : Real) / Real.log 2 := by
      exact (le_div_iff₀ hlogTwo).2 (by simpa using hlogMono)
    _ = (1 / Real.log 2) * corollaryOneRate horizon *
          corollaryOneEta horizon := by
      rw [← corollaryOneEta_mul_rate_eq_log horizon hhorizon]
      field_simp

/-- For `T >= 2`, `0 < Delta < 1`, and the Corollary-1 learning rate, the
argument of the Theorem-1 logarithm is at most `T^4`. -/
theorem corollaryOne_log_argument_le_horizon_pow_four
    (horizon : Nat) (hhorizon : 2 <= horizon)
    (Delta : Real) (hDelta : 0 < Delta) (hDelta_lt_one : Delta < 1) :
    1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real) <=
      (horizon : Real) ^ 4 := by
  let x : Real := (horizon : Real)
  let eta := corollaryOneEta horizon
  have hx2 : (2 : Real) <= x := by
    dsimp [x]
    exact_mod_cast hhorizon
  have hx0 : 0 <= x := le_trans (by norm_num) hx2
  have heta0 : 0 <= eta := by
    dsimp [eta]
    exact Real.sqrt_nonneg _
  have heta_le : eta <= 1 := by
    dsimp [eta]
    exact corollaryOneEta_le_one horizon hhorizon
  have hetaDelta_le : eta * Delta <= 1 := by
    have hDelta_le : Delta <= 1 := hDelta_lt_one.le
    nlinarith [mul_nonneg (sub_nonneg.mpr heta_le)
      (sub_nonneg.mpr hDelta_le)]
  have hscaled : eta * Delta * x <= x := by
    simpa using mul_le_mul_of_nonneg_right hetaDelta_le hx0
  have hxsq_ge_two_mul : 2 * x <= x ^ 2 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx2)]
  have hxsq_ge_four : 4 <= x ^ 2 := by nlinarith
  have hfour_sq_le_fourth : 4 * x ^ 2 <= x ^ 4 := by
    calc
      4 * x ^ 2 <= x ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hxsq_ge_four (sq_nonneg x)
      _ = x ^ 4 := by ring
  have hlinear_le_fourth : 1 + 4 * x <= x ^ 4 := by
    calc
      1 + 4 * x <= 8 * x := by nlinarith
      _ = 4 * (2 * x) := by ring
      _ <= 4 * x ^ 2 := by nlinarith
      _ <= x ^ 4 := hfour_sq_le_fourth
  dsimp [x, eta] at hscaled hlinear_le_fourth ⊢
  linarith

/-- The logarithmic term in the Theorem-1 branch is at most twice the
square-root rate. -/
theorem corollaryOne_log_term_le_two_mul_rate
    (horizon : Nat) (hhorizon : 2 <= horizon)
    (Delta : Real) (hDelta : 0 < Delta) (hDelta_lt_one : Delta < 1) :
    Real.log
        (1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real)) /
        (2 * corollaryOneEta horizon) <=
      2 * corollaryOneRate horizon := by
  have heta := corollaryOneEta_pos horizon hhorizon
  have hargPos : 0 <
      1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real) := by
    positivity
  have harg := corollaryOne_log_argument_le_horizon_pow_four
    horizon hhorizon Delta hDelta hDelta_lt_one
  have hlog :
      Real.log
          (1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real)) <=
        4 * Real.log (horizon : Real) := by
    calc
      Real.log
          (1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real)) <=
          Real.log ((horizon : Real) ^ 4) :=
        Real.log_le_log hargPos harg
      _ = 4 * Real.log (horizon : Real) := by
        rw [Real.log_pow]
        norm_num
  rw [div_le_iff₀ (mul_pos (by norm_num) heta)]
  rw [← corollaryOneEta_mul_rate_eq_log horizon hhorizon] at hlog
  nlinarith

/-- On the complementary branch, the pathwise `Delta * T` bound is still a
square-root rate because failure of `2 * eta * C_eta <= Delta` forces the gap
below the learning-rate scale. -/
theorem corollaryOne_gap_mul_horizon_le_exp_constant_mul_rate
    (horizon : Nat) (hhorizon : 2 <= horizon) (Delta : Real)
    (hlarge : ¬ 2 * corollaryOneEta horizon *
      sourceC (corollaryOneEta horizon) <= Delta) :
    Delta * (horizon : Real) <=
      (2 * Real.exp 2) * corollaryOneRate horizon := by
  let eta := corollaryOneEta horizon
  have hx0 : 0 <= (horizon : Real) := by positivity
  have heta0 : 0 <= eta := by
    dsimp [eta]
    exact Real.sqrt_nonneg _
  have heta_le : eta <= 1 := by
    dsimp [eta]
    exact corollaryOneEta_le_one horizon hhorizon
  have hC : sourceC eta <= Real.exp (2 * eta) :=
    sourceC_le_exp_two_mul eta heta0
  have hexp : Real.exp (2 * eta) <= Real.exp 2 := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hCtwo : sourceC eta <= Real.exp 2 := hC.trans hexp
  have hgap : Delta <= 2 * eta * sourceC eta := by
    exact (lt_of_not_ge (by simpa [eta] using hlarge)).le
  have hcoef : 2 * eta * sourceC eta <= 2 * eta * Real.exp 2 := by
    exact mul_le_mul_of_nonneg_left hCtwo (by positivity)
  calc
    Delta * (horizon : Real) <=
        (2 * eta * sourceC eta) * (horizon : Real) :=
      mul_le_mul_of_nonneg_right hgap hx0
    _ <= (2 * eta * Real.exp 2) * (horizon : Real) :=
      mul_le_mul_of_nonneg_right hcoef hx0
    _ = (2 * Real.exp 2) * corollaryOneRate horizon := by
      rw [← corollaryOneEta_mul_horizon_eq_rate horizon hhorizon]
      dsimp [eta]
      ring

/-- An explicit horizon-independent constant for the finite Corollary-1
endpoint. -/
noncomputable def corollaryOneAbsoluteConstant : Real :=
  2 + 1 / Real.log 2 + 2 * Real.exp 2

theorem corollaryOne_piecewise_bound
    (horizon : Nat) (hhorizon : 2 <= horizon)
    (Delta : Real) (hDelta : 0 < Delta) (hDelta_lt_one : Delta < 1) :
    (if 2 * corollaryOneEta horizon * sourceC (corollaryOneEta horizon) <=
        Delta then
      Real.log
          (1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real)) /
          (2 * corollaryOneEta horizon) +
        1 / corollaryOneEta horizon
    else
      Delta * (horizon : Real)) <=
      corollaryOneAbsoluteConstant * corollaryOneRate horizon := by
  have hrate0 := corollaryOneRate_nonneg horizon
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hsmall :
      2 * corollaryOneEta horizon * sourceC (corollaryOneEta horizon) <=
        Delta
  · rw [if_pos hsmall]
    have hlog := corollaryOne_log_term_le_two_mul_rate
      horizon hhorizon Delta hDelta hDelta_lt_one
    have hinv := corollaryOne_inv_eta_le_inv_log_two_mul_rate
      horizon hhorizon
    have hbase :
        Real.log
            (1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real)) /
              (2 * corollaryOneEta horizon) +
            1 / corollaryOneEta horizon <=
          (2 + 1 / Real.log 2) * corollaryOneRate horizon := by
      calc
        Real.log
            (1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real)) /
              (2 * corollaryOneEta horizon) +
            1 / corollaryOneEta horizon <=
            2 * corollaryOneRate horizon +
              (1 / Real.log 2) * corollaryOneRate horizon :=
          add_le_add hlog hinv
        _ = (2 + 1 / Real.log 2) * corollaryOneRate horizon := by ring
    calc
      Real.log
            (1 + 4 * corollaryOneEta horizon * Delta * (horizon : Real)) /
              (2 * corollaryOneEta horizon) +
            1 / corollaryOneEta horizon <=
          (2 + 1 / Real.log 2) * corollaryOneRate horizon := hbase
      _ <= corollaryOneAbsoluteConstant * corollaryOneRate horizon := by
        apply mul_le_mul_of_nonneg_right _ hrate0
        unfold corollaryOneAbsoluteConstant
        nlinarith [Real.exp_pos 2]
  · rw [if_neg hsmall]
    have hgap := corollaryOne_gap_mul_horizon_le_exp_constant_mul_rate
      horizon hhorizon Delta hsmall
    calc
      Delta * (horizon : Real) <=
          (2 * Real.exp 2) * corollaryOneRate horizon := hgap
      _ <= corollaryOneAbsoluteConstant * corollaryOneRate horizon := by
        apply mul_le_mul_of_nonneg_right _ hrate0
        unfold corollaryOneAbsoluteConstant
        have hinvLog : 0 < 1 / Real.log 2 := by positivity
        nlinarith

/-- Exact finite two-branch version of source Corollary 1.  A separate fixed
rate is used for each source horizon `T = tailHorizon + 1`. -/
theorem twoArmFixedIIDDirac_corollaryOne_piecewise
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (mean : Fin 2 -> Real)
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm, |reward| <= 1)
    (hmean : forall arm, integral (armLaw arm) id = mean arm)
    (Delta : Real) (hDelta : 0 < Delta) (hDelta_lt_one : Delta < 1)
    (hgap : mean 0 - mean 1 = Delta)
    (tailHorizon : Nat) (horizon_ge_two : 1 <= tailHorizon) :
    let eta := corollaryOneEta (tailHorizon + 1)
    integral
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmSampledPseudoRegret (Env := Unit) Delta
          (tailHorizon + 1)) <=
      if 2 * eta * sourceC eta <= Delta then
        Real.log
            (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) /
            (2 * eta) +
          1 / eta
      else
        Delta * ((tailHorizon + 1 : Nat) : Real) := by
  dsimp only
  let eta := corollaryOneEta (tailHorizon + 1)
  have htwo : 2 <= tailHorizon + 1 := by omega
  have heta : 0 < eta := corollaryOneEta_pos _ htwo
  letI : IsProbabilityMeasure
      (twoArmTrajectoryMeasure (Measure.dirac ()) eta
        (twoArmFixedIIDEnvironment armLaw hprob)) := by
    dsimp [twoArmTrajectoryMeasure]
    infer_instance
  by_cases hsmall : 2 * eta * sourceC eta <= Delta
  · rw [if_pos hsmall]
    have hmargin := sourceTheoremOne_margin_of_two_mul_eta_sourceC_le
      eta Delta heta hDelta hsmall
    have htheoremOne := twoArmFixedIIDDirac_theoremOne
      armLaw hprob mean hbound hmean eta Delta heta hDelta hDelta_lt_one
        hgap hmargin tailHorizon
    have hbound := htheoremOne.trans (add_le_add_right
      (sourceTheoremOne_constant_le_inv_eta
        eta Delta heta hDelta hsmall)
      (Real.log
        (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) /
        (2 * eta)))
    simpa [eta, add_comm] using hbound
  · rw [if_neg hsmall]
    exact integral_twoArmSampledPseudoRegret_le_gap_mul_horizon
      (twoArmTrajectoryMeasure (Measure.dirac ()) eta
        (twoArmFixedIIDEnvironment armLaw hprob))
      Delta hDelta.le (tailHorizon + 1)

/-- Source Corollary 1 on the generated two-arm fixed-IID trajectory, with
an explicit absolute constant and no asymptotic notation.  The learning rate
is fixed within each horizon and may vary across the horizon-indexed family. -/
theorem twoArmFixedIIDDirac_corollaryOne
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (mean : Fin 2 -> Real)
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm, |reward| <= 1)
    (hmean : forall arm, integral (armLaw arm) id = mean arm)
    (Delta : Real) (hDelta : 0 < Delta) (hDelta_lt_one : Delta < 1)
    (hgap : mean 0 - mean 1 = Delta)
    (tailHorizon : Nat) (horizon_ge_two : 1 <= tailHorizon) :
    let eta := corollaryOneEta (tailHorizon + 1)
    integral
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmSampledPseudoRegret (Env := Unit) Delta
          (tailHorizon + 1)) <=
      corollaryOneAbsoluteConstant *
        corollaryOneRate (tailHorizon + 1) := by
  dsimp only
  have htwo : 2 <= tailHorizon + 1 := by omega
  have hpiece := twoArmFixedIIDDirac_corollaryOne_piecewise
    armLaw hprob mean hbound hmean Delta hDelta hDelta_lt_one hgap
      tailHorizon horizon_ge_two
  have hscalar := corollaryOne_piecewise_bound
    (tailHorizon + 1) htwo Delta hDelta hDelta_lt_one
  exact hpiece.trans hscalar

end

end StochasticGradientBandit
end BanditRLProof
