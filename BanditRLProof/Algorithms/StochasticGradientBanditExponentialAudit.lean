import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmRate

/-!
# Stochastic-gradient-bandit exponential-moment audit

This module formalizes the source constant `C_eta` and Equation (8) from the
two-arm proof of Baudry--Johnson--Vary--Pike-Burke--Rebeschini (NeurIPS 2025).
For an almost-everywhere measurable reward supported on `[-1, 1]`, it derives
the exact second-order moment-generating-function inequality used by the
paper.  It also proves the source comparison `C_eta <= exp (2 * eta)` for
nonnegative `eta`.

The declarations below do not yet instantiate Equation (8) inside the
generated SGB trajectory, prove either conditional exponential recurrence,
bound the expected squared failure mass, or assemble Theorem 1.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open scoped BigOperators

noncomputable section

/-- A factorial comparison used to dominate the shifted exponential series. -/
theorem two_mul_abs_pow_div_factorial_add_two_le (x : Real) (n : Nat) :
    2 * |x| ^ n / ((n + 2).factorial : Real) <=
      |x| ^ n / (n.factorial : Real) := by
  have hfact :
      (2 : Real) * (n.factorial : Real) <= ((n + 2).factorial : Real) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    have hn : (0 : Real) < n.factorial := by positivity
    have hpoly : 0 <= (n : Real) * ((n : Real) + 3) := by positivity
    nlinarith
  have hnum : 0 <= |x| ^ n := by positivity
  have hnfac : (0 : Real) < n.factorial := by positivity
  have hn2fac : (0 : Real) < (n + 2).factorial := by positivity
  rw [div_le_div_iff₀ hn2fac hnfac]
  nlinarith

/-- The source constant
`C_eta = 2 * sum_{n >= 0} (2 * eta)^n / (n + 2)!`. -/
noncomputable def sourceC (eta : Real) : Real :=
  2 * ∑' n : Nat, (2 * eta) ^ n / ((n + 2).factorial : Real)

theorem sourceC_terms_summable (eta : Real) :
    Summable (fun n : Nat =>
      (2 * eta) ^ n / ((n + 2).factorial : Real)) := by
  apply Summable.of_norm_bounded
    (Real.summable_pow_div_factorial |2 * eta|)
  intro n
  simpa using (show
    ‖(2 * eta) ^ n / ((n + 2).factorial : Real)‖ <=
      |2 * eta| ^ n / (n.factorial : Real) by
        have hfactnat : n.factorial <= (n + 2).factorial :=
          Nat.factorial_le (by omega)
        have hfact : (n.factorial : Real) <= ((n + 2).factorial : Real) := by
          exact_mod_cast hfactnat
        have hnfac : (0 : Real) < n.factorial := by positivity
        rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_natCast]
        exact div_le_div_of_nonneg_left (by positivity) hnfac hfact)

theorem sourceC_nonneg (eta : Real) (heta : 0 <= eta) :
    0 <= sourceC eta := by
  unfold sourceC
  positivity

/-- Monotonicity needed to replace the time-varying source constants in the
Theorem-1 recurrences by a common `C_eta`. -/
theorem sourceC_mono {eta eta' : Real} (heta : 0 <= eta)
    (hle : eta <= eta') : sourceC eta <= sourceC eta' := by
  unfold sourceC
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Summable.tsum_le_tsum
  · intro n
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (by positivity : 0 <= 2 * eta) (by linarith) n
  · exact sourceC_terms_summable eta
  · exact sourceC_terms_summable eta'

/-- The source comparison following Theorem 1: `C_eta <= exp (2 * eta)`. -/
theorem sourceC_le_exp_two_mul (eta : Real) (heta : 0 <= eta) :
    sourceC eta <= Real.exp (2 * eta) := by
  unfold sourceC
  rw [← tsum_mul_left]
  rw [Real.exp_eq_exp_ℝ,
    ← (NormedSpace.expSeries_div_hasSum_exp (2 * eta)).tsum_eq]
  apply Summable.tsum_le_tsum
  · intro n
    have h := two_mul_abs_pow_div_factorial_add_two_le (2 * eta) n
    rw [abs_of_nonneg (by positivity : 0 <= 2 * eta)] at h
    calc
      2 * ((2 * eta) ^ n / ((n + 2).factorial : Real)) =
          2 * (2 * eta) ^ n / ((n + 2).factorial : Real) := by ring
      _ <= (2 * eta) ^ n / (n.factorial : Real) := h
  · exact (sourceC_terms_summable eta).mul_left 2
  · exact Real.summable_pow_div_factorial (2 * eta)

/-- The exponential-series tail beginning at degree two. -/
noncomputable def expTailTwo (x : Real) : Real :=
  ∑' n : Nat, x ^ (n + 2) / ((n + 2).factorial : Real)

theorem expTailTwo_terms_summable (x : Real) :
    Summable (fun n : Nat =>
      x ^ (n + 2) / ((n + 2).factorial : Real)) := by
  exact (summable_nat_add_iff 2).mpr
    (Real.summable_pow_div_factorial x)

theorem exp_eq_one_add_self_add_expTailTwo (x : Real) :
    Real.exp x = 1 + x + expTailTwo x := by
  have h := (Real.summable_pow_div_factorial x).sum_add_tsum_nat_add 2
  rw [Real.exp_eq_exp_ℝ,
    ← (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq]
  unfold expTailTwo
  simpa [Finset.sum_range_succ, add_assoc] using h.symm

theorem expTailTwo_le_of_abs_le {x y : Real} (hxy : |x| <= y) :
    expTailTwo x <= expTailTwo y := by
  unfold expTailTwo
  apply Summable.tsum_le_tsum
  · intro n
    have hpow : x ^ (n + 2) <= y ^ (n + 2) := calc
      x ^ (n + 2) <= |x ^ (n + 2)| := le_abs_self _
      _ = |x| ^ (n + 2) := abs_pow x (n + 2)
      _ <= y ^ (n + 2) := pow_le_pow_left₀ (abs_nonneg x) hxy (n + 2)
    exact div_le_div_of_nonneg_right hpow (by positivity)
  · exact expTailTwo_terms_summable x
  · exact expTailTwo_terms_summable y

theorem sq_div_two_mul_sourceC_abs_div_two (q : Real) :
    q ^ 2 / 2 * sourceC (|q| / 2) = expTailTwo |q| := by
  unfold sourceC expTailTwo
  rw [show 2 * (|q| / 2) = |q| by ring]
  calc
    q ^ 2 / 2 *
        (2 * ∑' n : Nat, |q| ^ n / ((n + 2).factorial : Real)) =
      q ^ 2 * ∑' n : Nat, |q| ^ n / ((n + 2).factorial : Real) := by ring
    _ = ∑' n : Nat,
        q ^ 2 * (|q| ^ n / ((n + 2).factorial : Real)) := by
      rw [tsum_mul_left]
    _ = ∑' n : Nat, |q| ^ (n + 2) / ((n + 2).factorial : Real) := by
      apply tsum_congr
      intro n
      rw [← sq_abs q, pow_add]
      ring

/-- Pointwise form of source Equation (8). -/
theorem exp_mul_le_sourceEqEight (q reward : Real)
    (hreward : |reward| <= 1) :
    Real.exp (q * reward) <=
      1 + q * reward + q ^ 2 / 2 * sourceC (|q| / 2) := by
  rw [exp_eq_one_add_self_add_expTailTwo,
    sq_div_two_mul_sourceC_abs_div_two]
  gcongr
  apply expTailTwo_le_of_abs_le
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg q) hreward

/-- Expectation form of source Equation (8), with integrability explicit. -/
theorem integral_exp_mul_le_sourceEqEight
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (q : Real) (reward : Omega -> Real)
    (hrewardIntegrable : MeasureTheory.Integrable reward mu)
    (hexpIntegrable :
      MeasureTheory.Integrable (fun omega => Real.exp (q * reward omega)) mu)
    (hreward : ∀ᵐ omega ∂mu, |reward omega| <= 1) :
    (∫ omega, Real.exp (q * reward omega) ∂mu) <=
      1 + q * (∫ omega, reward omega ∂mu) +
        q ^ 2 / 2 * sourceC (|q| / 2) := by
  have hright : MeasureTheory.Integrable
      (fun omega =>
        1 + q * reward omega + q ^ 2 / 2 * sourceC (|q| / 2)) mu :=
    ((MeasureTheory.integrable_const 1).add
      (hrewardIntegrable.const_mul q)).add
        (MeasureTheory.integrable_const
          (q ^ 2 / 2 * sourceC (|q| / 2)))
  have hmono := MeasureTheory.integral_mono_ae hexpIntegrable hright
    (hreward.mono fun omega homega => exp_mul_le_sourceEqEight q (reward omega) homega)
  rw [MeasureTheory.integral_add, MeasureTheory.integral_add] at hmono
  · simpa [MeasureTheory.integral_const_mul,
      MeasureTheory.probReal_univ] using hmono
  · exact MeasureTheory.integrable_const 1
  · exact hrewardIntegrable.const_mul q
  · exact (MeasureTheory.integrable_const 1).add
      (hrewardIntegrable.const_mul q)
  · exact MeasureTheory.integrable_const
      (q ^ 2 / 2 * sourceC (|q| / 2))

/-- Equation (8) from measurability and almost-sure support in `[-1, 1]`. -/
theorem integral_exp_mul_le_sourceEqEight_of_ae_abs_le_one
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (q : Real) (reward : Omega -> Real)
    (hrewardMeasurable :
      MeasureTheory.AEStronglyMeasurable reward mu)
    (hreward : ∀ᵐ omega ∂mu, |reward omega| <= 1) :
    (∫ omega, Real.exp (q * reward omega) ∂mu) <=
      1 + q * (∫ omega, reward omega ∂mu) +
        q ^ 2 / 2 * sourceC (|q| / 2) := by
  have hrewardIntegrable : MeasureTheory.Integrable reward mu :=
    MeasureTheory.Integrable.of_bound hrewardMeasurable 1
      (hreward.mono fun omega homega => by
        simpa [Real.norm_eq_abs] using homega)
  have hexpMeasurable : MeasureTheory.AEStronglyMeasurable
      (fun omega => Real.exp (q * reward omega)) mu :=
    Real.continuous_exp.comp_aestronglyMeasurable
      (hrewardMeasurable.const_mul q)
  have hexpBound : ∀ᵐ omega ∂mu,
      ‖Real.exp (q * reward omega)‖ <= Real.exp |q| :=
    hreward.mono fun omega homega => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      calc
        q * reward omega <= |q * reward omega| := le_abs_self _
        _ = |q| * |reward omega| := abs_mul q (reward omega)
        _ <= |q| := mul_le_of_le_one_right (abs_nonneg q) homega
  have hexpIntegrable : MeasureTheory.Integrable
      (fun omega => Real.exp (q * reward omega)) mu :=
    MeasureTheory.Integrable.of_bound hexpMeasurable (Real.exp |q|) hexpBound
  exact integral_exp_mul_le_sourceEqEight mu q reward
    hrewardIntegrable hexpIntegrable hreward

end

end StochasticGradientBandit
end BanditRLProof
