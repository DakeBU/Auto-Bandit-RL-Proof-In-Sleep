import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic
import Mathlib.Probability.BorelCantelli
import BanditRLProof.MartingaleDifference

/-! # No-cardinality-loss finite maximal concentration

This module supplies the martingale analytic dependency for source Theorem 9.2.
Identifying an independent reward partial sum as this martingale is separate.
-/

namespace BanditRLProof.Concentration

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℕ ‹MeasurableSpace Ω›} {S : ℕ → Ω → ℝ}

/-- Conditional Jensen turns an exponentially integrable real martingale
into a nonnegative exponential submartingale. -/
theorem submartingale_exp_of_martingale (hS : Martingale S F μ)
    (hint : ∀ i, Integrable (fun ω => exp (S i ω)) μ) :
    Submartingale (fun i ω => exp (S i ω)) F μ := by
  refine ⟨fun i => continuous_exp.comp_stronglyMeasurable (hS.stronglyAdapted i),
    fun i j hij => ?_, hint⟩
  have hj := convexOn_exp.map_condExp_le_univ (F.le i)
    continuous_exp.lowerSemicontinuous (hS.integrable j) (hint j)
  filter_upwards [hj, hS.condExp_ae_eq hij] with ω hj hEq
  simpa only [Function.comp_apply, hEq] using hj

/-- Finite-time maximal Chernoff bound with no union-bound cardinality factor.
The terminal MGF supplies the variance budget; all-time exponential
integrability is explicit for the Jensen producer. -/
theorem measure_exists_le_martingale_ge_le_exp (hS : Martingale S F μ)
    (hint : ∀ i t, Integrable (fun ω => exp (t * S i ω)) μ)
    (n : ℕ) (c : ℝ≥0) (hmgf : HasSubgaussianMGF (S n) c μ)
    (ε t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ i, i ≤ n ∧ ε ≤ S i ω} ≤
      ENNReal.ofReal (exp (-t * ε + (c : ℝ) * t ^ 2 / 2)) := by
  have hscaled : Martingale (fun i ω => t * S i ω) F μ := hS.smul t
  have hexp := submartingale_exp_of_martingale hscaled (fun i => hint i t)
  let a : ℝ≥0 := ⟨exp (t * ε), (exp_pos _).le⟩
  let B : Set Ω := {ω | (a : ℝ) ≤
    (range (n + 1)).sup' nonempty_range_add_one (fun i => exp (t * S i ω))}
  have hsub : {ω | ∃ i, i ≤ n ∧ ε ≤ S i ω} ⊆ B := by
    rintro ω ⟨i, hi, hε⟩
    exact (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hε ht.le)).trans
      (le_sup' (f := fun j => exp (t * S j ω)) (mem_range.mpr (Nat.lt_succ_of_le hi)))
  have hd : (a : ℝ≥0∞) * μ B ≤ ENNReal.ofReal (exp ((c : ℝ) * t ^ 2 / 2)) := by
    refine (maximal_ineq hexp (fun i ω => (exp_pos _).le) n).trans ?_
    apply ENNReal.ofReal_le_ofReal
    exact (setIntegral_le_integral (hint n t)
      (Filter.Eventually.of_forall fun ω => (exp_pos _).le)).trans (hmgf.mgf_le t)
  have hbound := (mul_le_mul_left' (measure_mono hsub) (a : ℝ≥0∞)).trans hd
  have hr := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hbound
  have hr' : exp (t * ε) * (μ {ω | ∃ i, i ≤ n ∧ ε ≤ S i ω}).toReal ≤
      exp ((c : ℝ) * t ^ 2 / 2) := by
    simpa [ENNReal.toReal_mul, a, (exp_pos _).le] using hr
  have hreal : (μ {ω | ∃ i, i ≤ n ∧ ε ≤ S i ω}).toReal ≤
      exp (-t * ε + (c : ℝ) * t ^ 2 / 2) := by
    have hdiv : (μ {ω | ∃ i, i ≤ n ∧ ε ≤ S i ω}).toReal ≤
        exp ((c : ℝ) * t ^ 2 / 2) / exp (t * ε) :=
      (le_div_iff₀ (exp_pos (t * ε))).2
      (by simpa [mul_comm] using hr')
    rw [← exp_sub] at hdiv
    convert hdiv using 1 <;> congr 1 <;> ring
  simpa using ENNReal.ofReal_le_ofReal hreal

/-- Optimized finite maximal subgaussian bound. -/
theorem measure_exists_le_martingale_ge_le_subgaussian (hS : Martingale S F μ)
    (hint : ∀ i t, Integrable (fun ω => exp (t * S i ω)) μ)
    (n : ℕ) (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (hmgf : HasSubgaussianMGF (S n) c μ) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ∃ i, i ≤ n ∧ ε ≤ S i ω} ≤
      ENNReal.ofReal (exp (-(ε ^ 2) / (2 * (c : ℝ)))) := by
  have h := measure_exists_le_martingale_ge_le_exp hS hint n c hmgf ε
    (ε / (c : ℝ)) (div_pos hε hc)
  have heq : -(ε / (c : ℝ)) * ε + (c : ℝ) * (ε / (c : ℝ)) ^ 2 / 2 =
      -(ε ^ 2) / (2 * (c : ℝ)) := by
    field_simp [ne_of_gt hc]
    <;> ring
  simpa only [heq] using h

/-- Source Theorem 9.2 shape for independent centered subgaussian increments.
The source variance is `c = σ²`; the partial sum uses X1 through Xn.
Centering and coordinate measurability are explicit model contracts. -/
theorem measure_exists_le_independent_partialSum_ge_le_subgaussian
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, StronglyMeasurable (X i))
    (hind : iIndepFun X μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (hsubG : ∀ i, HasSubgaussianMGF (X i) c μ)
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ∃ i, i ≤ n ∧ ε ≤ ∑ j ∈ range i, X (j + 1) ω} ≤
      ENNReal.ofReal (exp (-(ε ^ 2) / (2 * (n : ℝ) * (c : ℝ)))) := by
  have hdiff : MartingaleDiff.SuccMartingaleDifference μ (Filtration.natural X hXm) X := {
    stronglyAdapted := Filtration.stronglyAdapted_natural hXm
    integrable := fun i => (hsubG i).integrable
    condExp_succ_eq_zero := fun i => by
      simpa only [hmean] using hind.condExp_natural_ae_eq_of_lt hXm (Nat.lt_succ_self i)
  }
  have hmart := MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference μ hdiff
  have hsum (m : ℕ) : HasSubgaussianMGF (MartingaleDiff.partialSumsSucc X m)
      ((m : ℝ≥0) * c) μ := by
    have h := HasSubgaussianMGF.sum_of_iIndepFun
      (hind.precomp Nat.succ_injective) (s := range m) (c := fun _ => c)
      (fun i _ => hsubG (i + 1))
    have heq : MartingaleDiff.partialSumsSucc X m =
        (fun ω => ∑ i ∈ range m, X (i + 1) ω) := by
      funext ω
      simp [MartingaleDiff.partialSumsSucc, sum_apply]
    rw [heq]
    simpa using h
  have h := measure_exists_le_martingale_ge_le_subgaussian hmart
    (fun i t => (hsum i).integrable_exp_mul t) n ((n : ℝ≥0) * c)
    (by simpa using mul_pos (Nat.cast_pos.mpr hn : 0 < (n : ℝ)) hc)
    (hsum n) ε hε
  simpa [MartingaleDiff.partialSumsSucc, sum_apply, mul_assoc] using h

end BanditRLProof.Concentration
