import BanditRLProof.LowerBounds.CommonDensityOverlap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The measure-level Jensen step in the Chapter 14 overlap proof. -/

namespace BanditRLProof.LowerBounds

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem mul_exp_neg_half_log_eq_sqrt {r : ℝ} (hr : 0 ≤ r) :
    r * Real.exp (-Real.log r / 2) = Real.sqrt r := by
  rcases eq_or_lt_of_le hr with h | h
  · simp [← h]
  · calc
      _ = Real.exp (Real.log r) * Real.exp (-Real.log r / 2) := by
        rw [Real.exp_log h]
      _ = Real.exp (Real.log r / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ = Real.sqrt r := by rw [Real.exp_half, Real.exp_log h]

theorem integrable_sqrt_rnDeriv
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => Real.sqrt (P.rnDeriv Q x).toReal) Q := by
  exact (memLp_sqrt_of_integrable_nonneg Measure.integrable_toReal_rnDeriv
    (fun _ => ENNReal.toReal_nonneg)).integrable (by norm_num)

theorem integrable_exp_neg_half_llr
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hPQ : P ≪ Q) :
    Integrable (fun x => Real.exp (-llr P Q x / 2)) P := by
  rw [← integrable_toReal_rnDeriv_mul_iff hPQ]
  simpa only [llr, mul_exp_neg_half_log_eq_sqrt ENNReal.toReal_nonneg]
    using integrable_sqrt_rnDeriv P Q

theorem integral_exp_neg_half_llr_eq
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hPQ : P ≪ Q) :
    (∫ x, Real.exp (-llr P Q x / 2) ∂P) =
      ∫ x, Real.sqrt (P.rnDeriv Q x).toReal ∂Q := by
  rw [← integral_toReal_rnDeriv_mul hPQ]
  simp only [llr, mul_exp_neg_half_log_eq_sqrt ENNReal.toReal_nonneg]

/-- Jensen's source proof step, in the RN representation and finite-KL branch. -/
theorem exp_neg_half_integral_llr_le_rnAffinity
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hi : Integrable (llr P Q) P) :
    Real.exp (-(∫ x, llr P Q x ∂P) / 2) ≤
      ∫ x, Real.sqrt (P.rnDeriv Q x).toReal ∂Q := by
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all P fun _ => mem_univ _)
    (hi.neg.div_const 2) (integrable_exp_neg_half_llr P Q hPQ)
  simp only [Pi.neg_apply] at h
  rw [integral_div, integral_neg, integral_exp_neg_half_llr_eq P Q hPQ] at h
  exact h

/-- Change the RN affinity to any common sigma-finite dominating measure. -/
theorem rnAffinity_eq_commonDensityAffinity
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [SigmaFinite μ]
    (hPQ : P ≪ Q) (hQ : Q ≪ μ) :
    (∫ x, Real.sqrt (P.rnDeriv Q x).toReal ∂Q) = commonDensityAffinity P Q μ := by
  rw [← integral_toReal_rnDeriv_mul hQ, commonDensityAffinity]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := μ) hPQ] with x hx
  have heq : (P.rnDeriv Q x).toReal * (Q.rnDeriv μ x).toReal =
      (P.rnDeriv μ x).toReal := by
    simpa only [Pi.mul_apply, ENNReal.toReal_mul] using congrArg ENNReal.toReal hx
  rw [← heq]
  have halg : (P.rnDeriv Q x).toReal * (Q.rnDeriv μ x).toReal *
      (Q.rnDeriv μ x).toReal = (P.rnDeriv Q x).toReal * (Q.rnDeriv μ x).toReal ^ 2 := by ring
  rw [halg, Real.sqrt_mul ENNReal.toReal_nonneg,
    Real.sqrt_sq ENNReal.toReal_nonneg]
  ring

/-- The source's measure-level Jensen step with arbitrary common domination. -/
theorem exp_neg_half_integral_llr_le_commonDensityAffinity
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hPQ : P ≪ Q) (hQ : Q ≪ μ) (hi : Integrable (llr P Q) P) :
    Real.exp (-(∫ x, llr P Q x ∂P) / 2) ≤ commonDensityAffinity P Q μ := by
  rw [← rnAffinity_eq_commonDensityAffinity P Q μ hPQ hQ]
  exact exp_neg_half_integral_llr_le_rnAffinity P Q hPQ hi

/-- The squared-affinity/KL bound, with the infinite-KL branch explicit. -/
theorem bretagnolleHuberScale_le_half_commonDensityAffinity_sq
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hQ : Q ≪ μ) :
    bretagnolleHuberScale (relativeEntropy P Q) ≤
      (1 / 2 : ℝ) * commonDensityAffinity P Q μ ^ 2 := by
  by_cases ht : relativeEntropy P Q = ⊤
  · simp only [bretagnolleHuberScale, ht, ↓reduceIte]
    positivity
  have hr := relativeEntropy_ne_top_iff.1 ht
  have hj := exp_neg_half_integral_llr_le_commonDensityAffinity P Q μ hr.1 hQ hr.2
  have ha : 0 ≤ commonDensityAffinity P Q μ :=
    integral_nonneg fun x => Real.sqrt_nonneg _
  have hs := (sq_le_sq₀ (Real.exp_pos _).le ha).2 hj
  have he : Real.exp (-(∫ x, llr P Q x ∂P) / 2) ^ 2 =
      Real.exp (-(∫ x, llr P Q x ∂P)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hk : (relativeEntropy P Q).toReal = ∫ x, llr P Q x ∂P := by
    simpa only [relativeEntropy, probReal_univ, add_sub_cancel_right]
      using InformationTheory.toReal_klDiv hr.1 hr.2
  rw [he] at hs
  simp only [bretagnolleHuberScale, ht, ↓reduceIte, hk]
  linarith

end
end BanditRLProof.LowerBounds
