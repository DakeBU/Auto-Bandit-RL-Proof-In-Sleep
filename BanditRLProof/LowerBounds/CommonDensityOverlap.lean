import BanditRLProof.LowerBounds.CommonDensityKL
import Mathlib.MeasureTheory.Function.L2Space

/-! Measure-level overlap in Chapter 14, including the optimal testing event. -/

namespace BanditRLProof.LowerBounds

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Square roots of nonnegative integrable functions belong to L2. -/
theorem memLp_sqrt_of_integrable_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) (hpos : ∀ x, 0 ≤ f x) :
    MemLp (fun x => Real.sqrt (f x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).2
  have heq : (fun x => Real.sqrt (f x) ^ 2) = f :=
    funext fun x => Real.sq_sqrt (hpos x)
  rwa [heq]

/-- Cauchy--Schwarz for the square-root affinity integrand. -/
theorem integral_sqrt_mul_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : α → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) :
    (∫ x, Real.sqrt (p x * q x) ∂μ) ^ 2 ≤ (∫ x, p x ∂μ) * ∫ x, q x ∂μ := by
  have hp2 := memLp_sqrt_of_integrable_nonneg hp hp0
  have hq2 := memLp_sqrt_of_integrable_nonneg hq hq0
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ fun x => Real.sqrt_nonneg (p x))
    (ae_of_all μ fun x => Real.sqrt_nonneg (q x))
    (by simpa using hp2) (by simpa using hq2)
  have hpPow (x) : Real.sqrt (p x) ^ (2 : ℝ) = p x := by
    rw [Real.rpow_two, Real.sq_sqrt (hp0 x)]
  have hqPow (x) : Real.sqrt (q x) ^ (2 : ℝ) = q x := by
    rw [Real.rpow_two, Real.sq_sqrt (hq0 x)]
  simp_rw [hpPow, hqPow, ← Real.sqrt_eq_rpow] at hcs
  have heq : (fun x => Real.sqrt (p x) * Real.sqrt (q x)) =
      (fun x => Real.sqrt (p x * q x)) :=
    funext fun x => (Real.sqrt_mul (hp0 x) (q x)).symm
  rw [heq] at hcs
  have hs := (sq_le_sq₀ (integral_nonneg fun x => Real.sqrt_nonneg (p x * q x))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hcs
  simpa only [mul_pow, Real.sq_sqrt (integral_nonneg hp0),
    Real.sq_sqrt (integral_nonneg hq0)] using hs

/-- Integral of the pointwise minimum of common RN densities. -/
def commonDensityOverlap {α : Type*} [MeasurableSpace α] (P Q μ : Measure α) : ℝ :=
  ∫ x, min (P.rnDeriv μ x).toReal (Q.rnDeriv μ x).toReal ∂μ

/-- Hellinger affinity of two densities relative to a common measure. -/
def commonDensityAffinity {α : Type*} [MeasurableSpace α] (P Q μ : Measure α) : ℝ :=
  ∫ x, Real.sqrt ((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) ∂μ

theorem integrable_commonDensityAffinity
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => Real.sqrt
      ((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)) μ := by
  have hp := memLp_sqrt_of_integrable_nonneg
    (Measure.integrable_toReal_rnDeriv (μ := P) (ν := μ))
    (fun _ => ENNReal.toReal_nonneg)
  have hq := memLp_sqrt_of_integrable_nonneg
    (Measure.integrable_toReal_rnDeriv (μ := Q) (ν := μ))
    (fun _ => ENNReal.toReal_nonneg)
  have h := hp.integrable_mul hq
  change Integrable (fun x => Real.sqrt (P.rnDeriv μ x).toReal *
    Real.sqrt (Q.rnDeriv μ x).toReal) μ at h
  simpa only [← Real.sqrt_mul ENNReal.toReal_nonneg] using h

/-- Eq. (14.9), including integrable densities with zeros. -/
theorem half_commonDensityAffinity_sq_le_overlap
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) :
    (1 / 2 : ℝ) * commonDensityAffinity P Q μ ^ 2 ≤
      commonDensityOverlap P Q μ := by
  let p := fun x => (P.rnDeriv μ x).toReal
  let q := fun x => (Q.rnDeriv μ x).toReal
  have hp : Integrable p μ := Measure.integrable_toReal_rnDeriv
  have hq : Integrable q μ := Measure.integrable_toReal_rnDeriv
  have hp0 (x) : 0 ≤ p x := ENNReal.toReal_nonneg
  have hq0 (x) : 0 ≤ q x := ENNReal.toReal_nonneg
  have hcs := integral_sqrt_mul_sq_le (hp.inf hq) (hp.sup hq)
    (fun x => le_min (hp0 x) (hq0 x))
    (fun x => le_trans (hp0 x) (le_max_left _ _))
  simp only [Pi.inf_apply, Pi.sup_apply, min_mul_max] at hcs
  have hmax : (∫ x, max (p x) (q x) ∂μ) ≤ 2 := by
    calc
      _ ≤ ∫ x, p x + q x ∂μ := integral_mono (hp.sup hq) (hp.add hq)
        (fun x => max_le (le_add_of_nonneg_right (hq0 x))
          (le_add_of_nonneg_left (hp0 x)))
      _ = 2 := by
        rw [integral_add hp hq]
        dsimp [p, q]
        rw [Measure.integral_toReal_rnDeriv hP, Measure.integral_toReal_rnDeriv hQ]
        norm_num
  have hmin : 0 ≤ ∫ x, min (p x) (q x) ∂μ :=
    integral_nonneg fun x => le_min (hp0 x) (hq0 x)
  have hb := mul_le_mul_of_nonneg_left hmax hmin
  change (1 / 2 : ℝ) * (∫ x, Real.sqrt (p x * q x) ∂μ) ^ 2 ≤
    ∫ x, min (p x) (q x) ∂μ
  nlinarith

/-- The event selecting the smaller source density. -/
def commonDensityComparisonEvent {α : Type*} [MeasurableSpace α]
    (P Q μ : Measure α) : Set α :=
  {x | (P.rnDeriv μ x).toReal ≤ (Q.rnDeriv μ x).toReal}

theorem measurableSet_commonDensityComparisonEvent
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α) :
    MeasurableSet (commonDensityComparisonEvent P Q μ) :=
  measurableSet_le (by fun_prop) (by fun_prop)

theorem integrable_min_commonDensity
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => min (P.rnDeriv μ x).toReal (Q.rnDeriv μ x).toReal) μ :=
  Measure.integrable_toReal_rnDeriv.inf Measure.integrable_toReal_rnDeriv

theorem commonDensityOverlap_nonneg
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α) :
    0 ≤ commonDensityOverlap P Q μ :=
  integral_nonneg fun _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The likelihood comparison event attains the density-overlap testing error. -/
theorem commonDensityOverlap_eq_testingError
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) :
    commonDensityOverlap P Q μ =
      P.real (commonDensityComparisonEvent P Q μ) +
        Q.real (commonDensityComparisonEvent P Q μ)ᶜ := by
  let A := commonDensityComparisonEvent P Q μ
  have hA : MeasurableSet A := measurableSet_commonDensityComparisonEvent P Q μ
  rw [commonDensityOverlap, ← integral_add_compl hA (integrable_min_commonDensity P Q μ)]
  calc
    _ = (∫ x in A, (P.rnDeriv μ x).toReal ∂μ) +
        ∫ x in Aᶜ, (Q.rnDeriv μ x).toReal ∂μ := by
      congr 1
      · apply setIntegral_congr_fun hA
        intro x hx
        exact min_eq_left hx
      · apply setIntegral_congr_fun hA.compl
        intro x hx
        exact min_eq_right (le_of_lt (lt_of_not_ge hx))
    _ = _ := by
      rw [Measure.setIntegral_toReal_rnDeriv hP A,
        Measure.setIntegral_toReal_rnDeriv hQ Aᶜ]

/-- Eq. (14.8): the measure overlap is bounded below by the BH exponential scale. -/
theorem bretagnolleHuberScale_le_commonDensityOverlap
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) :
    bretagnolleHuberScale (relativeEntropy P Q) ≤ commonDensityOverlap P Q μ := by
  rw [commonDensityOverlap_eq_testingError P Q μ hP hQ]
  exact bretagnolleHuber (measurableSet_commonDensityComparisonEvent P Q μ)

end
end BanditRLProof.LowerBounds
