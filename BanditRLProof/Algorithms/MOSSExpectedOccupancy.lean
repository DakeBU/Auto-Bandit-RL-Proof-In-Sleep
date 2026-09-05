import BanditRLProof.Algorithms.MOSSOccupancy
import BanditRLProof.ConcentrationIndexOccupancy
import BanditRLProof.Algorithms.MOSSConstants

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
namespace BanditRLProof.MOSS
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def streamMean (X : ℕ → Ω → ℝ) (ω : Ω) (s : ℕ) : ℝ := peelingSum X s ω/(s : ℝ)

theorem fixedLogExceedanceCount_eq_fixedRadiusCount (X : ℕ → Ω → ℝ)
    (δ gap : ℝ) (n : ℕ) (ω : Ω) :
    fixedLogExceedanceCount (streamMean X ω) δ gap n =
      Concentration.fixedRadiusCount X (2*logPlus (gap^2/δ)) (gap/2) n ω := by
  unfold fixedLogExceedanceCount Concentration.fixedRadiusCount
  apply Finset.sum_congr rfl
  intro s hs
  have hr : 4/((s+1 : ℕ) : ℝ)*logPlus (gap^2/δ) =
      2*(2*logPlus (gap^2/δ))/((s+1 : ℕ) : ℝ) := by ring
  simp only [Set.indicator_apply, Concentration.fixedRadiusMeanEvent, Set.mem_setOf_eq,
    streamMean, peelingSum, fixedLogRadius, hr]

/-- Finite measurable indicator counts are integrable, without tail assumptions. -/
theorem integrable_indexExceedanceCount (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (δ gap : ℝ) (n : ℕ) :
    Integrable (fun ω => indexExceedanceCount (streamMean X ω) δ gap n) μ := by
  classical
  unfold indexExceedanceCount
  apply integrable_finset_sum
  intro s _
  have hm : MeasurableSet {ω | gap/2 ≤ centeredIndex X δ (s+1) ω} :=
    measurableSet_le measurable_const (stronglyMeasurable_centeredIndex X hXm δ (s+1)).measurable
  have hi := (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).indicator hm
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, centeredIndex, streamMean] using hi

theorem integral_indexExceedanceCount_le_sharp (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (hlarge : δ < gap^2) (n : ℕ) :
    (∫ ω, indexExceedanceCount (streamMean X ω) δ gap n ∂μ) ≤
      1/gap^2 + (8/gap^2)*(2*logPlus (gap^2/δ)+sqrt (Real.pi*(2*logPlus (gap^2/δ)))+1) := by
  have hlog : 0 < logPlus (gap^2/δ) := by
    unfold logPlus
    apply log_pos
    exact lt_of_lt_of_le ((one_lt_div hδ).mpr hlarge) (le_max_right _ _)
  have hi := Concentration.integrable_fixedRadiusCount (μ := μ) X hXm
    (2*logPlus (gap^2/δ)) (gap/2) n
  have hle := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun ω => show 0 ≤ indexExceedanceCount (streamMean X ω) δ gap n from by
      unfold indexExceedanceCount
      apply Finset.sum_nonneg
      intro s hs
      split_ifs <;> norm_num))
    ((integrable_const (1/gap^2)).add hi)
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [Pi.add_apply, ← fixedLogExceedanceCount_eq_fixedRadiusCount] using
        indexExceedanceCount_le_inv_sq_add_fixed (streamMean X ω) δ gap hδ hg n))
  simp only [Pi.add_apply] at hle
  rw [integral_add (integrable_const _) hi] at hle
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hle
  have hb := Concentration.integral_fixedRadiusCount_le_sharp X hXm hind hmean hsubG
    (2*logPlus (gap^2/δ)) (gap/2) (by positivity) (by positivity) n
  have he : 2/(gap/2)^2 = 8/gap^2 := by ring
  rw [he] at hb
  linarith

theorem integral_indexExceedanceCount_le (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (hlarge : δ < gap^2) (n : ℕ) :
    (∫ ω, indexExceedanceCount (streamMean X ω) δ gap n ∂μ) ≤
      1/gap^2 + 1 + (8/gap^2)*(2*logPlus (gap^2/δ)+sqrt (Real.pi*(2*logPlus (gap^2/δ)))+1) := by
  have h := integral_indexExceedanceCount_le_sharp X hXm hind hmean hsubG δ gap hδ hg hlarge n
  linarith

theorem gap_mul_integral_indexExceedanceCount_le_sharp (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (hlarge : 8*sqrt δ ≤ gap) (n : ℕ) :
    gap*(∫ ω, indexExceedanceCount (streamMean X ω) δ gap n ∂μ) ≤ 15/sqrt δ := by
  have hlg : δ < gap^2 := by
    nlinarith [sq_sqrt hδ.le, sqrt_nonneg δ, sq_nonneg (gap-8*sqrt δ)]
  have h := mul_le_mul_of_nonneg_left
    (integral_indexExceedanceCount_le_sharp X hXm hind hmean hsubG δ gap hδ hg hlg n) hg.le
  have hc := largeGap_scaled_constant_fifteen δ gap hδ hg hlarge
  nlinarith

/-- Source large-gap weighted occupancy bound, before selected-count transport. -/
theorem gap_mul_integral_indexExceedanceCount_le (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (hlarge : 8*sqrt δ ≤ gap) (n : ℕ) :
    gap*(∫ ω, indexExceedanceCount (streamMean X ω) δ gap n ∂μ) ≤ gap+15/sqrt δ := by
  have hlg : δ < gap^2 := by
    have hs := sq_sqrt hδ.le
    have hn := sqrt_nonneg δ
    nlinarith [sq_nonneg (gap-8*sqrt δ)]
  exact (mul_le_mul_of_nonneg_left
    (integral_indexExceedanceCount_le X hXm hind hmean hsubG δ gap hδ hg hlg n) hg.le).trans
      (largeGap_scaled_constant_fifteen δ gap hδ hg hlarge)

end BanditRLProof.MOSS
