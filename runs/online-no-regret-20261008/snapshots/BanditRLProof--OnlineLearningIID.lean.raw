import BanditRLProof.OnlineLearningInformation
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory

namespace BanditRL.OnlineLearning

/-- Measurability of the actual source predictor. -/
theorem meanPredict_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (t : ℕ) :
    Measurable (fun ω => meanPredict (fun i => Y i ω) t) := by
  unfold meanPredict empiricalMean
  split_ifs <;> fun_prop

/-- Bounded source observations imply square integrability of the actual prediction. -/
theorem meanPredict_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    MemLp (fun ω => meanPredict (fun i => Y i ω) t) 2 μ := by
  apply memLp_of_bounded (a := 0) (b := 1) _ (meanPredict_measurable Y hY t).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => meanPredict_mem (fun i => Y i ω) t (fun i hi => hb i ω))

/-- Source equation (1.1) is a sum of nonnegative mean-estimation errors for the actual strategy. -/
theorem iid_meanPredict_excess {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    (∫ ω, ∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) -
      T * variance (Y 0) μ =
        ∑ t ∈ Finset.range T,
          ∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ := by
  have hL (t : ℕ) : MemLp (Y t) 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall (hb t)) (hY t).aestronglyMeasurable 2
  have hP (t : ℕ) := meanPredict_memLp μ Y hY hb t
  have hi := integral_finset_sum (Finset.range T)
    (f := fun t ω => (meanPredict (fun i => Y i ω) t - Y t ω)^2)
    (fun t ht => ((hP t).sub (hL t)).integrable_sq)
  rw [hi]
  have heq (t : ℕ) := independent_prediction_square μ
    (fun ω => meanPredict (fun i => Y i ω) t) (Y t) (hP t) (hL t)
    (meanPredict_independent μ Y hY hind t)
  have heq' (t : ℕ) :
      (∫ ω, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) =
      (∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) + variance (Y 0) μ := by
    simpa only [(hlaw t).integral_eq, (hlaw t).variance_eq] using heq t
  simp_rw [heq']
  simp [Finset.sum_add_distrib]

/-- The source's expected excess is nonnegative. -/
theorem iid_meanPredict_excess_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    0 ≤ (∫ ω, ∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) -
      T * variance (Y 0) μ := by
  rw [iid_meanPredict_excess μ Y hY hind hlaw hb T]
  exact Finset.sum_nonneg (fun t ht => integral_nonneg (fun ω => sq_nonneg _))

/-- The distribution mean is feasible and attains the variance benchmark. -/
theorem source_mean_optimal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hb : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, Y ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
    (∫ ω, ((∫ ω, Y ω ∂μ) - Y ω)^2 ∂μ) = variance Y μ ∧
    ∀ u : ℝ, variance Y μ ≤ ∫ ω, (u - Y ω)^2 ∂μ := by
  have hL : MemLp Y 2 μ := memLp_of_bounded
    (Filter.Eventually.of_forall hb) hY.aestronglyMeasurable 2
  have hI := hL.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  refine ⟨⟨integral_nonneg (fun ω => (hb ω).1), ?_⟩, ?_, ?_⟩
  · have h := integral_mono hI (integrable_const (1 : ℝ)) (fun ω => (hb ω).2)
    simpa using h
  · simpa using expected_square_decomposition μ Y hL (∫ ω, Y ω ∂μ)
  · intro u
    rw [expected_square_decomposition μ Y hL u]
    exact le_add_of_nonneg_right (sq_nonneg _)

end BanditRL.OnlineLearning
