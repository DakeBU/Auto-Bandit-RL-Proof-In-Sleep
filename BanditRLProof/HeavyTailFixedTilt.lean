import BanditRLProof.HeavyTailTruncation
import BanditRLProof.Exp3ComparatorBernstein

/-! A reusable bounded, centered, second-moment MGF producer. The existing
EXP3 exponential-remainder leaf is genuinely reused for a new probability law.
This is not yet the independent-sum or adaptive-policy concentration theorem. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

theorem bounded_centered_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (b v tilt : ℝ) (hXm : Measurable X) (hb : ∀ ω, |X ω| ≤ b)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    (hv : (∫ ω, (X ω)^2 ∂μ) ≤ v)
    (hsmall : |tilt| * b ≤ 1) :
    Concentration.HasMGFUpperBoundAt X tilt (tilt^2 * v) μ := by
  have hX : Integrable X μ := (integrable_const b).mono' hXm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb ω)
  have hsq : Integrable (fun ω => (X ω)^2) μ := by
    apply (integrable_const (b^2)).mono' (hXm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs, abs_sq]
      nlinarith [sq_nonneg (b - |X ω|), sq_abs (X ω), hb ω, abs_nonneg (X ω)]
  have hexp (s : ℝ) : Integrable (fun ω => Real.exp (s * X ω)) μ := by
    apply (integrable_const (Real.exp (|s| * b))).mono'
      (hXm.const_mul s).exp.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        s * X ω ≤ |s * X ω| := le_abs_self _
        _ = |s| * |X ω| := abs_mul _ _
        _ ≤ |s| * b := mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg _)
  refine ⟨hexp, ?_⟩
  change (∫ ω, Real.exp (tilt * X ω) ∂μ) ≤ Real.exp (tilt^2 * v)
  calc
    (∫ ω, Real.exp (tilt * X ω) ∂μ) ≤
        ∫ ω, (1 + tilt * X ω) + tilt^2 * (X ω)^2 ∂μ := by
      apply integral_mono (hexp tilt)
        (((integrable_const 1).add (hX.const_mul tilt)).add (hsq.const_mul _))
      intro ω
      have h := Concentration.exp_le_one_add_self_add_sq_of_abs_le_one
        (x := tilt * X ω) (by rw [abs_mul]; exact
          (mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg _)).trans hsmall)
      simpa only [Pi.add_apply, mul_pow] using h
    _ = 1 + tilt^2 * (∫ ω, (X ω)^2 ∂μ) := by
      rw [integral_add (f := fun ω => 1 + tilt * X ω)
        (g := fun ω => tilt^2 * (X ω)^2)
        ((integrable_const 1).add (hX.const_mul tilt)) (hsq.const_mul _),
        integral_add (f := fun _ : Ω => (1 : ℝ)) (g := fun ω => tilt * X ω)
        (integrable_const 1) (hX.const_mul tilt)]
      simp [integral_const_mul, hmean]
    _ ≤ 1 + tilt^2 * v := by gcongr
    _ ≤ Real.exp (tilt^2 * v) := by linarith [Real.add_one_le_exp (tilt^2 * v)]

/-- Shared centering producer for bounded transformed rewards. Both hard
truncation and clipping supply their own second-moment proofs to this interface. -/
theorem bounded_centering_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (B v tilt : ℝ) (hYm : Measurable Y) (hbound : ∀ ω, |Y ω| ≤ B)
    (hv : (∫ ω, (Y ω)^2 ∂μ) ≤ v)
    (hsmall : |tilt| * (2 * B) ≤ 1) :
    Concentration.HasMGFUpperBoundAt
      (fun ω => Y ω - ∫ ω, Y ω ∂μ) tilt (tilt^2 * v) μ := by
  have hYi : Integrable Y μ := (integrable_const B).mono' hYm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hbound ω)
  have hmeanB : |∫ ω, Y ω ∂μ| ≤ B := by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := Y)
      (C := B) (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hbound ω)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  apply bounded_centered_mgf μ _ (2 * B) v tilt
    (hYm.sub measurable_const) _ _ _ hsmall
  · intro ω
    calc
      |Y ω - ∫ ω, Y ω ∂μ| ≤ |Y ω| + |∫ ω, Y ω ∂μ| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hbound ω]
  · rw [integral_sub hYi (integrable_const _)]
    simp
  · rw [← ProbabilityTheory.variance_eq_integral hYm.aemeasurable]
    exact (ProbabilityTheory.variance_le_expectation_sq hYm.aestronglyMeasurable).trans
      hv

/-- Moment assumptions produce a centered truncated MGF at every admissible
tilt. Signed rewards require the factor 2 in the centering range. -/
theorem truncated_centered_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (B ε u tilt : ℝ) (hXm : Measurable X) (hB : 0 < B) (hε : ε ≤ 1)
    (hm : Integrable (fun ω => |X ω| ^ (1 + ε)) μ)
    (hu : (∫ ω, |X ω| ^ (1 + ε) ∂μ) ≤ u)
    (hsmall : |tilt| * (2 * B) ≤ 1) :
    Concentration.HasMGFUpperBoundAt
      (fun ω => truncate B (X ω) - ∫ ω, truncate B (X ω) ∂μ)
      tilt (tilt^2 * (u * B^(1-ε))) μ :=
  bounded_centering_mgf μ _ B _ tilt ((measurable_truncate B).comp hXm)
    (fun ω => abs_truncate_le B (X ω) hB.le)
    (integral_sq_truncate_le μ X B ε u hB hε hXm hm hu) hsmall

/-- Independent composition preserves the individual admissible tilt, instead
of imposing a range bound on the whole sum. -/
theorem independent_sum_mgf {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (s : Finset ι) (tilt : ℝ) (budget : ι → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (h : ∀ i ∈ s, Concentration.HasMGFUpperBoundAt (X i) tilt (budget i) μ) :
    Concentration.HasMGFUpperBoundAt (∑ i ∈ s, X i) tilt (∑ i ∈ s, budget i) μ := by
  classical
  constructor
  · intro t
    exact hi.integrable_exp_mul_sum hm (fun i his => (h i his).integrable_exp_mul t)
  · rw [hi.mgf_sum hm s, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
      (fun i his => (h i his).mgf_le)

/-- Fixed-prefix one-sided concentration from independent raw-moment data.
This is an actual tail producer, before bias assembly and adaptive-count peeling. -/
theorem truncated_sum_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (B : ℕ → ℝ) (ε u tilt r : ℝ) (n : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hB : ∀ i, 0 < B i) (hε : ε ≤ 1)
    (hm : ∀ i, Integrable (fun ω => |X i ω| ^ (1 + ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω| ^ (1 + ε) ∂μ) ≤ u)
    (ht : 0 ≤ tilt) (hsmall : ∀ i ∈ Finset.range n, |tilt| * (2 * B i) ≤ 1) :
    μ.real {ω | r ≤ ∑ i ∈ Finset.range n,
      (truncate (B i) (X i ω) - ∫ ω, truncate (B i) (X i ω) ∂μ)} ≤
      Real.exp (-tilt * r +
        ∑ i ∈ Finset.range n, tilt^2 * (u * (B i)^(1-ε))) := by
  let Y := fun i ω => truncate (B i) (X i ω) - ∫ ω, truncate (B i) (X i ω) ∂μ
  have hYi : iIndepFun Y μ := hi.comp
    (fun i x => truncate (B i) x - ∫ ω, truncate (B i) (X i ω) ∂μ)
    (fun i => (measurable_truncate (B i)).sub measurable_const)
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    ((measurable_truncate (B i)).comp (hXm i)).sub measurable_const
  have hmgf := independent_sum_mgf μ Y (Finset.range n) tilt
    (fun i => tilt^2 * (u * (B i)^(1-ε))) hYi hYm
    (fun i his => truncated_centered_mgf μ (X i) (B i) ε u tilt
      (hXm i) (hB i) hε (hm i) (hu i) (hsmall i his))
  simpa only [Y, Finset.sum_apply] using hmgf.measure_ge_le_exp_add r ht

end BanditRLProof.HeavyTail
