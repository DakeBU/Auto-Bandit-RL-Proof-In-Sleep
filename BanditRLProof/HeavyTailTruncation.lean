import BanditRLProof.Algorithms.UCBArmStreamSource
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Heavy-tail truncation producers

Raw absolute moments; no sub-Gaussian assumption. These are producer leaves,
not a complete robust-UCB regret theorem. Thresholds may depend on sample index
and on the evaluation round (by choosing a different `transform` each round).
-/

namespace BanditRLProof.HeavyTail
open MeasureTheory

noncomputable def truncate (B x : ℝ) : ℝ := if |x| ≤ B then x else 0

theorem abs_truncate_le (B x : ℝ) (hB : 0 ≤ B) : |truncate B x| ≤ B := by
  unfold truncate
  split_ifs with h
  · exact h
  · simpa using hB

theorem measurable_truncate (B : ℝ) : Measurable (truncate B) := by
  exact Measurable.ite (isClosed_le continuous_abs continuous_const).measurableSet
    measurable_id measurable_const

/-- The discarded tail is controlled by a raw (1+epsilon)-moment. -/
theorem abs_sub_truncate_le (B x ε : ℝ) (hB : 0 < B) (hε : 0 ≤ ε) :
    |x - truncate B x| ≤ |x| ^ (1 + ε) / B ^ ε := by
  unfold truncate
  split_ifs with h
  · simpa using div_nonneg (Real.rpow_nonneg (abs_nonneg x) (1 + ε))
      (Real.rpow_nonneg hB.le ε)
  · have hx : 0 < |x| := lt_trans hB (lt_of_not_ge h)
    rw [sub_zero, le_div_iff₀ (Real.rpow_pos_of_pos hB ε),
      Real.rpow_add hx, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hB.le (le_of_lt (lt_of_not_ge h)) hε) (abs_nonneg x)

/-- Truncation supplies the variance-scale envelope needed by Bernstein. -/
theorem sq_truncate_le (B x ε : ℝ) (hB : 0 < B) (hε : ε ≤ 1) :
    (truncate B x) ^ 2 ≤ |x| ^ (1 + ε) * B ^ (1 - ε) := by
  unfold truncate
  split_ifs with h
  · by_cases hx : x = 0
    · subst x
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · have ha : 0 < |x| := abs_pos.mpr hx
      have hr := Real.rpow_le_rpow (abs_nonneg x) h (sub_nonneg.mpr hε)
      have hid : |x| ^ (1 + ε) * |x| ^ (1 - ε) = x ^ 2 := by
        rw [← Real.rpow_add ha]
        convert Real.rpow_two (|x|) using 1 <;> ring_nf
        simp
      rw [← hid]
      exact mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg (abs_nonneg x) _)
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

/-- Integrating the pointwise tail inequality produces an actual bias bound. -/
theorem integral_truncate_bias_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (B ε u : ℝ)
    (hB : 0 < B) (hε : 0 ≤ ε) (hXm : Measurable X) (hX : Integrable X μ)
    (hm : Integrable (fun ω => |X ω| ^ (1 + ε)) μ)
    (hu : (∫ ω, |X ω| ^ (1 + ε) ∂μ) ≤ u) :
    |(∫ ω, X ω ∂μ) - ∫ ω, truncate B (X ω) ∂μ| ≤ u / B ^ ε := by
  have ht : Integrable (fun ω => truncate B (X ω)) μ := by
    have heq : (fun ω => truncate B (X ω)) =
        {ω | |X ω| ≤ B}.indicator X := by
      funext ω; simp [truncate, Set.indicator]
    rw [heq]
    exact hX.indicator (measurableSet_le hXm.abs measurable_const)
  rw [← integral_sub hX ht]
  calc
    |∫ ω, X ω - truncate B (X ω) ∂μ| ≤
        ∫ ω, |X ω - truncate B (X ω)| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun ω => X ω - truncate B (X ω))
    _ ≤ ∫ ω, |X ω| ^ (1 + ε) / B ^ ε ∂μ :=
      integral_mono (hX.sub ht).abs (hm.div_const _) (fun ω =>
        abs_sub_truncate_le B (X ω) ε hB hε)
    _ = (∫ ω, |X ω| ^ (1 + ε) ∂μ) / B ^ ε := integral_div _ _
    _ ≤ u / B ^ ε := div_le_div_of_nonneg_right hu (Real.rpow_nonneg hB.le ε)

/-- The second moment envelope is integrable and bounded by the raw moment. -/
theorem integral_sq_truncate_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (B ε u : ℝ)
    (hB : 0 < B) (hε : ε ≤ 1) (hXm : Measurable X)
    (hm : Integrable (fun ω => |X ω| ^ (1 + ε)) μ)
    (hu : (∫ ω, |X ω| ^ (1 + ε) ∂μ) ≤ u) :
    (∫ ω, (truncate B (X ω)) ^ 2 ∂μ) ≤ u * B ^ (1 - ε) := by
  have hg := hm.mul_const (B ^ (1 - ε))
  have ht : Integrable (fun ω => (truncate B (X ω)) ^ 2) μ := by
    apply hg.mono' (((measurable_truncate B).comp hXm).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, abs_sq] using
        sq_truncate_le B (X ω) ε hB hε
  calc
    (∫ ω, (truncate B (X ω)) ^ 2 ∂μ) ≤
        ∫ ω, |X ω| ^ (1 + ε) * B ^ (1 - ε) ∂μ :=
      integral_mono ht hg (fun ω => sq_truncate_le B (X ω) ε hB hε)
    _ = (∫ ω, |X ω| ^ (1 + ε) ∂μ) * B ^ (1 - ε) := integral_mul_const _ _
    _ ≤ u * B ^ (1 - ε) := mul_le_mul_of_nonneg_right hu (Real.rpow_nonneg hB.le _)

/-- A sample-index transform of actual observations is the same transform of
the consumed latent prefix. No IID claim is made about adaptively selected data. -/
theorem transformed_observed_prefix {Ω : Type*} {K : ℕ}
    (action : Ω → ActionTrace (Fin K)) (stream : Ω → UCB.ArmRewardStream K)
    (transform : ℕ → Fin K → ℝ → ℝ) (ω : Ω) (arm : Fin K) (n : ℕ) :
    sumRewards (action ω)
        (fun t => transform (pullCount (action ω) (action ω t) t) (action ω t)
          (UCB.rewardFromArmStream action stream ω t)) arm n =
      (Finset.range (pullCount (action ω) arm n)).sum
        (fun s => transform s arm (stream ω s arm)) := by
  exact UCB.sumRewards_rewardFromArmStream_eq_armPrefixSum action
    (fun ω s a => transform s a (stream ω s a)) ω arm n

/-- Common estimator assembly: deterministic bias and stochastic fluctuation
remain separate obligations, rather than assuming the desired confidence event. -/
theorem estimator_error_le (estimate center mean bias fluctuation : ℝ)
    (hb : |center - mean| ≤ bias) (hf : |estimate - center| ≤ fluctuation) :
    |estimate - mean| ≤ bias + fluctuation := by
  calc
    |estimate - mean| ≤ |estimate - center| + |center - mean| := abs_sub_le _ _ _
    _ ≤ bias + fluctuation := by linarith

end BanditRLProof.HeavyTail
