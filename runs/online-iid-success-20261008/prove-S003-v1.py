from leaf_tools_v2 import *
description='Actual unknown-law initial-half strictpast meanPredict expected-fixed upper from source pathwise Theorem1.3; independence not assumed.'
body='''  let prediction := fun t ω => meanPredict (fun i => Y i ω) t
  let m := ∫ ω, Y 0 ω ∂μ
  have hall : ∀ᵐ ω ∂μ, ∀ t, Y t ω ∈ Set.Icc (0 : ℝ) 1 := ae_all_iff.2 hb
  have hL (t : ℕ) : MemLp (Y t) 2 μ :=
    memLp_of_bounded (hb t) (hY t).aestronglyMeasurable 2
  have hP (t : ℕ) : MemLp (prediction t) 2 μ := by
    apply memLp_of_bounded (a := 0) (b := 1) _
      (meanPredict_measurable Y hY t).aestronglyMeasurable
    filter_upwards [hall] with ω hω
    exact meanPredict_mem (fun i => Y i ω) t (fun i _ => hω i)
  have hPI : Integrable (fun ω => ∑ t ∈ Finset.range T,
      (prediction t ω - Y t ω)^2) μ :=
    integrable_finset_sum (Finset.range T)
      (fun t _ => ((hP t).sub (hL t)).integrable_sq)
  have hCI : Integrable (fun ω => ∑ t ∈ Finset.range T, (m - Y t ω)^2) μ :=
    integrable_finset_sum (Finset.range T)
      (fun t _ => ((memLp_const m).sub (hL t)).integrable_sq)
  have hpath : ∀ᵐ ω ∂μ,
      (∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2) -
        (∑ t ∈ Finset.range T, (m - Y t ω)^2) ≤ 4 + 4 * Real.log T := by
    filter_upwards [hall] with ω hω
    have hmain := theorem_1_3 (fun i => Y i ω) T hT (fun i _ => hω i)
    have hmin := empiricalMean_minimizes (fun i => Y i ω) T hT m
    change (∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2) -
      (∑ t ∈ Finset.range T, (m - Y t ω)^2) ≤ _
    linarith
  have hi := integral_mono_ae (hPI.sub hCI)
    (integrable_const (4 + 4 * Real.log (T : ℝ))) hpath
  rw [integral_sub hPI hCI] at hi
  have hc : (∫ ω, ∑ t ∈ Finset.range T, (m - Y t ω)^2 ∂μ) =
      (T : ℝ) * variance (Y 0) μ := by
    simpa only [m, sub_self, sq_zero, mul_zero, add_zero] using
      expected_fixed_prefix_decomposition μ Y hY hlaw hb T m
  rw [hc] at hi
  unfold expectedFixedRegret
  rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
  simpa [prediction] using hi
'''
row=start_leaf(2,body,description)
gate('S003-focused-build-v1','lake','build','BanditRLProof.OnlineGuessingIIDSuccess')
finish_leaf(2,'v1',description)
