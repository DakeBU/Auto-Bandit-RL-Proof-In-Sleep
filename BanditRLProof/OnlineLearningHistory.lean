import BanditRLProof.OnlineLearningIID

open MeasureTheory ProbabilityTheory

namespace BanditRL.OnlineLearning

/-- A policy consumes only the finite strict-past tuple; no full-sequence algorithm argument. -/
theorem history_policy_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ)
    (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy) :
    IndepFun (fun ω => policy (fun i => Y i ω)) (Y t) μ := by
  have hdis : Disjoint (Finset.range t) {t} := by simp
  have hi := iIndepFun.indepFun_finset (Finset.range t) {t} hdis hind hY
  have hc := hi.comp hp (measurable_pi_apply (⟨t, by simp⟩ : (↑({t} : Finset ℕ) : Type)))
  simpa [Function.comp_def] using hc

/-- No bounded measurable history policy beats the variance benchmark in expectation. -/
theorem history_policy_loss_ge_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ)
    (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy)
    (hpb : ∀ z, policy z ∈ Set.Icc (0 : ℝ) 1) :
    variance (Y t) μ ≤ ∫ ω, (policy (fun i => Y i ω) - Y t ω)^2 ∂μ := by
  have hmeas : Measurable (fun ω => policy (fun i => Y i ω)) :=
    hp.comp (measurable_pi_lambda _ (fun i => hY i))
  have hP : MemLp (fun ω => policy (fun i => Y i ω)) 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall (fun ω => hpb _)) hmeas.aestronglyMeasurable 2
  have hL : MemLp (Y t) 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall (hb t)) (hY t).aestronglyMeasurable 2
  rw [independent_prediction_square μ _ _ hP hL (history_policy_independent μ Y hY hind t policy hp)]
  have hnon : 0 ≤ ∫ ω, (policy (fun i => Y i ω) - ∫ ω, Y t ω ∂μ)^2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  linarith

/-- Equations (1.1) and (1.2) differ exactly by normalization for positive horizon. -/
theorem normalized_excess (total variance : ℝ) (T : ℕ) (hT : 0 < T) :
    total / T - variance = (total - T * variance) / T := by
  have h : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  field_simp
  <;> ring

end BanditRL.OnlineLearning
