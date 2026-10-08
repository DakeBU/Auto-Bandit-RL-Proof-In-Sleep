theorem lemma_1_2 {X : Type*} (V : Set X) (loss : ℕ → X → ℝ) (leader : ℕ → X) (T : ℕ) (hmem : ∀ n, 0 < n → n ≤ T → leader n ∈ V) (hmin : ∀ n, 0 < n → n ≤ T → ∀ u ∈ V, (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u) : (∑ t ∈ Finset.range T, loss t (leader (t + 1))) ≤ ∑ t ∈ Finset.range T, loss t (leader T)

theorem expected_square_decomposition {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (u : ℝ) : (∫ ω, (u - Y ω)^2 ∂μ) = variance Y μ + (u - ∫ ω, Y ω ∂μ)^2

theorem independent_prediction_square {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (P Y : Ω → ℝ) (hP : MemLp P 2 μ) (hY : MemLp Y 2 μ) (h : IndepFun P Y μ) : (∫ ω, (P ω - Y ω)^2 ∂μ) = (∫ ω, (P ω - ∫ ω, Y ω ∂μ)^2 ∂μ) + variance Y μ

theorem meanPredict_independent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ) : IndepFun (fun ω => meanPredict (fun i => Y i ω) t) (Y t) μ

theorem meanPredict_measurable {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (t : ℕ) : Measurable (fun ω => meanPredict (fun i => Y i ω) t)

theorem meanPredict_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) : MemLp (fun ω => meanPredict (fun i => Y i ω) t) 2 μ

theorem iid_meanPredict_excess {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) : (∫ ω, ∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) - T * variance (Y 0) μ = ∑ t ∈ Finset.range T, ∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ

theorem iid_meanPredict_excess_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) : 0 ≤ (∫ ω, ∑ t ∈ Finset.range T, (meanPredict (fun i => Y i ω) t - Y t ω)^2 ∂μ) - T * variance (Y 0) μ

theorem source_mean_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y) (hb : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1) : (∫ ω, Y ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧ (∫ ω, ((∫ ω, Y ω ∂μ) - Y ω)^2 ∂μ) = variance Y μ ∧ ∀ u : ℝ, variance Y μ ≤ ∫ ω, (u - Y ω)^2 ∂μ

theorem history_policy_independent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ) (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy) : IndepFun (fun ω => policy (fun i => Y i ω)) (Y t) μ

theorem history_policy_loss_ge_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (hb : ∀ t ω, Y t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) (policy : ((↑(Finset.range t) : Type) → ℝ) → ℝ) (hp : Measurable policy) (hpb : ∀ z, policy z ∈ Set.Icc (0 : ℝ) 1) : variance (Y t) μ ≤ ∫ ω, (policy (fun i => Y i ω) - Y t ω)^2 ∂μ

theorem normalized_excess (total variance : ℝ) (T : ℕ) (hT : 0 < T) : total / T - variance = (total - T * variance) / T
