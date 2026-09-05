import BanditRLProof.Algorithms.MOSSStreamMeasurable

noncomputable section
open Real Finset MeasureTheory ProbabilityTheory
namespace BanditRLProof.MOSS

/-- Theorem 9.1's exact constant for the concrete centered reward-table execution.
Identification with the common bandit history law is a separate theorem. -/
theorem integral_streamTrace_regret_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k)
    (n : ℕ) (hkn : k ≤ n) (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ)
    (best : Fin k) (hbest : ∀ a, mean a ≤ mean best)
    (hXm : ∀ a i, StronglyMeasurable (X a i))
    (hind : ∀ a, iIndepFun (X a) μ)
    (hmean : ∀ a i, ∫ ω, X a i ω ∂μ = 0)
    (hsubG : ∀ a i, HasSubgaussianMGF (X a i) 1 μ) :
    (∫ ω, realMeanRegret mean (streamTrace hk n mean X ω) n ∂μ) ≤
      39*sqrt ((n : ℝ)*k) + ∑ a, (mean best-mean a) := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  let δ : ℝ := (k : ℝ)/(n : ℝ)
  have hδ : 0 < δ := div_pos hkR hnR
  let Z := optimismDeficit (X best) δ n
  let f : Fin k → Ω → ℝ := fun a ω => if 8*sqrt δ ≤ mean best-mean a then
    (mean best-mean a)*(1+indexExceedanceCount (streamMean (X a) ω) δ (mean best-mean a) n) else 0
  have hi (a : Fin k) : Integrable (f a) μ := by
    dsimp [f]
    split_ifs
    · exact ((integrable_const 1).add (integrable_indexExceedanceCount (X a) (hXm a) δ _ n)).const_mul _
    · exact integrable_const 0
  have hsum : Integrable (fun ω => ∑ a, f a ω) μ := integrable_finset_sum _ (fun a _ => hi a)
  have hZ : Integrable Z μ := integrable_optimismDeficit (X best)
    (fun i => (hsubG best i).integrable) δ n
  have hbase : Integrable (fun ω => (8*sqrt δ+2*Z ω)*(n : ℝ)) μ :=
    ((integrable_const _).add (hZ.const_mul 2)).mul_const _
  have hb := integral_mono (integrable_streamTrace_regret μ hk n mean X hXm)
    (hbase.add hsum) (fun ω => streamTrace_realMeanRegret_le hk n hkn mean X ω best hbest)
  simp only [Pi.add_apply] at hb
  rw [integral_add hbase hsum, integral_mul_const] at hb
  rw [integral_add (integrable_const _) (hZ.const_mul 2), integral_const_mul] at hb
  simp only [integral_const, probReal_univ, one_smul] at hb
  rw [integral_const_mul] at hb
  have hf := integral_largeGapCountSum_le μ mean X best hbest hXm hind hmean hsubG δ hδ n
  have hz := twice_horizon_mul_integral_optimismDeficit_le (X best) (hXm best)
    (hind best) (hmean best) (hsubG best) n k hn hk
  have he : (n : ℝ)*sqrt δ = sqrt ((n : ℝ)*k) := by
    calc
      _ = sqrt ((n : ℝ)^2)*sqrt δ := by rw [sqrt_sq hnR.le]
      _ = sqrt ((n : ℝ)^2*δ) := (sqrt_mul (sq_nonneg _) _).symm
      _ = _ := by congr 1; dsimp [δ]; field_simp
  have he' : (k : ℝ)/sqrt δ = sqrt ((n : ℝ)*k) := by
    apply (div_eq_iff (ne_of_gt (sqrt_pos.mpr hδ))).mpr
    rw [← he, mul_assoc, ← sq, sq_sqrt hδ.le]
    dsimp [δ]
    field_simp
  have hscale : (k : ℝ)*(15/sqrt δ) = 15*sqrt ((n : ℝ)*k) := by
    calc
      _ = 15*((k : ℝ)/sqrt δ) := by ring
      _ = _ := by rw [he']
  change (∫ ω, ∑ a, f a ω ∂μ) ≤ _ at hf
  change 2*(n : ℝ)*(∫ ω, Z ω ∂μ) ≤ _ at hz
  rw [hscale] at hf
  nlinarith

end BanditRLProof.MOSS
