import BanditRLProof.Algorithms.MOSSPeeling
import Mathlib.MeasureTheory.Integral.Layercake

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
namespace BanditRLProof.MOSS
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def centeredIndex (X : ℕ → Ω → ℝ) (δ : ℝ) (s : ℕ) (ω : Ω) : ℝ :=
  peelingSum X s ω / (s : ℝ) + sqrt (4 / (s : ℝ) * logPlus (1 / ((s : ℝ)*δ)))

/-- Positive part of the worst centered index through sample count n. -/
def optimismDeficit (X : ℕ → Ω → ℝ) (δ : ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => max (optimismDeficit X δ n ω) (-centeredIndex X δ (n+1) ω)

theorem optimismDeficit_nonneg (X : ℕ → Ω → ℝ) (δ : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ optimismDeficit X δ n ω := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem le_optimismDeficit_iff (X : ℕ → Ω → ℝ) (δ gap : ℝ) (hg : 0 < gap)
    (n : ℕ) (ω : Ω) : gap ≤ optimismDeficit X δ n ω ↔
      ∃ s : ℕ, 0 < s ∧ s ≤ n ∧ centeredIndex X δ s ω + gap ≤ 0 := by
  induction n with
  | zero => simp [optimismDeficit, not_le.mpr hg]
  | succ n ih =>
    rw [optimismDeficit, le_max_iff, ih]
    constructor
    · rintro (⟨s, hs, hsn, hb⟩ | hb)
      · exact ⟨s, hs, Nat.le_succ_of_le hsn, hb⟩
      · exact ⟨n+1, by omega, le_rfl, by linarith⟩
    · rintro ⟨s, hs, hsn, hb⟩
      by_cases h : s ≤ n
      · exact Or.inl ⟨s, hs, h, hb⟩
      · have heq : s = n+1 := by omega
        subst s
        exact Or.inr (by linarith)

theorem stronglyMeasurable_centeredIndex (X : ℕ → Ω → ℝ)
    (hX : ∀ i, StronglyMeasurable (X i)) (δ : ℝ) (s : ℕ) :
    StronglyMeasurable (centeredIndex X δ s) := by
  unfold centeredIndex peelingSum
  have hsum : StronglyMeasurable (fun ω => ∑ j ∈ range s, X (j+1) ω) := by
    convert (Finset.stronglyMeasurable_sum (range s) (fun i _ => hX (i+1))) using 1
    ext ω
    simp
  exact (hsum.div stronglyMeasurable_const).add stronglyMeasurable_const

theorem integrable_centeredIndex [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) μ) (δ : ℝ) (s : ℕ) :
    Integrable (centeredIndex X δ s) μ := by
  unfold centeredIndex peelingSum
  exact ((integrable_finset_sum _ (fun i _ => hX (i+1))).div_const _).add
    (integrable_const _)

theorem stronglyMeasurable_optimismDeficit (X : ℕ → Ω → ℝ)
    (hX : ∀ i, StronglyMeasurable (X i)) (δ : ℝ) (n : ℕ) :
    StronglyMeasurable (optimismDeficit X δ n) := by
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih => exact ih.sup (stronglyMeasurable_centeredIndex X hX δ (n+1)).neg

theorem integrable_optimismDeficit [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) μ) (δ : ℝ) (n : ℕ) :
    Integrable (optimismDeficit X δ n) μ := by
  induction n with
  | zero => exact integrable_const _
  | succ n ih => exact ih.sup (integrable_centeredIndex X hX δ (n+1)).neg

theorem measure_optimismDeficit_ge_le [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (n : ℕ) :
    μ {ω | gap ≤ optimismDeficit X δ n ω} ≤ ENNReal.ofReal (15*δ/gap^2) := by
  apply (measure_mono (show {ω | gap ≤ optimismDeficit X δ n ω} ⊆
    meanBadEvent X δ gap from ?_)).trans
    (measure_meanBadEvent_le_fifteen X hXm hind hmean hsubG δ gap hδ hg)
  intro ω hω
  obtain ⟨s, hs, _, hb⟩ := (le_optimismDeficit_iff X δ gap hg n ω).mp hω
  exact ⟨s, hs, hb⟩

/-- Layer-cake identity with integrability derived from the coordinate MGF contracts. -/
theorem integral_optimismDeficit_eq_integral_tail [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ : ℝ) (n : ℕ) :
    ∫ ω, optimismDeficit X δ n ω ∂μ =
      ∫ gap in Set.Ioi 0, μ.real {ω | gap ≤ optimismDeficit X δ n ω} :=
  (integrable_optimismDeficit X (fun i => (hsubG i).integrable) δ n).integral_eq_integral_meas_le
    (Filter.Eventually.of_forall (optimismDeficit_nonneg X δ n))

end BanditRLProof.MOSS
