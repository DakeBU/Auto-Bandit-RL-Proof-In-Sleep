import BanditRLProof.ConcentrationGaussianOccupancy
import BanditRLProof.ConcentrationMartingaleMaximal

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
namespace BanditRLProof.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def fixedRadiusMeanEvent (X : ℕ → Ω → ℝ) (a ε : ℝ) (s : ℕ) : Set Ω :=
  {ω | ε ≤ (∑ j ∈ range s, X (j+1) ω)/(s : ℝ)+sqrt (2*a/(s : ℝ))}

theorem measure_fixedRadiusMeanEvent_le (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (s : ℕ) (hs : 2*a/ε^2 < (s : ℝ)) :
    μ (fixedRadiusMeanEvent X a ε s) ≤ ENNReal.ofReal (occupancyTail a ε s) := by
  have hsR : 0 < (s : ℝ) := (by positivity : 0 < 2*a/ε^2).trans hs
  have hsN : 0 < s := Nat.cast_pos.mp hsR
  have hsq := sq_sqrt hsR.le
  have haSq := sq_sqrt (by positivity : 0 ≤ 2*a)
  have hlarge : 2*a < (s : ℝ)*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hs
  have hpos : 0 < ε*sqrt (s : ℝ)-sqrt (2*a) := by
    have he : (ε*sqrt (s : ℝ))^2 = ε^2*(s : ℝ) := by rw [mul_pow, hsq]
    nlinarith [mul_pos hε (sqrt_pos.mpr hsR), sqrt_nonneg (2*a)]
  let A := sqrt (s : ℝ)*(ε*sqrt (s : ℝ)-sqrt (2*a))
  have hA : 0 < A := mul_pos (sqrt_pos.mpr hsR) hpos
  have hr : (s : ℝ)*sqrt (2*a/(s : ℝ)) = sqrt (s : ℝ)*sqrt (2*a) := by
    rw [sqrt_div (by positivity), div_eq_mul_inv]
    field_simp
    nlinarith
  have hbound := measure_exists_le_independent_partialSum_ge_le_subgaussian
    X hXm hind hmean 1 (by norm_num) hsubG s hsN A hA
  have hevent : fixedRadiusMeanEvent X a ε s ⊆
      {ω | ∃ i, i ≤ s ∧ A ≤ ∑ j ∈ range i, X (j+1) ω} := by
    intro ω hω
    refine ⟨s, le_rfl, ?_⟩
    have h := mul_le_mul_of_nonneg_left hω hsR.le
    change (s : ℝ)*ε ≤ (s : ℝ)*((∑ j ∈ range s, X (j+1) ω)/(s : ℝ)+sqrt (2*a/(s : ℝ))) at h
    rw [mul_add, mul_div_cancel₀ _ hsR.ne', hr] at h
    dsimp [A]
    nlinarith
  apply (measure_mono hevent).trans
  convert hbound using 1
  unfold occupancyTail
  congr 2
  dsimp [A]
  rw [mul_pow, hsq]
  field_simp

theorem sum_measureReal_fixedRadiusMeanEvent_le (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (n : ℕ) :
    (∑ i ∈ range n, μ.real (fixedRadiusMeanEvent X a ε (i+1))) ≤
      1+(2/ε^2)*(a+sqrt (Real.pi*a)+1) := by
  apply sum_le_occupancy_bound _ a ε ha hε (fun _ => measureReal_le_one) _ n
  intro s hs
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (measure_fixedRadiusMeanEvent_le X hXm hind hmean hsubG a ε ha hε s hs)
  have hn : 0 ≤ occupancyTail a ε s := (exp_pos _).le
  simpa only [ENNReal.toReal_ofReal hn] using h

theorem measurableSet_fixedRadiusMeanEvent (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (a ε : ℝ) (s : ℕ) :
    MeasurableSet (fixedRadiusMeanEvent X a ε s) := by
  have hm : StronglyMeasurable (fun ω => ∑ j ∈ range s, X (j+1) ω) := by
    convert Finset.stronglyMeasurable_sum (range s) (fun i _ => hXm (i+1)) using 1
    ext ω; simp
  exact measurableSet_le measurable_const ((hm.measurable.div_const _).add_const _)

def fixedRadiusCount (X : ℕ → Ω → ℝ) (a ε : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, (fixedRadiusMeanEvent X a ε (i+1)).indicator (fun _ => (1 : ℝ)) ω

theorem integrable_fixedRadiusCount (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (a ε : ℝ) (n : ℕ) :
    Integrable (fixedRadiusCount X a ε n) μ := by
  exact integrable_finset_sum _ (fun i _ => (integrable_const (1 : ℝ)).indicator
    (measurableSet_fixedRadiusMeanEvent X hXm a ε (i+1)))

/-- Source Lemma 8.2 expected-count conclusion for centered unit-subgaussian coordinates. -/
theorem integral_fixedRadiusCount_le (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (n : ℕ) :
    (∫ ω, fixedRadiusCount X a ε n ω ∂μ) ≤
      1+(2/ε^2)*(a+sqrt (Real.pi*a)+1) := by
  unfold fixedRadiusCount
  rw [integral_finset_sum _ (fun i _ => (integrable_const (1 : ℝ)).indicator
    (measurableSet_fixedRadiusMeanEvent X hXm a ε (i+1)))]
  have he : (∑ i ∈ range n, ∫ ω, (fixedRadiusMeanEvent X a ε (i+1)).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      ∑ i ∈ range n, μ.real (fixedRadiusMeanEvent X a ε (i+1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator (measurableSet_fixedRadiusMeanEvent X hXm a ε (i+1))]
    simp
  rw [he]
  exact sum_measureReal_fixedRadiusMeanEvent_le X hXm hind hmean hsubG a ε ha hε n

end BanditRLProof.Concentration
