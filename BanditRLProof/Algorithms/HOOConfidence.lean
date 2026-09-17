import BanditRLProof.Algorithms.HOOConcentration
import BanditRLProof.ProbabilityUnionBound

/-! Finite visit-count peeling for HOO. The time parameter is the number of
already observed chronological rewards; the bound applies to the next decision. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory

noncomputable def regionDeviation (ν ρ : ℝ) (law : Kernel Node ℝ) (v : Node)
    (n : ℕ) (lower : Bool) (Y : ℕ → ℝ) : ℝ :=
  if lower then -(∑ i ∈ Finset.range n, regionNoise ν ρ law v i Y)
  else ∑ i ∈ Finset.range n, regionNoise ν ρ law v i Y

theorem visits_history_le (ν ρ : ℝ) (v : Node) (n : ℕ) (Y : ℕ → ℝ) :
    visits (history ν ρ Y n) v ≤ n := by
  simpa only [history_length] using
    (List.countP_le_length (l := history ν ρ Y n) (p := fun p => decide (v <+: p.1)))

theorem region_deviation_slice (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n k : ℕ) (lower : Bool) (L : ℝ) (hL : 0 ≤ L) (hk : 0 < k) :
    (trajectory ν ρ law) {Y |
      Real.sqrt (2 * (k : ℝ) * L) ≤ regionDeviation ν ρ law v n lower Y ∧
      (visits (history ν ρ Y n) v : ℝ) ≤ k} ≤ ENNReal.ofReal (Real.exp (-4*L)) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have he : -2 * (Real.sqrt (2 * (k : ℝ) * L))^2 / k = -4*L := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    ring
  cases lower with
  | false =>
    simpa only [regionDeviation, Bool.false_eq_true, if_false, he] using
      region_noise_visits_tail ν ρ law hbound v n (Real.sqrt (2*(k:ℝ)*L)) k
        (Real.sqrt_nonneg _) hkR
  | true =>
    simpa only [regionDeviation, if_true, he] using
      region_negative_noise_visits_tail ν ρ law hbound v n (Real.sqrt (2*(k:ℝ)*L)) k
        (Real.sqrt_nonneg _) hkR

/-- One-sided confidence for the empirical regional noise, with its actual
random visit count. The Boolean selects the upper or lower deviation. -/
theorem region_deviation_confidence (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (n : ℕ) (lower : Bool) (L : ℝ) (hL : 0 ≤ L) :
    (trajectory ν ρ law) {Y | 0 < visits (history ν ρ Y n) v ∧
      Real.sqrt (2 * (visits (history ν ρ Y n) v : ℝ) * L) ≤
        regionDeviation ν ρ law v n lower Y} ≤
      (n : ENNReal) * ENNReal.ofReal (Real.exp (-4*L)) := by
  let E : ℕ → Set (ℕ → ℝ) := fun k => {Y |
    Real.sqrt (2*(k:ℝ)*L) ≤ regionDeviation ν ρ law v n lower Y ∧
      (visits (history ν ρ Y n) v : ℝ) ≤ k}
  have hs : {Y : ℕ → ℝ | 0 < visits (history ν ρ Y n) v ∧
      Real.sqrt (2*(visits (history ν ρ Y n) v : ℝ)*L) ≤ regionDeviation ν ρ law v n lower Y}
      ⊆ ⋃ k ∈ Finset.Icc 1 n, E k := by
    intro Y hY
    apply Set.mem_iUnion.mpr ⟨visits (history ν ρ Y n) v, ?_⟩
    apply Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hY.1, visits_history_le ν ρ v n Y⟩, ?_⟩
    exact ⟨hY.2, le_rfl⟩
  calc
    _ ≤ (trajectory ν ρ law) (⋃ k ∈ Finset.Icc 1 n, E k) := measure_mono hs
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (trajectory ν ρ law) (E k) :=
      ProbabilityUnionBound.measure_biUnion_finset_le _ _ E
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, ENNReal.ofReal (Real.exp (-4*L)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact region_deviation_slice ν ρ law hbound v n k lower L hL (Finset.mem_Icc.mp hk).1
    _ = _ := by simp [nsmul_eq_mul]

end BanditRLProof.HOO
