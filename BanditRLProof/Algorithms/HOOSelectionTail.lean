import BanditRLProof.Algorithms.HOOIndexConfidence
import BanditRLProof.Algorithms.HOOPathComparison

/-! Selection of a sufficiently visited poor region forces a confidence failure
for that region or for a finite prefix of a supremum-optimal branch. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory

theorem RegularCovering.poor_region_selection_tail {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best : ℝ) (hmean : ∀ x, (∫ y, y ∂law x) = f x)
    (hf : ∀ x, f x ≤ best) (hbest : regionSup f Set.univ = best)
    (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (hv : C.nu1*C.rho^v.length < best-regionSup f (C.region v)) (n : ℕ) :
    (trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) {Y |
      8*Real.log (max (n:ℝ) 2)/(best-regionSup f (C.region v)-C.nu1*C.rho^v.length)^2 ≤
        (visits (history C.nu1 C.rho Y n) v : ℝ) ∧
      v <+: action C.nu1 C.rho Y n} ≤
      ((n:ENNReal)+2) * ((n:ENNReal) * ENNReal.ofReal (Real.exp (-4*Real.log (max (n:ℝ) 2)))) := by
  let μ := trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)
  let q : ENNReal := (n:ENNReal) * ENNReal.ofReal (Real.exp (-4*Real.log (max (n:ℝ) 2)))
  let bad : Set (ℕ → ℝ) := {Y |
    8*Real.log (max (n:ℝ) 2)/(best-regionSup f (C.region v)-C.nu1*C.rho^v.length)^2 ≤
      (visits (history C.nu1 C.rho Y n) v : ℝ) ∧
    (best : WithTop ℝ) ≤ upper C.nu1 C.rho (history C.nu1 C.rho Y n) v}
  let branchBad : ℕ → Set (ℕ → ℝ) := fun j => {Y |
    upper C.nu1 C.rho (history C.nu1 C.rho Y n) (C.toCovering.optimalPath f j) ≤ (best : WithTop ℝ)}
  have hs : {Y : ℕ → ℝ |
      8*Real.log (max (n:ℝ) 2)/(best-regionSup f (C.region v)-C.nu1*C.rho^v.length)^2 ≤
        (visits (history C.nu1 C.rho Y n) v : ℝ) ∧ v <+: action C.nu1 C.rho Y n}
      ⊆ bad ∪ ⋃ j ∈ Finset.range (n+1), branchBad j := by
    intro Y hY
    by_cases hu : (best : WithTop ℝ) ≤ upper C.nu1 C.rho (history C.nu1 C.rho Y n) v
    · exact Or.inl ⟨hY.1, hu⟩
    · have hL : 0 < Real.log (max (n:ℝ) 2) := Real.log_pos (lt_max_of_lt_right (by norm_num))
      have htR : 0 < (visits (history C.nu1 C.rho Y n) v : ℝ) :=
        lt_of_lt_of_le (div_pos (mul_pos (by norm_num) hL) (sq_pos_of_pos (sub_pos.mpr hv))) hY.1
      have ht : 0 < visits (history C.nu1 C.rho Y n) v := by exact_mod_cast htR
      obtain ⟨j, hj, hjU⟩ := C.toCovering.history_selected_underestimate f C.nu1 C.rho best Y n v
        (visits_pos_mem_expanded _ _ _ _ _ ht) hY.2 (lt_of_not_ge hu)
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr (by omega), hjU.le⟩⟩)
  have hb : μ bad ≤ q := C.poor_upper_overestimate_probability law f best hmean hf hbound v hv n
  have hbranch (j : ℕ) : μ (branchBad j) ≤ q := by
    apply C.optimal_upper_underestimate_probability law f best hmean hw hbound
    exact (C.toCovering.optimalPath_sup f best hf j).trans hbest
  calc
    _ ≤ μ (bad ∪ ⋃ j ∈ Finset.range (n+1), branchBad j) := measure_mono hs
    _ ≤ μ bad + μ (⋃ j ∈ Finset.range (n+1), branchBad j) := measure_union_le _ _
    _ ≤ q + ∑ j ∈ Finset.range (n+1), μ (branchBad j) :=
      add_le_add hb (ProbabilityUnionBound.measure_biUnion_finset_le _ _ _)
    _ ≤ q + ∑ _j ∈ Finset.range (n+1), q :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hbranch j))
    _ = ((n:ENNReal)+2)*q := by simp [nsmul_eq_mul]; ring

end BanditRLProof.HOO
