```lean
import Mathlib.Tactic


namespace BanditRLProof.ConfidenceIntervals


theorem bias_statistical_composition {μ ν estimate b s : ℝ}
    (hb : |ν - μ| ≤ b) (hs : |estimate - ν| ≤ s) :
    |estimate - μ| ≤ b + s := by
  calc
    _ = |(estimate - ν) + (ν - μ)| := by congr 1; ring
    _ ≤ |estimate - ν| + |ν - μ| := abs_add_le _ _
    _ ≤ b + s := by linarith


noncomputable def survivors {K : ℕ} (active : Finset (Fin K))
    (estimate radius : Fin K → ℝ) : Finset (Fin K) :=
  active.filter fun i => ∀ j ∈ active, estimate j - radius j ≤ estimate i + radius i

theorem optimal_survives {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star : Fin K) (hstar : star ∈ active)
    (hopt : ∀ i ∈ active, μ i ≤ μ star)
    (hconf : ∀ i ∈ active, |estimate i - μ i| ≤ radius i) :
    star ∈ survivors active estimate radius := by
  classical
  simp only [survivors, Finset.mem_filter]
  refine ⟨hstar, fun i hi => ?_⟩
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hi)).2
  linarith [hopt i hi]

theorem large_gap_removed {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star i : Fin K) (hstar : star ∈ active)
    {r : ℝ} (hwidth : ∀ j ∈ active, radius j ≤ r)
    (hconf : ∀ j ∈ active, |estimate j - μ j| ≤ radius j)
    (hgap : 4 * r < μ star - μ i) :
    i ∉ survivors active estimate radius := by
  classical
  intro hi
  obtain ⟨hia, hkeep⟩ := Finset.mem_filter.mp hi
  have hcmp := hkeep star hstar
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hia)).2
  linarith [hwidth star hstar, hwidth i hia]

end BanditRLProof.ConfidenceIntervals
```
