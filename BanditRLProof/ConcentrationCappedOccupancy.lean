import BanditRLProof.ConcentrationGaussianOccupancy

noncomputable section
open MeasureTheory Real Set Filter
namespace BanditRLProof.Concentration

def cappedOccupancyTail (a ε t : ℝ) : ℝ :=
  if t ≤ 2*a/ε^2 then 1 else occupancyTail a ε t

theorem cappedOccupancyTail_nonneg (a ε t : ℝ) : 0 ≤ cappedOccupancyTail a ε t := by
  unfold cappedOccupancyTail occupancyTail
  split_ifs <;> positivity

theorem cappedOccupancyTail_antitone (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    Antitone (cappedOccupancyTail a ε) := by
  intro x y hxy
  by_cases hx : x ≤ 2*a/ε^2
  · by_cases hy : y ≤ 2*a/ε^2
    · simp [cappedOccupancyTail, hx, hy]
    · simp only [cappedOccupancyTail, hx, hy, if_true, if_false]
      unfold occupancyTail
      apply exp_le_one_iff.mpr
      nlinarith [sq_nonneg (ε*sqrt y-sqrt (2*a))]
  · have hy : ¬y ≤ 2*a/ε^2 := fun h => hx (hxy.trans h)
    simp only [cappedOccupancyTail, hx, hy, if_false]
    exact occupancyTail_antitoneOn a ε ha hε (le_of_not_ge hx) (le_of_not_ge hy) hxy

theorem integral_cappedOccupancyTail (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    IntegrableOn (cappedOccupancyTail a ε) (Ioi 0) ∧
      (∫ t in Ioi 0, cappedOccupancyTail a ε t) = (2/ε^2)*(a+sqrt (Real.pi*a)+1) := by
  let u := 2*a/ε^2
  have hu : 0 < u := by dsimp [u]; positivity
  have hs : (fun _ : ℝ => (1 : ℝ)) =ᵐ[volume.restrict (Ioc 0 u)] cappedOccupancyTail a ε := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp [cappedOccupancyTail, show t ≤ 2*a/ε^2 from ht.2]
  have hl : occupancyTail a ε =ᵐ[volume.restrict (Ioi u)] cappedOccupancyTail a ε := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [cappedOccupancyTail, show ¬t ≤ 2*a/ε^2 from not_le.mpr ht]
  have his : IntegrableOn (cappedOccupancyTail a ε) (Ioc 0 u) :=
    (integrableOn_const (C := (1 : ℝ)) (hs := by simp)).congr hs
  have hil : IntegrableOn (cappedOccupancyTail a ε) (Ioi u) :=
    (integrableOn_occupancyTail a ε ha hε).congr hl
  have hi : IntegrableOn (cappedOccupancyTail a ε) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hu.le]
    exact his.union hil
  refine ⟨hi, ?_⟩
  rw [← Ioc_union_Ioi_eq_Ioi hu.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi his hil,
    ← integral_congr_ae hs, ← integral_congr_ae hl, integral_occupancyTail a ε ha hε]
  simp [hu.le]
  dsimp [u]
  ring

theorem sum_le_occupancy_bound_sharp (p : ℕ → ℝ) (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (h1 : ∀ s, p s ≤ 1)
    (htail : ∀ s : ℕ, 2*a/ε^2 < (s : ℝ) → p s ≤ occupancyTail a ε s) (n : ℕ) :
    (∑ i ∈ Finset.range n, p (i+1)) ≤ (2/ε^2)*(a+sqrt (Real.pi*a)+1) := by
  have hi := integral_cappedOccupancyTail a ε ha hε
  have hm := (cappedOccupancyTail_antitone a ε ha hε).antitoneOn (s := Icc 0 (0+(n : ℝ)))
  calc
    _ ≤ ∑ i ∈ Finset.range n, cappedOccupancyTail a ε (0+(i+1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [zero_add, cappedOccupancyTail]
      split_ifs with h
      · exact h1 _
      · exact htail _ (lt_of_not_ge h)
    _ ≤ ∫ t in (0 : ℝ)..0+(n : ℝ), cappedOccupancyTail a ε t := hm.sum_le_integral
    _ = ∫ t in Ioc (0 : ℝ) (0+(n : ℝ)), cappedOccupancyTail a ε t :=
      intervalIntegral.integral_of_le (by positivity)
    _ ≤ ∫ t in Ioi 0, cappedOccupancyTail a ε t :=
      setIntegral_mono_set hi.1 (Eventually.of_forall (cappedOccupancyTail_nonneg a ε))
        (Eventually.of_forall (fun t ht => ht.1))
    _ = _ := hi.2

end BanditRLProof.Concentration
