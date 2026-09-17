import BanditRLProof.Algorithms.HOOConfidence
import BanditRLProof.HOOModel

/-! Transfer from actual centered regional observations to HOO U indices. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory

theorem regional_means_lower (ν ρ : ℝ) (law : Kernel Node ℝ) (v : Node)
    (m : ℝ) (hm : ∀ a, v <+: a → m ≤ nodeMean law a) (n : ℕ) (Y : ℕ → ℝ) :
    m * (visits (history ν ρ Y n) v : ℝ) ≤
      ∑ i ∈ Finset.range n, regionCount ν ρ v i Y * nodeMean law (action ν ρ Y i) := by
  rw [← sum_regionCount_eq_visits, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hv : v <+: action ν ρ Y i
  · simpa only [regionCount, if_pos hv, mul_one, one_mul] using hm _ hv
  · simp only [regionCount, if_neg hv, mul_zero, zero_mul, le_refl]

theorem regional_means_upper (ν ρ : ℝ) (law : Kernel Node ℝ) (v : Node)
    (m : ℝ) (hm : ∀ a, v <+: a → nodeMean law a ≤ m) (n : ℕ) (Y : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, regionCount ν ρ v i Y * nodeMean law (action ν ρ Y i)) ≤
      m * (visits (history ν ρ Y n) v : ℝ) := by
  rw [← sum_regionCount_eq_visits, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hv : v <+: action ν ρ Y i
  · simpa only [regionCount, if_pos hv, mul_one, one_mul] using hm _ hv
  · simp only [regionCount, if_neg hv, mul_zero, zero_mul, le_refl]

theorem count_mul_width (T L : ℝ) (hT : 0 < T) :
    T * Real.sqrt (2*L/T) = Real.sqrt (2*T*L) := by
  have he : 2*T*L = T^2*(2*L/T) := by field_simp
  rw [he, Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT.le]

/-- A low U value in a region whose descendant means exceed `best-D`
forces a lower centered-noise deviation, on the exact generated history. -/
theorem upper_le_implies_lower_deviation (ν ρ : ℝ) (law : Kernel Node ℝ)
    (v : Node) (best : ℝ)
    (hm : ∀ a, v <+: a → best - ν*ρ^v.length ≤ nodeMean law a)
    (n : ℕ) (Y : ℕ → ℝ)
    (hu : upper ν ρ (history ν ρ Y n) v ≤ (best : WithTop ℝ)) :
    0 < visits (history ν ρ Y n) v ∧
      Real.sqrt (2*(visits (history ν ρ Y n) v : ℝ)*Real.log (max (n:ℝ) 2)) ≤
        regionDeviation ν ρ law v n true Y := by
  have ht : visits (history ν ρ Y n) v ≠ 0 := by
    intro ht
    simp [upper, ht] at hu
  have htR : 0 < (visits (history ν ρ Y n) v : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ht
  have huR : rewardSum (history ν ρ Y n) v / visits (history ν ρ Y n) v +
      Real.sqrt (2*Real.log (max (n:ℝ) 2)/visits (history ν ρ Y n) v) +
      ν*ρ^v.length ≤ best := by
    simpa only [upper, if_neg ht, history_length, WithTop.coe_le_coe] using hu
  have hmean := regional_means_lower ν ρ law v (best-ν*ρ^v.length) hm n Y
  have hdiv : rewardSum (history ν ρ Y n) v / visits (history ν ρ Y n) v ≤
      best - ν*ρ^v.length - Real.sqrt (2*Real.log (max (n:ℝ) 2)/visits (history ν ρ Y n) v) := by
    linarith
  have hmul := (div_le_iff₀ htR).mp hdiv
  refine ⟨Nat.pos_of_ne_zero ht, ?_⟩
  simp only [regionDeviation, if_true, sum_regionNoise_eq_rewardSum_sub_means]
  rw [← count_mul_width _ _ htR]
  nlinarith

theorem upper_underestimate_probability (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (best : ℝ)
    (hm : ∀ a, v <+: a → best - ν*ρ^v.length ≤ nodeMean law a) (n : ℕ) :
    (trajectory ν ρ law) {Y | upper ν ρ (history ν ρ Y n) v ≤ (best : WithTop ℝ)} ≤
      (n : ENNReal) * ENNReal.ofReal (Real.exp (-4*Real.log (max (n:ℝ) 2))) := by
  apply (measure_mono (fun Y hY => upper_le_implies_lower_deviation ν ρ law v best hm n Y hY)).trans
  exact region_deviation_confidence ν ρ law hbound v n true _
    (Real.log_nonneg (le_max_of_le_right (by norm_num)))

theorem width_le_half_gap (T L gap : ℝ) (hT : 0 < T) (hgap : 0 < gap)
    (hcount : 8*L/gap^2 ≤ T) : Real.sqrt (2*L/T) ≤ gap/2 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · apply (div_le_iff₀ hT).mpr
    have hh := (div_le_iff₀ (sq_pos_of_pos hgap)).mp hcount
    nlinarith

theorem upper_ge_implies_upper_deviation (ν ρ : ℝ) (law : Kernel Node ℝ)
    (v : Node) (best gap : ℝ) (hgap : 0 < gap - ν*ρ^v.length)
    (hm : ∀ a, v <+: a → nodeMean law a ≤ best-gap)
    (n : ℕ) (Y : ℕ → ℝ)
    (hcount : 8*Real.log (max (n:ℝ) 2)/(gap-ν*ρ^v.length)^2 ≤
      (visits (history ν ρ Y n) v : ℝ))
    (hu : (best : WithTop ℝ) ≤ upper ν ρ (history ν ρ Y n) v) :
    0 < visits (history ν ρ Y n) v ∧
      Real.sqrt (2*(visits (history ν ρ Y n) v : ℝ)*Real.log (max (n:ℝ) 2)) ≤
        regionDeviation ν ρ law v n false Y := by
  have hL : 0 < Real.log (max (n:ℝ) 2) := Real.log_pos (lt_max_of_lt_right (by norm_num))
  have htR : 0 < (visits (history ν ρ Y n) v : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos (by norm_num) hL) (sq_pos_of_pos hgap)) hcount
  have ht : visits (history ν ρ Y n) v ≠ 0 := by exact_mod_cast htR.ne'
  have huR : best ≤ rewardSum (history ν ρ Y n) v / visits (history ν ρ Y n) v +
      Real.sqrt (2*Real.log (max (n:ℝ) 2)/visits (history ν ρ Y n) v) + ν*ρ^v.length := by
    simpa only [upper, if_neg ht, history_length, WithTop.coe_le_coe] using hu
  have hmean := regional_means_upper ν ρ law v (best-gap) hm n Y
  have hdiv : best - ν*ρ^v.length -
      Real.sqrt (2*Real.log (max (n:ℝ) 2)/visits (history ν ρ Y n) v) ≤
        rewardSum (history ν ρ Y n) v / visits (history ν ρ Y n) v := by linarith
  have hmul := (le_div_iff₀ htR).mp hdiv
  have hw := width_le_half_gap _ _ _ htR hgap hcount
  refine ⟨Nat.pos_of_ne_zero ht, ?_⟩
  simp only [regionDeviation, Bool.false_eq_true, if_false, sum_regionNoise_eq_rewardSum_sub_means]
  rw [← count_mul_width _ _ htR]
  nlinarith

theorem upper_overestimate_probability (ν ρ : ℝ) (law : Kernel Node ℝ)
    [IsMarkovKernel law]
    (hbound : ∀ a, ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (best gap : ℝ) (hgap : 0 < gap - ν*ρ^v.length)
    (hm : ∀ a, v <+: a → nodeMean law a ≤ best-gap) (n : ℕ) :
    (trajectory ν ρ law) {Y |
      8*Real.log (max (n:ℝ) 2)/(gap-ν*ρ^v.length)^2 ≤ (visits (history ν ρ Y n) v : ℝ) ∧
      (best : WithTop ℝ) ≤ upper ν ρ (history ν ρ Y n) v} ≤
      (n : ENNReal) * ENNReal.ofReal (Real.exp (-4*Real.log (max (n:ℝ) 2))) := by
  apply (measure_mono (fun Y hY =>
    upper_ge_implies_upper_deviation ν ρ law v best gap hgap hm n Y hY.1 hY.2)).trans
  exact region_deviation_confidence ν ρ law hbound v n false _
    (Real.log_nonneg (le_max_of_le_right (by norm_num)))

theorem Covering.nodeMean_eq {X : Type*} [MeasurableSpace X] (C : Covering X)
    (law : Kernel X ℝ) (f : X → ℝ) (hmean : ∀ x, (∫ y, y ∂law x) = f x) (a : Node) :
    nodeMean (C.nodeLaw law) a = f (C.representative a) := by
  exact hmean _

theorem RegularCovering.optimal_descendant_mean_lower {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) (f : X → ℝ) (best : ℝ)
    (hmean : ∀ x, (∫ y, y ∂law x) = f x) (hw : WeaklyLipschitz f C.ell best)
    (v : Node) (hv : regionSup f (C.region v) = best) :
    ∀ a, v <+: a → best - C.nu1*C.rho^v.length ≤ nodeMean (C.toCovering.nodeLaw law) a := by
  intro a ha
  have hmem := C.toCovering.descendant_subset ha (C.toCovering.representative_mem a)
  have hh := C.region_near_optimal f best 0 v hw (by simp [hv]) _ hmem
  norm_num at hh
  rw [C.toCovering.nodeMean_eq law f hmean a]
  linarith

theorem Covering.descendant_mean_upper {X : Type*} [MeasurableSpace X]
    (C : Covering X) (law : Kernel X ℝ) (f : X → ℝ) (best : ℝ)
    (hmean : ∀ x, (∫ y, y ∂law x) = f x) (hf : ∀ x, f x ≤ best) (v : Node) :
    ∀ a, v <+: a → nodeMean (C.nodeLaw law) a ≤ regionSup f (C.region v) := by
  intro a ha
  rw [C.nodeMean_eq law f hmean a]
  apply le_csSup (show BddAbove (f '' C.region v) from ⟨best, by
    rintro y ⟨x, _, rfl⟩; exact hf x⟩)
  exact ⟨C.representative a, C.descendant_subset ha (C.representative_mem a), rfl⟩

/-- Source optimal-region underestimation bound, now produced from A1/A2,
the reward-mean identity and bounded reward support. No confidence premise. -/
theorem RegularCovering.optimal_upper_underestimate_probability {X : Type*}
    [MeasurableSpace X] (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best : ℝ) (hmean : ∀ x, (∫ y, y ∂law x) = f x)
    (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (hv : regionSup f (C.region v) = best) (n : ℕ) :
    (trajectory C.nu1 C.rho (C.toCovering.nodeLaw law))
      {Y | upper C.nu1 C.rho (history C.nu1 C.rho Y n) v ≤ (best : WithTop ℝ)} ≤
      (n : ENNReal) * ENNReal.ofReal (Real.exp (-4*Real.log (max (n:ℝ) 2))) :=
  upper_underestimate_probability C.nu1 C.rho (C.toCovering.nodeLaw law)
    (fun a => hbound (C.toCovering.representative a)) v best
    (C.optimal_descendant_mean_lower law f best hmean hw v hv) n

theorem RegularCovering.poor_upper_overestimate_probability {X : Type*}
    [MeasurableSpace X] (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best : ℝ) (hmean : ∀ x, (∫ y, y ∂law x) = f x)
    (hf : ∀ x, f x ≤ best) (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0 : ℝ) 1)
    (v : Node) (hv : C.nu1*C.rho^v.length < best-regionSup f (C.region v)) (n : ℕ) :
    (trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) {Y |
      8*Real.log (max (n:ℝ) 2)/(best-regionSup f (C.region v)-C.nu1*C.rho^v.length)^2 ≤
        (visits (history C.nu1 C.rho Y n) v : ℝ) ∧
      (best : WithTop ℝ) ≤ upper C.nu1 C.rho (history C.nu1 C.rho Y n) v} ≤
      (n : ENNReal) * ENNReal.ofReal (Real.exp (-4*Real.log (max (n:ℝ) 2))) := by
  apply upper_overestimate_probability C.nu1 C.rho (C.toCovering.nodeLaw law)
    (fun a => hbound (C.toCovering.representative a)) v best (best-regionSup f (C.region v))
    (sub_pos.mpr hv)
  intro a ha
  simpa only [sub_sub_cancel] using C.toCovering.descendant_mean_upper law f best hmean hf v a ha

end BanditRLProof.HOO
