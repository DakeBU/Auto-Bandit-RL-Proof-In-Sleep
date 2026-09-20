import BanditRLProof.Algorithms.MusicalChairsCoordinationTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Round
import BanditRLProof.Algorithms.MusicalChairsCollision

open scoped Classical ENNReal
set_option autoImplicit false

namespace BanditRLProof.MusicalChairs

theorem base_gamma_upper {k : ℝ} (hk : 1 < k) :
    (1-1/k) ^ (2/5 : ℝ) ≤ 1 - (2/5 : ℝ)/k := by
  have hi : 1/k ≤ 1 := (div_le_one (by positivity)).2 hk.le
  have h := rpow_one_add_le_one_add_mul_self (s := -(1/k)) (by linarith)
    (p := (2/5 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem base_neg_gamma_lower {k : ℝ} (hk : 1 < k) :
    1 + (2/5 : ℝ)/k ≤ (1-1/k) ^ (-(2/5 : ℝ)) := by
  have hi : 1/k < 1 := (div_lt_one (by positivity)).2 hk
  have hb : 0 < 1-1/k := by linarith
  have hp : 0 < (1-1/k) ^ (2/5 : ℝ) := Real.rpow_pos_of_pos hb _
  rw [Real.rpow_neg hb.le, ← one_div, le_div_iff₀ hp]
  have h := mul_le_mul_of_nonneg_left (base_gamma_upper hk)
    (by positivity : (0 : ℝ) ≤ 1+(2/5 : ℝ)/k)
  nlinarith [sq_nonneg ((2/5 : ℝ)/k)]

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem avoidanceBase_eq {k : ℕ} (hk : 0 < k) :
    (((k-1 : ℕ) : ℝ)/(k : ℝ)) = 1-1/(k : ℝ) := by
  rw [Nat.cast_sub (by omega : 1 ≤ k)]
  push_cast
  field_simp

theorem avoidance_mass_lower {n k : ℕ} (hk : 1 < k) (hnk : n ≤ k) :
    (1/4 : ℝ) ≤ (1-1/(k : ℝ))^(n-1) := by
  rw [← avoidanceBase_eq (by omega)]
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hb : (((k-1 : ℕ) : ℝ)/(k : ℝ)) ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.sub_le k 1)
  exact (quarter_le_avoidance k (by omega)).trans
    (pow_le_pow_of_le_one (by positivity) hb (Nat.sub_le_sub_right hnk 1))

theorem collision_accuracy_sandwich {n k : ℕ} (hk : 1 < k) (hnk : n ≤ k)
    (pHat : ℝ) (hacc : |pHat-collisionProbReal n k| ≤ 1/(10*(k : ℝ))) :
    (1-1/(k : ℝ))^(n-1) * (1-1/(k : ℝ))^(2/5 : ℝ) ≤ 1-pHat ∧
    1-pHat ≤ (1-1/(k : ℝ))^(n-1) * (1-1/(k : ℝ))^(-(2/5 : ℝ)) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hq := avoidance_mass_lower hk hnk
  have hu := base_gamma_upper hkR
  have hl := base_neg_gamma_lower hkR
  have hq0 : 0 ≤ (1-1/(k : ℝ))^(n-1) := by linarith
  have hu' := mul_le_mul_of_nonneg_left hu hq0
  have hl' := mul_le_mul_of_nonneg_left hl hq0
  have hmargin := mul_le_mul_of_nonneg_right hq
    (by positivity : (0 : ℝ) ≤ (2/5 : ℝ)/(k : ℝ))
  have he : (1/4 : ℝ) * ((2/5 : ℝ)/(k : ℝ)) = 1/(10*(k : ℝ)) := by ring
  rw [he] at hmargin
  rw [collisionProbReal, avoidanceBase_eq (by omega)] at hacc
  rcases abs_le.mp hacc with ⟨ha,hb⟩
  constructor <;> nlinarith

theorem collision_accuracy_survival_pos {n k : ℕ} (hk : 1 < k) (hnk : n ≤ k)
    (pHat : ℝ) (hacc : |pHat-collisionProbReal n k| ≤ 1/(10*(k : ℝ))) : 0 < 1-pHat := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hb : 0 < 1-1/(k : ℝ) := by
    have hi : 1/(k : ℝ) < 1 := (div_lt_one (by positivity)).2 hkR
    linarith
  exact (mul_pos (pow_pos hb _) (Real.rpow_pos_of_pos hb _)).trans_le
    (collision_accuracy_sandwich hk hnk pHat hacc).1

theorem population_inverse_margin {n k : ℕ} (hn : 0 < n) (hk : 1 < k) (hnk : n ≤ k)
    (pHat : ℝ) (hacc : |pHat-collisionProbReal n k| ≤ 1/(10*(k : ℝ))) :
    (n : ℝ)-(2/5 : ℝ) ≤ 1+Real.log (1-pHat)/Real.log (1-1/(k : ℝ)) ∧
    1+Real.log (1-pHat)/Real.log (1-1/(k : ℝ)) ≤ (n : ℝ)+(2/5 : ℝ) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hb : 0 < 1-1/(k : ℝ) := by
    have hi : 1/(k : ℝ) < 1 := (div_lt_one (by positivity)).2 hkR
    linarith
  have hb1 : 1-1/(k : ℝ) < 1 := by
    have : (0 : ℝ) < 1/(k : ℝ) := by positivity
    linarith
  have hL := Real.log_neg hb hb1
  have hs := collision_accuracy_sandwich hk hnk pHat hacc
  have hy := collision_accuracy_survival_pos hk hnk pHat hacc
  have hl := Real.log_le_log (mul_pos (pow_pos hb (n-1)) (Real.rpow_pos_of_pos hb (2/5 : ℝ))) hs.1
  have hu := Real.log_le_log hy hs.2
  rw [Real.log_mul (ne_of_gt (pow_pos hb _)) (ne_of_gt (Real.rpow_pos_of_pos hb _)),
    Real.log_pow, Real.log_rpow hb] at hl hu
  have hncast : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hncast] at hl hu
  have hlo : (n : ℝ)-1-(2/5 : ℝ) ≤ Real.log (1-pHat)/Real.log (1-1/(k : ℝ)) := by
    apply (le_div_iff_of_neg hL).2
    nlinarith
  have hup : Real.log (1-pHat)/Real.log (1-1/(k : ℝ)) ≤ (n : ℝ)-1+(2/5 : ℝ) := by
    apply (div_le_iff_of_neg hL).2
    nlinarith
  constructor <;> linarith

theorem population_inverse_round {n k : ℕ} (hn : 0 < n) (hk : 1 < k) (hnk : n ≤ k)
    (pHat : ℝ) (hacc : |pHat-collisionProbReal n k| ≤ 1/(10*(k : ℝ))) :
    round (1+Real.log (1-pHat)/Real.log (1-1/(k : ℝ))) = (n : ℤ) := by
  apply round_eq_iff.mpr
  have h := population_inverse_margin hn hk hnk pHat hacc
  simp only [Set.mem_Ico, Int.cast_natCast]
  constructor <;> linarith [h.1,h.2]

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def populationInverse (k T C : ℕ) : ℝ :=
  1 + Real.log (((T-C : ℕ) : ℝ)/(T : ℝ)) / Real.log (1-1/(k : ℝ))

noncomputable def populationEstimate (k T C : ℕ) : ℕ :=
  if C = T then k else min k (round (populationInverse k T C)).toNat

noncomputable def localPopulationEstimate {k T : ℕ} (f : Fin T → ExplorationFeedback k) : ℕ :=
  populationEstimate k T (localCollisionCount f)

theorem localCollisionCount_le {k T : ℕ} (f : Fin T → ExplorationFeedback k) :
    localCollisionCount f ≤ T := by
  simpa [localCollisionCount] using
    (Finset.card_filter_le (s := Finset.univ) (p := fun t => (f t).collided = true))

theorem noncollision_fraction_eq {T C : ℕ} (hT : 0 < T) (hC : C ≤ T) :
    (((T-C : ℕ) : ℝ)/(T : ℝ)) = 1-(C : ℝ)/(T : ℝ) := by
  rw [Nat.cast_sub hC]
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  field_simp

theorem populationInverse_ge_one {k T C : ℕ} (hk : 1 < k) (hC : C < T) :
    1 ≤ populationInverse k T C := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hq : 0 < (((T-C : ℕ) : ℝ)/(T : ℝ)) := by
    apply div_pos _ hTr
    exact_mod_cast (Nat.sub_pos_of_lt hC)
  have hq1 : (((T-C : ℕ) : ℝ)/(T : ℝ)) ≤ 1 := by
    apply (div_le_one hTr).2
    exact_mod_cast (Nat.sub_le T C)
  have hlogq : Real.log (((T-C : ℕ) : ℝ)/(T : ℝ)) ≤ 0 := Real.log_nonpos hq.le hq1
  have hb : 0 < 1-1/(k : ℝ) := by
    have hi : 1/(k : ℝ) < 1 := (div_lt_one (by positivity)).2 hkR
    linarith
  have hb1 : 1-1/(k : ℝ) < 1 := by
    have hi : (0 : ℝ) < 1/(k : ℝ) := by positivity
    linarith
  have hdiv := div_nonneg_of_nonpos hlogq (Real.log_neg hb hb1).le
  unfold populationInverse
  linarith

theorem populationEstimate_le (k T C : ℕ) : populationEstimate k T C ≤ k := by
  unfold populationEstimate
  split_ifs
  · rfl
  · exact min_le_left _ _

theorem populationEstimate_all_collision (k T : ℕ) : populationEstimate k T T = k := by
  simp [populationEstimate]

theorem populationEstimate_zero_collision {k T : ℕ} (hk : 0 < k) (hT : 0 < T) :
    populationEstimate k T 0 = 1 := by
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  simp [populationEstimate, populationInverse, (Nat.ne_of_gt hT).symm,
    hTr, min_eq_right (show 1 ≤ k by omega)]

theorem populationEstimate_correct {n k T C : ℕ} (hn : 0 < n) (hk : 1 < k)
    (hnk : n ≤ k) (hT : 0 < T) (hC : C ≤ T)
    (hacc : |(C : ℝ)/T-collisionProbReal n k| ≤ 1/(10*(k : ℝ))) :
    populationEstimate k T C = n := by
  have hq := collision_accuracy_survival_pos hk hnk ((C : ℝ)/T) hacc
  have hne : C ≠ T := by
    intro he
    have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
    simp [he,hTr] at hq
  have hr := population_inverse_round hn hk hnk ((C : ℝ)/T) hacc
  rw [populationEstimate, if_neg hne, populationInverse, noncollision_fraction_eq hT hC, hr]
  simp [min_eq_right hnk]

theorem localPopulationEstimate_correct {n k T : ℕ} (hn : 0 < n) (hk : 1 < k)
    (hnk : n ≤ k) (hT : 0 < T) (f : Fin T → ExplorationFeedback k)
    (hacc : |(localCollisionCount f : ℝ)/T-collisionProbReal n k| ≤ 1/(10*(k : ℝ))) :
    localPopulationEstimate f = n :=
  populationEstimate_correct hn hk hnk hT (localCollisionCount_le f) hacc

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem populationEstimate_regular_cast {k T C : ℕ} (hk : 1 < k) (hC : C < T) :
    (populationEstimate k T C : ℤ) = min (k : ℤ) (round (populationInverse k T C)) := by
  have hnonneg : 0 ≤ round (populationInverse k T C) := by
    rw [round_eq]
    apply Int.floor_nonneg.mpr
    have h := populationInverse_ge_one hk hC
    linarith
  rw [populationEstimate, if_neg (Nat.ne_of_lt hC), Nat.cast_min, Int.toNat_of_nonneg hnonneg]

theorem collisionCount_le {n k T : ℕ} (x : Fin T → Fin n → Fin k) (i : Fin n) :
    collisionCount i x ≤ T := by
  simpa only [localCollisionCount_eq] using
    localCollisionCount_le (explorationFeedback x (fun _ _ => 0) i)

theorem localPopulationEstimate_eq {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (r : Fin T → Fin k → ℝ) (i : Fin n) :
    localPopulationEstimate (explorationFeedback x r i) = populationEstimate k T (collisionCount i x) := by
  simp [localPopulationEstimate, localCollisionCount_eq]

def populationRecovered {n k T : ℕ} : Set (Fin T → Fin n → Fin k) :=
  {x | ∀ i : Fin n, populationEstimate k T (collisionCount i x) = n}

theorem allCollisionAccurate_subset_populationRecovered {n k T : ℕ} (hn : 0 < n)
    (hk : 1 < k) (hnk : n ≤ k) (hT : 0 < T) :
    allCollisionAccurate (n := n) (k := k) (T := T) ⊆ populationRecovered := by
  intro x hx i
  exact populationEstimate_correct hn hk hnk hT (collisionCount_le x i) (hx i).le

theorem populationRecovered_probability {n k T : ℕ} (hn : 0 < n) (hk : 1 < k)
    (hnk : n ≤ k) (hT : 0 < T) (delta : ℝ) (hdelta : 0 < delta)
    (hbudget : (50*(k : ℝ)^2) * Real.log (4*(k : ℝ)/delta) ≤ T) :
    1 - ENNReal.ofReal (delta/2) ≤
      (explorationLaw n k T (by omega)).toMeasure (populationRecovered (n := n) (k := k) (T := T)) :=
  (allCollisionAccurate_probability (by omega) hnk hT delta hdelta hbudget).trans
    (measure_mono (allCollisionAccurate_subset_populationRecovered hn hk hnk hT))

def explorationEstimatesCorrect {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | (∀ i : Fin n, ∀ a : Fin k,
        |localEmpiricalMean (explorationFeedback z.1 z.2 i) a - armMean nu a| < eps/2) ∧
    (∀ i : Fin n, localPopulationEstimate (explorationFeedback z.1 z.2 i) = n)}

theorem explorationEstimatesCorrect_eq_inter {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    explorationEstimatesCorrect (n := n) (T := T) nu eps =
      allMeanAccurate nu eps ∩ Prod.fst ⁻¹' populationRecovered := by
  ext z
  simp [explorationEstimatesCorrect, allMeanAccurate, populationRecovered, localPopulationEstimate_eq]

theorem measurableSet_explorationEstimatesCorrect {n k T : ℕ}
    (nu : Fin k → Measure ℝ) (eps : ℝ) :
    MeasurableSet (explorationEstimatesCorrect (n := n) (T := T) nu eps) := by
  rw [explorationEstimatesCorrect_eq_inter, allMeanAccurate_eq_compl]
  exact (MeasurableSet.iUnion (fun i => MeasurableSet.iUnion
    (fun a => measurableSet_meanBadEvent nu i a eps))).compl.inter
      ((Set.toFinite _).measurableSet.preimage measurable_fst)

theorem explorationStatisticsAccurate_subset_estimatesCorrect {n k T : ℕ}
    (hn : 0 < n) (hk : 1 < k) (hnk : n ≤ k) (hT : 0 < T)
    (nu : Fin k → Measure ℝ) (eps : ℝ) :
    explorationStatisticsAccurate (n := n) (T := T) nu eps ⊆ explorationEstimatesCorrect nu eps := by
  intro z hz
  refine ⟨hz.1, fun i => ?_⟩
  exact localPopulationEstimate_correct hn hk hnk hT (explorationFeedback z.1 z.2 i) (hz.2 i).le

theorem explorationEstimatesCorrect_probability {n k : ℕ} (hn : 0 < n) (hk : 1 < k)
    (hnk : n ≤ k) (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - ENNReal.ofReal delta ≤ explorationRewardLaw (by omega) nu
      (explorationEstimatesCorrect (n := n) (T := explorationLength k eps delta) nu eps) :=
  (explorationStatisticsAccurate_at_explorationLength (by omega) hnk nu hb eps delta heps heps1
    hdelta hdelta1).trans (measure_mono (explorationStatisticsAccurate_subset_estimatesCorrect
      hn hk hnk (explorationLength_pos (by omega) eps delta hdelta hdelta1) nu eps))

end BanditRLProof.MusicalChairs

