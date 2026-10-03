import BanditRLProof.Algorithms.MusicalChairsCoordinationTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import BanditRLProof.Algorithms.MusicalChairsReward

open scoped Classical ENNReal
set_option autoImplicit false

namespace BanditRLProof.FinitePMF
open MeasureTheory ProbabilityTheory

theorem iid_toMeasure_pi {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (T : ℕ) :
    (iid p T).toMeasure = Measure.pi (fun _ : Fin T => p.toMeasure) := by
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), iid_apply,
    Measure.pi_singleton]
  congr 1
  ext t
  exact (PMF.toMeasure_apply_singleton p (x t) (measurableSet_singleton _)).symm

noncomputable def eventIndicator {α : Type*} (E : Set α) (a : α) : ℝ :=
  if a ∈ E then 1 else 0

theorem eventIndicator_mean {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E : Set α) :
    (∫ a, eventIndicator E a ∂p.toMeasure) = p.toMeasure.real E := by
  have he : eventIndicator E = E.indicator (fun _ : α => (1 : ℝ)) := by
    ext a
    simp [eventIndicator, Set.indicator]
  rw [he, integral_indicator (Set.toFinite E).measurableSet, integral_const]
  simp

theorem iid_indicator_mean {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E : Set α) {T : ℕ} (t : Fin T) :
    (∫ x, eventIndicator E (x t) ∂(iid p T).toMeasure) = p.toMeasure.real E := by
  rw [iid_toMeasure_pi]
  have hm := measurePreserving_eval (fun _ : Fin T => p.toMeasure) t
  calc
    _ = ∫ a, eventIndicator E a ∂(Measure.pi (fun _ : Fin T => p.toMeasure)).map
        (fun x => x t) := (integral_map hm.measurable.aemeasurable
          (measurable_of_finite _).aestronglyMeasurable).symm
    _ = _ := by rw [hm.map_eq, eventIndicator_mean]

theorem iid_indicator_subGaussian {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E : Set α) {T : ℕ} (t : Fin T) :
    HasSubgaussianMGF (fun x => eventIndicator E (x t) - p.toMeasure.real E)
      (1/4 : NNReal) (iid p T).toMeasure := by
  have hb : ∀ᵐ x ∂(iid p T).toMeasure, eventIndicator E (x t) ∈ Set.Icc (0 : ℝ) 1 := by
    apply Filter.Eventually.of_forall
    intro x
    simp only [eventIndicator]
    split_ifs <;> norm_num
  have h := hasSubgaussianMGF_of_mem_Icc (measurable_of_finite
    (fun x : Fin T → α => eventIndicator E (x t))).aemeasurable hb
  norm_num [iid_indicator_mean] at h ⊢
  exact h

theorem iid_indicator_independent {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E : Set α) (T : ℕ) :
    iIndepFun (fun t (x : Fin T → α) => eventIndicator E (x t) - p.toMeasure.real E)
      (iid p T).toMeasure := by
  rw [iid_toMeasure_pi]
  apply iIndepFun_pi (Ω := fun _ : Fin T => α) (𝓧 := fun _ : Fin T => ℝ)
    (μ := fun _ : Fin T => p.toMeasure)
    (X := fun _ a => eventIndicator E a - p.toMeasure.real E)
  intro t
  exact (measurable_of_finite _).aemeasurable

end BanditRLProof.FinitePMF

namespace BanditRLProof.FinitePMF
open MeasureTheory ProbabilityTheory

theorem eventCount_eq_sum {α : Type*} {T : ℕ} (E : Set α) (x : Fin T → α) :
    (eventCount E x : ℝ) = ∑ t, eventIndicator E (x t) := by
  simp [eventCount, eventIndicator]

theorem iid_centered_sum_subGaussian {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E : Set α) (T : ℕ) :
    HasSubgaussianMGF (fun x : Fin T → α => ∑ t, (eventIndicator E (x t) - p.toMeasure.real E))
      ((T : NNReal)/4) (iid p T).toMeasure := by
  have h := HasSubgaussianMGF.sum_of_iIndepFun (iid_indicator_independent p E T)
    (s := Finset.univ) (fun t _ => iid_indicator_subGaussian p E t)
  simpa [div_eq_mul_inv] using h

theorem iid_centered_sum_abs_tail {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E : Set α) (T : ℕ)
    (u : ℝ) (hu : 0 ≤ u) :
    (iid p T).toMeasure.real {x | u ≤ |∑ t, (eventIndicator E (x t) - p.toMeasure.real E)|} ≤
      2 * Real.exp (-u^2 / (2 * ((T : ℝ)/4))) := by
  have h := iid_centered_sum_subGaussian p E T
  have hp := h.measure_ge_le hu
  have hn := h.neg.measure_ge_le hu
  have he : {x : Fin T → α | u ≤ |∑ t, (eventIndicator E (x t) - p.toMeasure.real E)|} =
      {x | u ≤ ∑ t, (eventIndicator E (x t) - p.toMeasure.real E)} ∪
      {x | u ≤ -(∑ t, (eventIndicator E (x t) - p.toMeasure.real E))} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [he]
  have hU := measureReal_union_le (μ := (iid p T).toMeasure)
    {x | u ≤ ∑ t, (eventIndicator E (x t) - p.toMeasure.real E)}
    {x | u ≤ -(∑ t, (eventIndicator E (x t) - p.toMeasure.real E))}
  simp only [Pi.neg_apply, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat] at hp hn
  linarith

theorem iid_frequency_tail {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E : Set α) {T : ℕ} (hT : 0 < T)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (iid p T).toMeasure.real {x | eta ≤ |(eventCount E x : ℝ)/T - p.toMeasure.real E|} ≤
      2 * Real.exp (-2 * T * eta^2) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have h := iid_centered_sum_abs_tail p E T ((T : ℝ)*eta) (by positivity)
  have hid (x : Fin T → α) :
      (∑ t, (eventIndicator E (x t) - p.toMeasure.real E)) =
        (T : ℝ)*((eventCount E x : ℝ)/T - p.toMeasure.real E) := by
    rw [Finset.sum_sub_distrib, ← eventCount_eq_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hid, abs_mul, abs_of_pos hTr, mul_le_mul_iff_right₀ hTr] at h
  convert h using 1
  congr 2
  field_simp
  ring

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def collisionProbReal (n k : ℕ) : ℝ :=
  1 - (((k-1 : ℕ) : ℝ)/(k : ℝ))^(n-1)

theorem collision_indicator_mean {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    (explorationDraw n k hk).toMeasure.real {draw | ¬ CollisionFree draw i} =
      collisionProbReal n k := by
  have hfree := exploration_collisionFree_probability hk i
  have hle : (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1) ≤ 1 := by
    rw [← hfree, ← PMF.toMeasure_apply_eq_toOuterMeasure]
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  rw [measureReal_def, PMF.toMeasure_apply_eq_toOuterMeasure,
    exploration_collision_probability hk i, ENNReal.toReal_sub_of_le hle (by simp)]
  simp only [collisionProbReal, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_natCast]

noncomputable def localCollisionRate {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (r : Fin T → Fin k → ℝ) (i : Fin n) : ℝ :=
  (localCollisionCount (explorationFeedback x r i) : ℝ)/T

theorem localCollisionRate_eq {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (r : Fin T → Fin k → ℝ) (i : Fin n) :
    localCollisionRate x r i = (collisionCount i x : ℝ)/T := by
  simp [localCollisionRate, localCollisionCount_eq]

def collisionBadEvent {n k T : ℕ} (i : Fin n) : Set (Fin T → Fin n → Fin k) :=
  {x | 1/(10*(k : ℝ)) ≤ |(collisionCount i x : ℝ)/T - collisionProbReal n k|}

theorem collisionBadEvent_bound {n k T : ℕ} (hk : 0 < k) (hT : 0 < T) (i : Fin n) :
    (explorationLaw n k T hk).toMeasure (collisionBadEvent (k := k) (T := T) i) ≤
      ENNReal.ofReal (2 * Real.exp (-(T : ℝ)/(50*(k : ℝ)^2))) := by
  have h := FinitePMF.iid_frequency_tail (explorationDraw n k hk)
    {draw | ¬ CollisionFree draw i} hT (1/(10*(k : ℝ))) (by positivity)
  rw [collision_indicator_mean hk i] at h
  have he : -2*(T : ℝ)*(1/(10*(k : ℝ)))^2 = -(T : ℝ)/(50*(k : ℝ)^2) := by ring
  rw [he] at h
  have h' := ENNReal.ofReal_le_ofReal h
  rw [ofReal_measureReal] at h'
  exact h'

def allCollisionBadEvent {n k T : ℕ} : Set (Fin T → Fin n → Fin k) :=
  ⋃ i : Fin n, collisionBadEvent i

theorem allCollisionBadEvent_bound {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (hT : 0 < T) :
    (explorationLaw n k T hk).toMeasure (allCollisionBadEvent (n := n) (k := k) (T := T)) ≤
      ENNReal.ofReal (2*(k : ℝ)*Real.exp (-(T : ℝ)/(50*(k : ℝ)^2))) := by
  calc
    _ ≤ ∑ i : Fin n, (explorationLaw n k T hk).toMeasure (collisionBadEvent (T := T) i) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (2 * Real.exp (-(T : ℝ)/(50*(k : ℝ)^2))) :=
      Finset.sum_le_sum (fun i _ => collisionBadEvent_bound hk hT i)
    _ = ENNReal.ofReal ((n : ℝ)*(2 * Real.exp (-(T : ℝ)/(50*(k : ℝ)^2)))) := by
      simp [ENNReal.ofReal_mul, mul_comm]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hnr : (n : ℝ) ≤ k := by exact_mod_cast hnk
      nlinarith [Real.exp_pos (-(T : ℝ)/(50*(k : ℝ)^2))]

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem collision_exploration_threshold (k T : ℕ) (hk : 0 < k) (delta : ℝ)
    (hdelta : 0 < delta)
    (hT : (50*(k : ℝ)^2) * Real.log (4*(k : ℝ)/delta) ≤ T) :
    2*(k : ℝ) * Real.exp (-(T : ℝ)/(50*(k : ℝ)^2)) ≤ delta/2 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log (4*(k : ℝ)/delta) ≤ (T : ℝ)/(50*(k : ℝ)^2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 50*(k : ℝ)^2)).2
    simpa [mul_comm] using hT
  calc
    _ ≤ 2*(k : ℝ) * Real.exp (-Real.log (4*(k : ℝ)/delta)) := by
      gcongr
      convert neg_le_neg hlog using 1
      ring
    _ = delta/2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
      ring

theorem allCollisionBadEvent_le_half_delta {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (hT : 0 < T) (delta : ℝ) (hdelta : 0 < delta)
    (hbudget : (50*(k : ℝ)^2) * Real.log (4*(k : ℝ)/delta) ≤ T) :
    (explorationLaw n k T hk).toMeasure (allCollisionBadEvent (n := n) (k := k) (T := T)) ≤
      ENNReal.ofReal (delta/2) :=
  (allCollisionBadEvent_bound hk hnk hT).trans
    (ENNReal.ofReal_le_ofReal (collision_exploration_threshold k T hk delta hdelta hbudget))

def allCollisionAccurate {n k T : ℕ} : Set (Fin T → Fin n → Fin k) :=
  {x | ∀ i : Fin n, |(collisionCount i x : ℝ)/T - collisionProbReal n k| < 1/(10*(k : ℝ))}

theorem allCollisionAccurate_eq_compl {n k T : ℕ} :
    allCollisionAccurate (n := n) (k := k) (T := T) = (allCollisionBadEvent)ᶜ := by
  ext x
  simp [allCollisionAccurate, allCollisionBadEvent, collisionBadEvent]

theorem allCollisionAccurate_probability {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (hT : 0 < T) (delta : ℝ) (hdelta : 0 < delta)
    (hbudget : (50*(k : ℝ)^2) * Real.log (4*(k : ℝ)/delta) ≤ T) :
    1 - ENNReal.ofReal (delta/2) ≤
      (explorationLaw n k T hk).toMeasure (allCollisionAccurate (n := n) (k := k) (T := T)) := by
  rw [allCollisionAccurate_eq_compl,
    measure_compl (Set.toFinite _).measurableSet (by finiteness), measure_univ]
  exact tsub_le_tsub_left (allCollisionBadEvent_le_half_delta hk hnk hT delta hdelta hbudget) 1

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem explorationRewardLaw_fst_event {n k T : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (E : Set (Fin T → Fin n → Fin k)) :
    explorationRewardLaw hk nu (Prod.fst ⁻¹' E) = (explorationLaw n k T hk).toMeasure E := by
  have he : (Prod.fst ⁻¹' E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) =
      E ×ˢ Set.univ := by ext z; simp
  rw [he, explorationRewardLaw, Measure.prod_prod, measure_univ, mul_one]

def statisticsBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  allMeanBadEvent nu eps ∪ Prod.fst ⁻¹' allCollisionBadEvent

theorem statisticsBadEvent_le_delta {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 < delta)
    (hT : 0 < T)
    (hmeans : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T)
    (hcoll : (50*(k : ℝ)^2) * Real.log (4*(k : ℝ)/delta) ≤ T) :
    explorationRewardLaw hk nu (statisticsBadEvent (n := n) (T := T) nu eps) ≤
      ENNReal.ofReal delta := by
  calc
    _ ≤ explorationRewardLaw hk nu (allMeanBadEvent (n := n) (T := T) nu eps) +
        explorationRewardLaw hk nu (Prod.fst ⁻¹' (allCollisionBadEvent (n := n) (T := T) (k := k))) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (delta/2) + ENNReal.ofReal (delta/2) := by
      apply add_le_add
      · exact allMeanBadEvent_le_half_delta hk hnk nu hb eps delta heps heps1 hdelta hmeans
      · rw [explorationRewardLaw_fst_event]
        exact allCollisionBadEvent_le_half_delta hk hnk hT delta hdelta hcoll
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

def explorationStatisticsAccurate {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | (∀ i : Fin n, ∀ a : Fin k,
        |localEmpiricalMean (explorationFeedback z.1 z.2 i) a - armMean nu a| < eps/2) ∧
    (∀ i : Fin n, |localCollisionRate z.1 z.2 i - collisionProbReal n k| < 1/(10*(k : ℝ)))}

theorem explorationStatisticsAccurate_eq_compl {n k T : ℕ}
    (nu : Fin k → Measure ℝ) (eps : ℝ) :
    explorationStatisticsAccurate (n := n) (T := T) nu eps = (statisticsBadEvent nu eps)ᶜ := by
  ext z
  simp [explorationStatisticsAccurate, statisticsBadEvent, allMeanBadEvent,
    meanBadEvent, allCollisionBadEvent, collisionBadEvent, localCollisionRate_eq]

theorem explorationStatisticsAccurate_probability {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 < delta)
    (hT : 0 < T)
    (hmeans : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T)
    (hcoll : (50*(k : ℝ)^2) * Real.log (4*(k : ℝ)/delta) ≤ T) :
    1 - ENNReal.ofReal delta ≤
      explorationRewardLaw hk nu (explorationStatisticsAccurate (n := n) (T := T) nu eps) := by
  have hm : MeasurableSet (statisticsBadEvent (n := n) (T := T) nu eps) :=
    (MeasurableSet.iUnion (fun i => MeasurableSet.iUnion
      (fun a => measurableSet_meanBadEvent nu i a eps))).union
      ((Set.toFinite _).measurableSet.preimage measurable_fst)
  rw [explorationStatisticsAccurate_eq_compl, measure_compl hm (by finiteness), measure_univ]
  exact tsub_le_tsub_left
    (statisticsBadEvent_le_delta hk hnk nu hb eps delta heps heps1 hdelta hT hmeans hcoll) 1


end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def explorationLength (k : ℕ) (eps delta : ℝ) : ℕ :=
  ⌈max ((16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta))
    ((50*(k : ℝ)^2) * Real.log (4*(k : ℝ)/delta))⌉₊

theorem explorationLength_mean_budget (k : ℕ) (eps delta : ℝ) :
    (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ explorationLength k eps delta :=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem explorationLength_collision_budget (k : ℕ) (eps delta : ℝ) :
    (50*(k : ℝ)^2) * Real.log (4*(k : ℝ)/delta) ≤ explorationLength k eps delta :=
  (le_max_right _ _).trans (Nat.le_ceil _)

theorem explorationLength_pos {k : ℕ} (hk : 0 < k) (eps delta : ℝ)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) : 0 < explorationLength k eps delta := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 < Real.log (4*(k : ℝ)/delta) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hdelta).2
    nlinarith
  have hpos : (0 : ℝ) < 50*(k : ℝ)^2 * Real.log (4*(k : ℝ)/delta) := by positivity
  have h := hpos.trans_le (explorationLength_collision_budget k eps delta)
  exact_mod_cast h

theorem explorationStatisticsAccurate_at_explorationLength {n k : ℕ}
    (hk : 0 < k) (hnk : n ≤ k) (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - ENNReal.ofReal delta ≤ explorationRewardLaw hk nu
      (explorationStatisticsAccurate (n := n) (T := explorationLength k eps delta) nu eps) :=
  explorationStatisticsAccurate_probability hk hnk nu hb eps delta heps heps1 hdelta
    (explorationLength_pos hk eps delta hdelta hdelta1)
    (explorationLength_mean_budget k eps delta) (explorationLength_collision_budget k eps delta)

end BanditRLProof.MusicalChairs
