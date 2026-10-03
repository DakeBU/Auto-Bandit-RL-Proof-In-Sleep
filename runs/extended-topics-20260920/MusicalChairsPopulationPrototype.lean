import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import BanditRLProof.Algorithms.MusicalChairsCoordinationTime

open scoped Classical ENNReal
set_option autoImplicit false

namespace BanditRLProof.FinitePMF

noncomputable def iid {α : Type*} [Fintype α] (p : PMF α) (T : ℕ) : PMF (Fin T → α) :=
  PMF.ofFintype (fun x => ∏ t, p (x t)) (by
    rw [← Fintype.prod_sum]
    have hp : ∑ a, p a = 1 := by simpa [tsum_fintype] using p.tsum_coe
    simp [hp])

theorem iid_apply {α : Type*} [Fintype α] (p : PMF α) (T : ℕ) (x : Fin T → α) :
    iid p T x = ∏ t, p (x t) := by simp [iid, PMF.ofFintype_apply]

theorem iid_product_expectation {α : Type*} [Fintype α] (p : PMF α) (T : ℕ)
    (f : Fin T → α → ℝ≥0∞) :
    ∑ x, iid p T x * ∏ t, f t (x t) = ∏ t, ∑ a, p a * f t a := by
  simp_rw [iid_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun t a => p a * f t a)).symm

noncomputable def eventCount {α : Type*} {T : ℕ} (E : Set α) (x : Fin T → α) : ℕ :=
  (Finset.univ.filter (fun t => x t ∈ E)).card

theorem pow_eventCount {α : Type*} {T : ℕ} (E : Set α) (x : Fin T → α) (z : ℝ≥0∞) :
    z ^ eventCount E x = ∏ t, if x t ∈ E then z else 1 := by
  simp [eventCount, ← Finset.prod_filter]

theorem indicator_weight_sum {α : Type*} [Fintype α] (p : PMF α) (E : Set α)
    (z : ℝ≥0∞) :
    ∑ a, p a * (if a ∈ E then z else 1) =
      p.toOuterMeasure E * z + p.toOuterMeasure Eᶜ := by
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a ∈ E <;> simp [h, Set.indicator]

theorem iid_count_pgf {α : Type*} [Fintype α] (p : PMF α) (T : ℕ)
    (E : Set α) (z : ℝ≥0∞) :
    ∑ x, iid p T x * z ^ eventCount E x =
      (p.toOuterMeasure E * z + p.toOuterMeasure Eᶜ)^T := by
  simp_rw [pow_eventCount]
  rw [iid_product_expectation p T (fun _ a => if a ∈ E then z else 1)]
  simp_rw [indicator_weight_sum]
  simp

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs

noncomputable def explorationDraw (n k : ℕ) (hk : 0 < k) : PMF (Fin n → Fin k) :=
  jointDraw (fun _ => Finset.univ) (fun _ => ⟨⟨0, hk⟩, Finset.mem_univ _⟩)

noncomputable def explorationLaw (n k T : ℕ) (hk : 0 < k) :
    PMF (Fin T → Fin n → Fin k) := FinitePMF.iid (explorationDraw n k hk) T

def observes {n k : ℕ} (i : Fin n) (a : Fin k) : Set (Fin n → Fin k) :=
  {draw | draw i = a ∧ CollisionFree draw i}

theorem observes_rectangle {n k : ℕ} (i : Fin n) (a : Fin k) :
    observes i a = {draw | ∀ j, draw j ∈ isolationWindow i a j} := by
  ext draw
  constructor
  · intro ⟨hi, hc⟩ j
    by_cases hj : j = i
    · subst j; simpa [isolationWindow] using hi
    · simpa [isolationWindow, hj, hi] using hc j hj
  · intro h
    have hi : draw i = a := by simpa [isolationWindow] using h i
    refine ⟨hi, ?_⟩
    intro j hj
    simpa [isolationWindow, hj, hi] using h j

theorem exploration_observes_probability {n k : ℕ} (hk : 0 < k) (i : Fin n) (a : Fin k) :
    (explorationDraw n k hk).toOuterMeasure (observes i a) =
      (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) := by
  rw [observes_rectangle, explorationDraw, jointDraw_rectangle_product]
  have hentry (j : Fin n) :
      (((Finset.univ : Finset (Fin k)) ∩ isolationWindow i a j).card : ℝ≥0∞) /
        ((Finset.univ : Finset (Fin k)).card : ℝ≥0∞) =
      if j = i then 1 / (k : ℝ≥0∞) else (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞)) := by
    by_cases h : j = i <;> simp [isolationWindow, h]
  simp_rw [hentry]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _j ∈ (Finset.univ.erase i),
        (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞)) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    _ = _ := by simp


theorem exploration_collisionFree_split {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    (explorationDraw n k hk).toOuterMeasure {draw | CollisionFree draw i} =
      ∑ a : Fin k, (explorationDraw n k hk).toOuterMeasure (observes i a) := by
  simp_rw [PMF.toOuterMeasure_apply_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro draw _
  rw [Finset.sum_eq_single (draw i)]
  · simp [observes, Set.indicator]
  · intro a _ ha
    simp [observes, Set.indicator, Ne.symm ha]
  · simp

theorem exploration_collisionFree_probability {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    (explorationDraw n k hk).toOuterMeasure {draw | CollisionFree draw i} =
      (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) := by
  rw [exploration_collisionFree_split]
  simp_rw [exploration_observes_probability hk i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp [one_div, ENNReal.mul_inv_cancel hk0 (by simp)]

theorem exploration_collision_probability {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    (explorationDraw n k hk).toOuterMeasure {draw | ¬ CollisionFree draw i} =
      1 - (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) := by
  have h := event_add_compl (explorationDraw n k hk) {draw | CollisionFree draw i}
  rw [exploration_collisionFree_probability hk i] at h
  have he : ({draw : Fin n → Fin k | CollisionFree draw i} : Set _)ᶜ =
      {draw | ¬ CollisionFree draw i} := rfl
  rw [he] at h
  apply ENNReal.eq_sub_of_add_eq
  · have hb : (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) ≤ 1 := by
      calc
        _ ≤ _ + (explorationDraw n k hk).toOuterMeasure {draw | ¬ CollisionFree draw i} := le_self_add
        _ = 1 := h
    exact ne_of_lt (lt_of_le_of_lt hb ENNReal.one_lt_top)
  · simpa [add_comm] using h

noncomputable def observationCount {n k T : ℕ} (i : Fin n) (a : Fin k)
    (x : Fin T → Fin n → Fin k) : ℕ := FinitePMF.eventCount (observes i a) x

noncomputable def collisionCount {n k T : ℕ} (i : Fin n)
    (x : Fin T → Fin n → Fin k) : ℕ :=
  FinitePMF.eventCount {draw | ¬ CollisionFree draw i} x

theorem observationCount_pgf {n k : ℕ} (hk : 0 < k) (T : ℕ) (i : Fin n)
    (a : Fin k) (z : ℝ≥0∞) :
    let q := (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    ∑ x, explorationLaw n k T hk x * z ^ observationCount i a x =
      (q * z + (1-q))^T := by
  dsimp
  simp only [explorationLaw, observationCount]
  rw [FinitePMF.iid_count_pgf]
  have hc := event_add_compl (explorationDraw n k hk) (observes i a)
  have hp := exploration_observes_probability hk i a
  rw [hp] at hc ⊢
  have he : (explorationDraw n k hk).toOuterMeasure (observes i a)ᶜ =
      1 - (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) := by
    apply ENNReal.eq_sub_of_add_eq
    · have hle : (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) ≤ 1 := by
        calc
          _ ≤ _ + (explorationDraw n k hk).toOuterMeasure (observes i a)ᶜ := le_self_add
          _ = 1 := hc
      exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
    · simpa [add_comm] using hc
  rw [he]

theorem collisionCount_pgf {n k : ℕ} (hk : 0 < k) (T : ℕ) (i : Fin n)
    (z : ℝ≥0∞) :
    let b := (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    ∑ x, explorationLaw n k T hk x * z ^ collisionCount i x =
      ((1-b) * z + b)^T := by
  dsimp
  simp only [explorationLaw, collisionCount]
  rw [FinitePMF.iid_count_pgf,
    exploration_collision_probability hk i]
  have he : ({draw : Fin n → Fin k | ¬ CollisionFree draw i} : Set _)ᶜ =
      {draw | CollisionFree draw i} := by ext draw; simp
  rw [he, exploration_collisionFree_probability hk i]


theorem exploration_observes_lower {n k : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (i : Fin n) (a : Fin k) :
    (1 : ℝ≥0∞) / (4*k) ≤ (explorationDraw n k hk).toOuterMeasure (observes i a) := by
  rw [exploration_observes_probability hk i a]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hb : (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞)) ≤ 1 := by
    calc
      _ ≤ (k : ℝ≥0∞) / (k : ℝ≥0∞) := by
        gcongr
        exact_mod_cast (Nat.sub_le k 1)
      _ = 1 := ENNReal.div_self hk0 (by simp)
  calc
    _ ≤ (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(k-1) :=
      uniform_hazard_lower k hk
    _ ≤ _ := mul_le_mul_right
      (pow_le_pow_of_le_one (zero_le _) hb (Nat.sub_le_sub_right hnk 1)) _


theorem observationCount_laplace {n k : ℕ} (hk : 0 < k) (T : ℕ) (i : Fin n)
    (a : Fin k) (eta : ℝ) :
    let q := (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    ∑ x, explorationLaw n k T hk x *
      ENNReal.ofReal (Real.exp (-eta * (observationCount i a x : ℝ))) =
      (q * ENNReal.ofReal (Real.exp (-eta)) + (1-q))^T := by
  have he (m : ℕ) : ENNReal.ofReal (Real.exp (-eta * (m : ℝ))) =
      ENNReal.ofReal (Real.exp (-eta))^m := by
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 2
    ring
  simp_rw [he]
  exact observationCount_pgf hk T i a (ENNReal.ofReal (Real.exp (-eta)))


structure ExplorationFeedback (k : ℕ) where
  arm : Fin k
  collided : Bool
  reward : ℝ

noncomputable def explorationFeedback {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (rewards : Fin T → Fin k → ℝ) (i : Fin n) : Fin T → ExplorationFeedback k :=
  fun t => ⟨x t i, decide (¬ CollisionFree (x t) i),
    if CollisionFree (x t) i then rewards t (x t i) else 0⟩

noncomputable def localObservationCount {k T : ℕ} (f : Fin T → ExplorationFeedback k)
    (a : Fin k) : ℕ :=
  (Finset.univ.filter (fun t => (f t).arm = a ∧ (f t).collided = false)).card

noncomputable def localCollisionCount {k T : ℕ} (f : Fin T → ExplorationFeedback k) : ℕ :=
  (Finset.univ.filter (fun t => (f t).collided = true)).card

noncomputable def localRewardSum {k T : ℕ} (f : Fin T → ExplorationFeedback k)
    (a : Fin k) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => (f t).arm = a ∧ (f t).collided = false), (f t).reward

noncomputable def localEmpiricalMean {k T : ℕ} (f : Fin T → ExplorationFeedback k)
    (a : Fin k) : ℝ :=
  if localObservationCount f a = 0 then 0 else localRewardSum f a / localObservationCount f a

theorem localObservationCount_eq {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (rewards : Fin T → Fin k → ℝ) (i : Fin n) (a : Fin k) :
    localObservationCount (explorationFeedback x rewards i) a = observationCount i a x := by
  unfold localObservationCount observationCount FinitePMF.eventCount
  congr 1
  ext t
  simp [explorationFeedback, observes]

theorem localCollisionCount_eq {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (rewards : Fin T → Fin k → ℝ) (i : Fin n) :
    localCollisionCount (explorationFeedback x rewards i) = collisionCount i x := by
  unfold localCollisionCount collisionCount FinitePMF.eventCount
  congr 1
  ext t
  simp [explorationFeedback]

theorem localRewardSum_eq {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (rewards : Fin T → Fin k → ℝ) (i : Fin n) (a : Fin k) :
    localRewardSum (explorationFeedback x rewards i) a =
      ∑ t ∈ Finset.univ.filter (fun t => x t ∈ observes i a), rewards t a := by
  unfold localRewardSum
  apply Finset.sum_congr
  · ext t
    simp [explorationFeedback, observes]
  · intro t ht
    have h : x t i = a ∧ CollisionFree (x t) i := by
      simpa [explorationFeedback] using (Finset.mem_filter.mp ht).2
    simp [explorationFeedback, h.1, h.2]


namespace ExplorationCanary

theorem effective_probability :
    (explorationDraw 2 3 (by decide)).toOuterMeasure (observes (0 : Fin 2) (0 : Fin 3)) = 2/9 := by
  rw [exploration_observes_probability]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem collision_probability :
    (explorationDraw 2 3 (by decide)).toOuterMeasure {draw | ¬ CollisionFree draw (0 : Fin 2)} = 1/3 := by
  rw [exploration_collision_probability]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) (by simp)]
  norm_num

theorem effective_pgf (T : ℕ) (z : ℝ≥0∞) :
    ∑ x, explorationLaw 2 3 T (by decide) x * z ^ observationCount (0 : Fin 2) (0 : Fin 3) x =
      ((2/9)*z+7/9)^T := by
  have h := observationCount_pgf (n := 2) (k := 3) (by decide) T (0 : Fin 2) (0 : Fin 3) z
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  have hq : (1/3 : ℝ≥0∞) * (2/3) = 2/9 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  have hc : (1 : ℝ≥0∞) - 2/9 = 7/9 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) (by simp)]
    norm_num
  simpa only [hq, hc] using h

def mixedDraws : Fin 2 → Fin 2 → Fin 3 := fun t i =>
  if t = 0 then 0 else if i = 0 then 0 else 1

theorem mixed_counts : observationCount (0 : Fin 2) (0 : Fin 3) mixedDraws = 1 ∧
    collisionCount (0 : Fin 2) mixedDraws = 1 := by
  simp only [observationCount, collisionCount, FinitePMF.eventCount,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two]
  norm_num [mixedDraws, observes, CollisionFree, Fin.forall_fin_two]


theorem free_zero_reward :
    (explorationFeedback mixedDraws (fun _ _ => 0) (0 : Fin 2) (1 : Fin 2)).reward = 0 ∧
    (explorationFeedback mixedDraws (fun _ _ => 0) (0 : Fin 2) (1 : Fin 2)).collided = false := by
  norm_num [explorationFeedback, mixedDraws, CollisionFree, Fin.forall_fin_two]

theorem collision_zero_reward :
    (explorationFeedback mixedDraws (fun _ _ => 1) (0 : Fin 2) (0 : Fin 2)).reward = 0 ∧
    (explorationFeedback mixedDraws (fun _ _ => 1) (0 : Fin 2) (0 : Fin 2)).collided = true := by
  norm_num [explorationFeedback, mixedDraws, CollisionFree, Fin.forall_fin_two]

end ExplorationCanary
end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def rewardLaw {k : ℕ} (nu : Fin k → Measure ℝ) (T : ℕ) :
    Measure (Fin T → Fin k → ℝ) := Measure.pi (fun _ : Fin T => Measure.pi nu)

instance rewardLaw_probability {k : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (T : ℕ) : IsProbabilityMeasure (rewardLaw nu T) := by
  unfold rewardLaw
  infer_instance

noncomputable def armMean {k : ℕ} (nu : Fin k → Measure ℝ) (a : Fin k) : ℝ :=
  ∫ y, y ∂nu a

theorem reward_coordinate_preserving {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (t : Fin T) (a : Fin k) :
    MeasurePreserving (fun r : Fin T → Fin k → ℝ => r t a) (rewardLaw nu T) (nu a) := by
  exact (measurePreserving_eval nu a).comp
    (measurePreserving_eval (fun _ : Fin T => Measure.pi nu) t)

theorem reward_coordinate_mean {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (t : Fin T) (a : Fin k) :
    (∫ r, r t a ∂rewardLaw nu T) = armMean nu a := by
  have hm := reward_coordinate_preserving nu t a
  calc
    _ = ∫ y, y ∂(rewardLaw nu T).map (fun r => r t a) :=
      (integral_map hm.measurable.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = _ := by rw [hm.map_eq]; rfl

theorem reward_coordinate_bounded {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (t : Fin T) (a : Fin k) :
    ∀ᵐ r ∂rewardLaw nu T, r t a ∈ Set.Icc (0 : ℝ) 1 :=
  (reward_coordinate_preserving nu t a).quasiMeasurePreserving.ae (hb a)

theorem reward_coordinate_subGaussian {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (t : Fin T) (a : Fin k) :
    HasSubgaussianMGF (fun r : Fin T → Fin k → ℝ => r t a - armMean nu a)
      (1/4 : NNReal) (rewardLaw nu T) := by
  have h := hasSubgaussianMGF_of_mem_Icc
    (reward_coordinate_preserving nu t a).measurable.aemeasurable
    (reward_coordinate_bounded nu hb t a)
  norm_num [reward_coordinate_mean] at h ⊢
  exact h

theorem reward_time_independent {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (a : Fin k) :
    iIndepFun (fun t (r : Fin T → Fin k → ℝ) => r t a - armMean nu a) (rewardLaw nu T) := by
  apply iIndepFun_pi (Ω := fun _ : Fin T => Fin k → ℝ) (𝓧 := fun _ : Fin T => ℝ)
    (μ := fun _ : Fin T => Measure.pi nu)
    (X := fun _ (r : Fin k → ℝ) => r a - armMean nu a)
  intro t
  exact (show Measurable (fun r : Fin k → ℝ => r a - armMean nu a) from
    (measurable_pi_apply a).sub measurable_const).aemeasurable

theorem selected_sum_subGaussian {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k) :
    HasSubgaussianMGF (fun r : Fin T → Fin k → ℝ => ∑ t ∈ S, (r t a - armMean nu a))
      ((S.card : NNReal)/4) (rewardLaw nu T) := by
  have h := HasSubgaussianMGF.sum_of_iIndepFun (reward_time_independent nu a)
    (fun t (_ : t ∈ S) => reward_coordinate_subGaussian nu hb t a)
  simpa [div_eq_mul_inv] using h


theorem selected_sum_abs_tail {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (u : ℝ) (hu : 0 ≤ u) :
    (rewardLaw nu T).real {r | u ≤ |∑ t ∈ S, (r t a - armMean nu a)|} ≤
      2 * Real.exp (-u^2 / (2 * ((S.card : ℝ)/4))) := by
  have h := selected_sum_subGaussian nu hb S a
  have hp := h.measure_ge_le hu
  have hn := h.neg.measure_ge_le hu
  have he : {r : Fin T → Fin k → ℝ | u ≤ |∑ t ∈ S, (r t a - armMean nu a)|} =
      {r | u ≤ ∑ t ∈ S, (r t a - armMean nu a)} ∪
      {r | u ≤ -(∑ t ∈ S, (r t a - armMean nu a))} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [he]
  have hU := measureReal_union_le (μ := rewardLaw nu T)
    {r | u ≤ ∑ t ∈ S, (r t a - armMean nu a)}
    {r | u ≤ -(∑ t ∈ S, (r t a - armMean nu a))}
  simp only [Pi.neg_apply, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat] at hp hn
  linarith

noncomputable def selectedMean {k T : ℕ} (S : Finset (Fin T)) (a : Fin k)
    (r : Fin T → Fin k → ℝ) : ℝ :=
  if S.card = 0 then 0 else (∑ t ∈ S, r t a) / S.card

theorem selected_centered_sum {k T : ℕ} (nu : Fin k → Measure ℝ)
    (S : Finset (Fin T)) (a : Fin k) (hS : 0 < S.card) (r : Fin T → Fin k → ℝ) :
    (∑ t ∈ S, (r t a - armMean nu a)) = (S.card : ℝ) * (selectedMean S a r - armMean nu a) := by
  have h0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  simp only [selectedMean, if_neg (Nat.ne_of_gt hS), Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem selectedMean_tail_pos {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (hS : 0 < S.card) (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤
      2 * Real.exp (-(S.card : ℝ) * eps^2 / 2) := by
  have hD : 0 < (S.card : ℝ) := by exact_mod_cast hS
  have he : {r : Fin T → Fin k → ℝ | eps/2 ≤ |selectedMean S a r - armMean nu a|} =
      {r | (S.card : ℝ) * eps/2 ≤ |∑ t ∈ S, (r t a - armMean nu a)|} := by
    ext r
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, selected_centered_sum nu S a hS r,
      abs_mul, abs_of_pos hD]
    rw [mul_div_assoc, mul_le_mul_iff_right₀ hD]
  rw [he]
  have h := selected_sum_abs_tail nu hb S a ((S.card : ℝ)*eps/2) (by positivity)
  convert h using 1
  congr 2
  field_simp
  ring


theorem selectedMean_tail {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤
      2 * Real.exp (-(S.card : ℝ) * eps^2 / 2) := by
  by_cases hS : S.card = 0
  · have h : (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤ 1 :=
      measureReal_le_one
    simpa [hS] using h.trans (by norm_num : (1 : ℝ) ≤ 2)
  · exact selectedMean_tail_pos nu hb S a (Nat.pos_of_ne_zero hS) eps heps

noncomputable def observedTimes {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (i : Fin n) (a : Fin k) : Finset (Fin T) :=
  Finset.univ.filter (fun t => x t ∈ observes i a)

theorem localEmpiricalMean_eq_selectedMean {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (r : Fin T → Fin k → ℝ) (i : Fin n) (a : Fin k) :
    localEmpiricalMean (explorationFeedback x r i) a = selectedMean (observedTimes x i a) a r := by
  simp only [localEmpiricalMean, localObservationCount_eq, localRewardSum_eq,
    selectedMean, observedTimes, observationCount, FinitePMF.eventCount]

theorem localEmpiricalMean_fixed_tail {n k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin T → Fin n → Fin k) (i : Fin n) (a : Fin k) (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |localEmpiricalMean (explorationFeedback x r i) a - armMean nu a|} ≤
      2 * Real.exp (-(observationCount i a x : ℝ) * eps^2 / 2) := by
  simp_rw [localEmpiricalMean_eq_selectedMean]
  exact selectedMean_tail nu hb (observedTimes x i a) a eps heps

theorem measurable_selectedMean {k T : ℕ} (S : Finset (Fin T)) (a : Fin k) :
    Measurable (selectedMean S a) := by
  unfold selectedMean
  split_ifs <;> fun_prop

theorem measurable_jointEmpiricalMean {n k T : ℕ} (i : Fin n) (a : Fin k) :
    Measurable (fun z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ) =>
      localEmpiricalMean (explorationFeedback z.1 z.2 i) a) := by
  apply measurable_from_prod_countable_right
  intro x
  simp_rw [localEmpiricalMean_eq_selectedMean]
  exact measurable_selectedMean (observedTimes x i a) a

noncomputable def explorationRewardLaw {n k T : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) :
    Measure ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  (explorationLaw n k T hk).toMeasure.prod (rewardLaw nu T)

instance explorationRewardLaw_probability {n k T : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] :
    IsProbabilityMeasure (explorationRewardLaw (n := n) (T := T) hk nu) := by
  unfold explorationRewardLaw
  infer_instance

def meanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ) (i : Fin n) (a : Fin k) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | eps/2 ≤ |localEmpiricalMean (explorationFeedback z.1 z.2 i) a - armMean nu a|}

theorem measurableSet_meanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ)
    (i : Fin n) (a : Fin k) (eps : ℝ) : MeasurableSet (meanBadEvent (T := T) nu i a eps) := by
  exact measurableSet_le measurable_const ((measurable_jointEmpiricalMean i a).sub_const (armMean nu a)).abs

theorem meanBadEvent_mixture {n k T : ℕ} (hk : 0 < k) (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (i : Fin n) (a : Fin k) (eps : ℝ) :
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) =
      ∑ x, explorationLaw n k T hk x *
        rewardLaw nu T {r | eps/2 ≤ |localEmpiricalMean (explorationFeedback x r i) a - armMean nu a|} := by
  rw [explorationRewardLaw, Measure.prod_apply (measurableSet_meanBadEvent nu i a eps), lintegral_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), mul_comm]
  rfl


theorem meanBadEvent_count_bound {n k T : ℕ} (hk : 0 < k) (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (a : Fin k) (eps : ℝ) (heps : 0 ≤ eps) :
    let q := (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) ≤
      2 * (q * ENNReal.ofReal (Real.exp (-(eps^2/2))) + (1-q))^T := by
  dsimp
  rw [meanBadEvent_mixture]
  calc
    _ ≤ ∑ x, explorationLaw n k T hk x * ENNReal.ofReal
        (2 * Real.exp (-(observationCount i a x : ℝ) * eps^2 / 2)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_right
      rw [← ofReal_measureReal (μ := rewardLaw nu T)]
      exact ENNReal.ofReal_le_ofReal (localEmpiricalMean_fixed_tail nu hb x i a eps heps)
    _ = 2 * (∑ x, explorationLaw n k T hk x * ENNReal.ofReal
        (Real.exp (-(eps^2/2) * (observationCount i a x : ℝ)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have he : -(observationCount i a x : ℝ) * eps^2 / 2 =
          -(eps^2/2) * (observationCount i a x : ℝ) := by ring
      rw [he, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ = _ := by rw [observationCount_laplace]


theorem half_le_one_sub_exp_neg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x/2 ≤ 1 - Real.exp (-x) := by
  have hprod : (1+x) * Real.exp (-x) ≤ 1 := by
    calc
      _ ≤ Real.exp x * Real.exp (-x) := by
        gcongr
        linarith [Real.add_one_le_exp x]
      _ = 1 := by rw [← Real.exp_add]; simp
  have hquad : 0 ≤ x * (1-x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  by_contra hh
  have hlt : (1-x/2)*(1+x) < Real.exp (-x)*(1+x) := by
    apply mul_lt_mul_of_pos_right _ (by linarith)
    linarith
  nlinarith

theorem count_mixture_exp_bound (q eps : ℝ) (T : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    (q * Real.exp (-(eps^2/2)) + (1-q))^T ≤
      Real.exp (-(T : ℝ)*q*eps^2/4) := by
  have hsmall := half_le_one_sub_exp_neg (eps^2/2) (by positivity) (by nlinarith)
  have hbase : q * Real.exp (-(eps^2/2)) + (1-q) ≤
      Real.exp (-q*(1-Real.exp (-(eps^2/2)))) := by
    have h := Real.add_one_le_exp (-q*(1-Real.exp (-(eps^2/2))))
    nlinarith
  calc
    _ ≤ (Real.exp (-q*(1-Real.exp (-(eps^2/2)))))^T := by
      gcongr
      exact add_nonneg (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1)
    _ = Real.exp ((T : ℝ) * (-q*(1-Real.exp (-(eps^2/2))))) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (Nat.cast_nonneg T) hq0)
      nlinarith


noncomputable def explorationProbReal (n k : ℕ) : ℝ :=
  (1 / (k : ℝ)) * (((k-1 : ℕ) : ℝ) / (k : ℝ))^(n-1)

theorem explorationProbReal_nonneg (n k : ℕ) : 0 ≤ explorationProbReal n k := by
  unfold explorationProbReal
  positivity

theorem explorationProbReal_le_one (n k : ℕ) (hk : 0 < k) : explorationProbReal n k ≤ 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hb : (((k-1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.sub_le k 1)
  have hp : ((((k-1 : ℕ) : ℝ) / (k : ℝ))^(n-1)) ≤ 1 := by
    calc
      _ ≤ (1 : ℝ)^(n-1) := by gcongr
      _ = 1 := one_pow _
  have hdiv : (1 : ℝ)/k ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.succ_le_iff.mpr hk)
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans (by simpa using hdiv)

theorem explorationProbReal_lower (n k : ℕ) (hk : 0 < k) (hnk : n ≤ k) :
    (1 : ℝ)/(4*k) ≤ explorationProbReal n k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hb : (((k-1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.sub_le k 1)
  calc
    _ ≤ (1/(k : ℝ)) * (((k-1 : ℕ) : ℝ)/(k : ℝ))^(k-1) := real_uniform_hazard_lower k hk
    _ ≤ explorationProbReal n k := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by positivity) hb (Nat.sub_le_sub_right hnk 1)) (by positivity)

theorem ofReal_explorationProbReal (n k : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (explorationProbReal n k) =
      (1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1) := by
  unfold explorationProbReal
  simp only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/k),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < k), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ((k-1 : ℕ) : ℝ)/(k : ℝ))]

theorem meanBadEvent_exponential_bound {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (a : Fin k) (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) ≤
      ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*eps^2/(16*k))) := by
  let q := explorationProbReal n k
  have hq0 : 0 ≤ q := explorationProbReal_nonneg n k
  have hq1 : q ≤ 1 := explorationProbReal_le_one n k hk
  have hbase : 0 ≤ q * Real.exp (-(eps^2/2)) + (1-q) :=
    add_nonneg (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1)
  have hconv : 2 * (((1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1)) *
      ENNReal.ofReal (Real.exp (-(eps^2/2))) +
      (1-((1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1))))^T =
      ENNReal.ofReal (2 * (q * Real.exp (-(eps^2/2)) + (1-q))^T) := by
    simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_pow hbase,
      ENNReal.ofReal_add (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1),
      ENNReal.ofReal_mul hq0, ENNReal.ofReal_sub 1 hq0, ENNReal.ofReal_one,
      q, ofReal_explorationProbReal n k hk]
  calc
    _ ≤ _ := meanBadEvent_count_bound hk nu hb i a eps heps0
    _ = _ := hconv
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*q*eps^2/4)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (count_mixture_exp_bound q eps T hq0 hq1 heps0 heps1) (by norm_num)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left (explorationProbReal_lower n k hk hnk)
        (by positivity : 0 ≤ (T : ℝ)*eps^2/4)
      calc
        _ = -((T : ℝ)*eps^2/4*q) := by ring
        _ ≤ -((T : ℝ)*eps^2/4*(1/(4*k))) := neg_le_neg hmul
        _ = _ := by ring


def allMeanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  ⋃ i : Fin n, ⋃ a : Fin k, meanBadEvent nu i a eps

theorem allMeanBadEvent_exponential_bound {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw hk nu (allMeanBadEvent (n := n) (T := T) nu eps) ≤
      ENNReal.ofReal (2 * (k : ℝ)^2 * Real.exp (-(T : ℝ)*eps^2/(16*k))) := by
  let M := explorationRewardLaw (n := n) (T := T) hk nu
  let B := ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*eps^2/(16*k)))
  have hnkE : (n : ℝ≥0∞) ≤ k := by exact_mod_cast hnk
  calc
    _ ≤ ∑ i : Fin n, M (⋃ a : Fin k, meanBadEvent nu i a eps) := by
      simpa only [tsum_fintype] using (measure_iUnion_le (μ := M)
        (fun i : Fin n => ⋃ a : Fin k, meanBadEvent nu i a eps))
    _ ≤ ∑ i : Fin n, ∑ a : Fin k, M (meanBadEvent nu i a eps) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [tsum_fintype] using (measure_iUnion_le (μ := M) (fun a : Fin k => meanBadEvent nu i a eps))
    _ ≤ ∑ _i : Fin n, ∑ _a : Fin k, B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro a _
      exact meanBadEvent_exponential_bound hk hnk nu hb i a eps heps0 heps1
    _ = (n : ℝ≥0∞) * (k : ℝ≥0∞) * B := by simp [mul_assoc]
    _ ≤ (k : ℝ≥0∞) * (k : ℝ≥0∞) * B := by gcongr
    _ = _ := by
      simp only [B, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2*(k : ℝ)^2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_pow (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      ring

theorem mean_exploration_threshold (k T : ℕ) (hk : 0 < k) (eps delta : ℝ)
    (heps : 0 < eps) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    2*(k : ℝ)^2 * Real.exp (-(T : ℝ)*eps^2/(16*k)) ≤ delta/2 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log (4*(k : ℝ)^2/delta) ≤ (T : ℝ)*eps^2/(16*k) := by
    have hmul := mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ eps^2/(16*(k : ℝ)))
    have he : ((16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta)) * (eps^2/(16*(k : ℝ))) =
        Real.log (4*(k : ℝ)^2/delta) := by field_simp
    rw [he] at hmul
    simpa only [mul_div_assoc] using hmul
  calc
    _ ≤ 2*(k : ℝ)^2 * Real.exp (-Real.log (4*(k : ℝ)^2/delta)) := by
      gcongr
      convert neg_le_neg hlog using 1
      ring
    _ = delta/2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
      ring

theorem allMeanBadEvent_le_half_delta {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    explorationRewardLaw hk nu (allMeanBadEvent (n := n) (T := T) nu eps) ≤
      ENNReal.ofReal (delta/2) := by
  exact (allMeanBadEvent_exponential_bound hk hnk nu hb eps heps.le heps1).trans
    (ENNReal.ofReal_le_ofReal (mean_exploration_threshold k T hk eps delta heps hdelta hT))



def allMeanAccurate {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | ∀ i : Fin n, ∀ a : Fin k,
    |localEmpiricalMean (explorationFeedback z.1 z.2 i) a - armMean nu a| < eps/2}

theorem allMeanAccurate_eq_compl {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    allMeanAccurate (n := n) (T := T) nu eps = (allMeanBadEvent nu eps)ᶜ := by
  ext z
  simp [allMeanAccurate, allMeanBadEvent, meanBadEvent]

theorem allMeanAccurate_probability {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    1 - ENNReal.ofReal (delta/2) ≤
      explorationRewardLaw hk nu (allMeanAccurate (n := n) (T := T) nu eps) := by
  have hm : MeasurableSet (allMeanBadEvent (n := n) (T := T) nu eps) :=
    MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun a => measurableSet_meanBadEvent nu i a eps))
  rw [allMeanAccurate_eq_compl, measure_compl hm (by finiteness), measure_univ]
  exact tsub_le_tsub_left (allMeanBadEvent_le_half_delta hk hnk nu hb eps delta heps heps1 hdelta hT) 1

namespace RewardCanary

noncomputable def unitUniform : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform := by
  constructor
  norm_num [unitUniform, Measure.restrict_apply_univ]

theorem unitUniform_bounded : ∀ᵐ y ∂unitUniform, y ∈ Set.Icc (0 : ℝ) 1 := by
  exact ae_restrict_mem measurableSet_Icc

theorem continuous_reward_tail (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw (n := 2) (T := 2) (by decide) (fun _ : Fin 3 => unitUniform)
      (meanBadEvent (fun _ : Fin 3 => unitUniform) (0 : Fin 2) (0 : Fin 3) eps) ≤
      ENNReal.ofReal (2 * Real.exp (-eps^2/24)) := by
  have h := meanBadEvent_exponential_bound (n := 2) (T := 2) (k := 3) (by decide) (by decide)
    (fun _ => unitUniform) (fun _ => unitUniform_bounded) (0 : Fin 2) (0 : Fin 3) eps heps0 heps1
  convert h using 1
  congr 3
  norm_num
  ring

theorem selected_single_value (r : Fin 2 → Fin 3 → ℝ) :
    selectedMean ({1} : Finset (Fin 2)) (0 : Fin 3) r = r 1 0 := by
  simp [selectedMean]

theorem selected_empty_zero (r : Fin 2 → Fin 3 → ℝ) :
    selectedMean (∅ : Finset (Fin 2)) (0 : Fin 3) r = 0 := by
  simp [selectedMean]

end RewardCanary
end BanditRLProof.MusicalChairs

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

namespace CollisionCanary

theorem two_players_three_arms_mean : collisionProbReal 2 3 = 1/3 := by
  norm_num [collisionProbReal]

theorem mixed_local_rate (r : Fin 2 → Fin 3 → ℝ) :
    localCollisionRate ExplorationCanary.mixedDraws r (0 : Fin 2) = 1/2 := by
  rw [localCollisionRate_eq, ExplorationCanary.mixed_counts.2]
  norm_num

theorem informative_tail :
    (explorationLaw 2 3 9000 (by decide)).toMeasure
      (collisionBadEvent (k := 3) (T := 9000) (0 : Fin 2)) ≤ ENNReal.ofReal (1/10 : ℝ) := by
  have h := collisionBadEvent_bound (n := 2) (k := 3) (T := 9000) (by decide) (by decide) (0 : Fin 2)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  norm_num
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos (20 : ℝ))]
  have he := Real.add_one_le_exp (20 : ℝ)
  linarith

end CollisionCanary
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

namespace BanditRLProof.MusicalChairs.PopulationCanary

theorem exact_mean_recovers_two : populationEstimate 3 30 10 = 2 := by
  apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  norm_num [collisionProbReal]

theorem lower_margin_recovers_two : populationEstimate 3 30 9 = 2 := by
  apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  norm_num [collisionProbReal]

theorem upper_margin_recovers_two : populationEstimate 3 30 11 = 2 := by
  apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  norm_num [collisionProbReal]

theorem zero_collision_returns_one : populationEstimate 3 30 0 = 1 :=
  populationEstimate_zero_collision (by decide) (by decide)

theorem all_collision_returns_cap : populationEstimate 3 30 30 = 3 :=
  populationEstimate_all_collision 3 30

def draws : Fin 3 → Fin 2 → Fin 3 := fun t i =>
  if t = 0 then 0 else if i = 0 then 0 else 1

theorem actual_collision_count : collisionCount (0 : Fin 2) draws = 1 := by
  norm_num [collisionCount, FinitePMF.eventCount, draws, CollisionFree, Fin.forall_fin_two,
    Finset.filter_eq']

theorem actual_local_estimate (r : Fin 3 → Fin 3 → ℝ) :
    localPopulationEstimate (explorationFeedback draws r (0 : Fin 2)) = 2 := by
  rw [localPopulationEstimate_eq, actual_collision_count]
  apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  norm_num [collisionProbReal]

end BanditRLProof.MusicalChairs.PopulationCanary
