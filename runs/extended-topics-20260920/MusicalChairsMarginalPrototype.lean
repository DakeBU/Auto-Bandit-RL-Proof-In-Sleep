import Mathlib.Probability.ProbabilityMassFunction.Integrals
import BanditRLProof.Algorithms.MusicalChairsCoordinationRegret
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Data.Finset.Sort
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

namespace BanditRLProof.MusicalChairs

def scoreOrder {k : ℕ} (score : Fin k → ℝ) (a b : Fin k) : Prop :=
  score b < score a ∨ score a = score b ∧ a ≤ b

noncomputable instance scoreOrder_decidable {k : ℕ} (score : Fin k → ℝ) :
    DecidableRel (scoreOrder score) := fun _ _ => Classical.propDecidable _

instance scoreOrder_trans {k : ℕ} (score : Fin k → ℝ) : IsTrans (Fin k) (scoreOrder score) := by
  constructor
  intro a b c hab hbc
  rcases hab with hab | ⟨hab,hab'⟩ <;> rcases hbc with hbc | ⟨hbc,hbc'⟩
  · exact Or.inl (lt_trans hbc hab)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨hab.trans hbc,le_trans hab' hbc'⟩

instance scoreOrder_antisymm {k : ℕ} (score : Fin k → ℝ) : Std.Antisymm (scoreOrder score) := by
  constructor
  intro a b hab hba
  rcases hab with hab | ⟨hab,hab'⟩ <;> rcases hba with hba | ⟨hba,hba'⟩
  · linarith
  · linarith
  · linarith
  · exact le_antisymm hab' hba'

instance scoreOrder_total {k : ℕ} (score : Fin k → ℝ) : Std.Total (scoreOrder score) := by
  constructor
  intro a b
  rcases lt_trichotomy (score a) (score b) with h | h | h
  · exact Or.inr (Or.inl h)
  · rcases le_total a b with hab | hba
    · exact Or.inl (Or.inr ⟨h,hab⟩)
    · exact Or.inr (Or.inr ⟨h.symm,hba⟩)
  · exact Or.inl (Or.inl h)

noncomputable def rankedArms {k : ℕ} (score : Fin k → ℝ) : List (Fin k) :=
  Finset.univ.sort (scoreOrder score)

noncomputable def topArms {k : ℕ} (score : Fin k → ℝ) (n : ℕ) : Finset (Fin k) :=
  ((rankedArms score).take n).toFinset

theorem topArms_card {k : ℕ} (score : Fin k → ℝ) (n : ℕ) :
    (topArms score n).card = min n k := by
  unfold topArms
  rw [List.toFinset_card_of_nodup]
  · simp [rankedArms]
  · exact (List.take_sublist n (rankedArms score)).nodup (Finset.sort_nodup _ _)

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem topArms_before_unselected {k : ℕ} (score : Fin k → ℝ) (n : ℕ)
    {a b : Fin k} (ha : a ∈ topArms score n) (hb : b ∉ topArms score n) :
    scoreOrder score a b := by
  have hs := Finset.pairwise_sort (Finset.univ : Finset (Fin k)) (scoreOrder score)
  change (rankedArms score).Pairwise (scoreOrder score) at hs
  rw [← List.take_append_drop n (rankedArms score), List.pairwise_append] at hs
  have hbl : b ∈ rankedArms score := by simp [rankedArms]
  rw [← List.take_append_drop n (rankedArms score), List.mem_append] at hbl
  have hbt : b ∉ (rankedArms score).take n := by simpa [topArms] using hb
  exact hs.2.2 a (by simpa [topArms] using ha) b (hbl.resolve_left hbt)

theorem topArms_eq_of_order_separated {k : ℕ} (score : Fin k → ℝ) (n : ℕ)
    (S : Finset (Fin k)) (hcard : S.card = n) (hnk : n ≤ k)
    (hsep : ∀ a ∈ S, ∀ b ∉ S, scoreOrder score a b) : topArms score n = S := by
  have hc : (topArms score n).card = S.card := by rw [topArms_card, min_eq_left hnk, hcard]
  apply Finset.eq_of_subset_of_card_le _ hc.ge
  intro b hb
  by_contra hbS
  have hsub : S ⊆ topArms score n := by
    intro a ha
    by_contra hat
    have hab := hsep a ha b hbS
    have hba := topArms_before_unselected score n hb hat
    have he : a = b := antisymm_of (scoreOrder score) hab hba
    exact hbS (he ▸ ha)
  have heq := Finset.eq_of_subset_of_card_le hsub hc.le
  exact hbS (heq.symm ▸ hb)

theorem topArms_eq_of_strict_separation {k : ℕ} (score : Fin k → ℝ) (n : ℕ)
    (S : Finset (Fin k)) (hcard : S.card = n) (hnk : n ≤ k)
    (hsep : ∀ a ∈ S, ∀ b ∉ S, score b < score a) : topArms score n = S :=
  topArms_eq_of_order_separated score n S hcard hnk (fun a ha b hb => Or.inl (hsep a ha b hb))

theorem topArms_eq_iff {k : ℕ} (score : Fin k → ℝ) (n : ℕ) (hnk : n ≤ k)
    (S : Finset (Fin k)) : topArms score n = S ↔
      S.card = n ∧ ∀ a ∈ S, ∀ b ∉ S, scoreOrder score a b := by
  constructor
  · intro h
    subst S
    exact ⟨by rw [topArms_card, min_eq_left hnk], fun _ ha _ hb =>
      topArms_before_unselected score n ha hb⟩
  · rintro ⟨hc,hs⟩
    exact topArms_eq_of_order_separated score n S hc hnk hs

theorem populationEstimate_pos {k T C : ℕ} (hk : 1 < k) (hC : C ≤ T) :
    0 < populationEstimate k T C := by
  by_cases he : C = T
  · simp [populationEstimate, he, show 0 < k by omega]
  · have hCt : C < T := lt_of_le_of_ne hC he
    have hr : (1 : ℤ) ≤ round (populationInverse k T C) := by
      rw [round_eq]
      apply Int.le_floor.mpr
      have hi := populationInverse_ge_one hk hCt
      norm_num
      linarith
    have hn : 1 ≤ (round (populationInverse k T C)).toNat := by
      simpa using Int.toNat_le_toNat hr
    simp only [populationEstimate, if_neg he, lt_min_iff]
    exact ⟨by omega, by omega⟩

noncomputable def localCandidateSet {k T : ℕ} (f : Fin T → ExplorationFeedback k) : Finset (Fin k) :=
  topArms (localEmpiricalMean f) (localPopulationEstimate f)

theorem localCandidateSet_card {k T : ℕ} (f : Fin T → ExplorationFeedback k) :
    (localCandidateSet f).card = localPopulationEstimate f := by
  rw [localCandidateSet, topArms_card, min_eq_left]
  exact populationEstimate_le k T (localCollisionCount f)

theorem localCandidateSet_nonempty {k T : ℕ} (hk : 1 < k) (f : Fin T → ExplorationFeedback k) :
    (localCandidateSet f).Nonempty := by
  rw [← Finset.card_pos, localCandidateSet_card]
  exact populationEstimate_pos hk (localCollisionCount_le f)

theorem empirical_strict_separation {k : ℕ} (mu score : Fin k → ℝ)
    (S : Finset (Fin k)) (eps gap : ℝ) (hepsgap : eps < gap)
    (hgap : ∀ a ∈ S, ∀ b ∉ S, gap ≤ mu a - mu b)
    (hacc : ∀ a, |score a-mu a| < eps/2) :
    ∀ a ∈ S, ∀ b ∉ S, score b < score a := by
  intro a ha b hb
  have h1 := (abs_lt.mp (hacc a)).1
  have h2 := (abs_lt.mp (hacc b)).2
  have hg := hgap a ha b hb
  linarith

theorem localCandidateSet_correct {n k T : ℕ} (f : Fin T → ExplorationFeedback k)
    (mu : Fin k → ℝ) (S : Finset (Fin k)) (hcard : S.card = n) (hnk : n ≤ k)
    (eps gap : ℝ) (hepsgap : eps < gap)
    (hgap : ∀ a ∈ S, ∀ b ∉ S, gap ≤ mu a - mu b)
    (hacc : ∀ a, |localEmpiricalMean f a-mu a| < eps/2)
    (hpop : localPopulationEstimate f = n) : localCandidateSet f = S := by
  rw [localCandidateSet, hpop]
  exact topArms_eq_of_strict_separation _ n S hcard hnk
    (empirical_strict_separation mu (localEmpiricalMean f) S eps gap hepsgap hgap hacc)

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem localCandidateSet_eq_iff {k T : ℕ} (f : Fin T → ExplorationFeedback k)
    (S : Finset (Fin k)) : localCandidateSet f = S ↔ S.card = localPopulationEstimate f ∧
      ∀ a ∈ S, ∀ b ∉ S, scoreOrder (localEmpiricalMean f) a b :=
  topArms_eq_iff _ _ (populationEstimate_le k T (localCollisionCount f)) S

theorem measurableSet_localScoreOrder {n k T : ℕ} (i : Fin n) (a b : Fin k) :
    MeasurableSet {z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ) |
      scoreOrder (localEmpiricalMean (explorationFeedback z.1 z.2 i)) a b} := by
  by_cases hab : a ≤ b
  · simp only [scoreOrder, hab, and_true]
    exact (measurableSet_lt (measurable_jointEmpiricalMean i b)
      (measurable_jointEmpiricalMean i a)).union
        (measurableSet_eq_fun (measurable_jointEmpiricalMean i a) (measurable_jointEmpiricalMean i b))
  · simp only [scoreOrder, hab, and_false, or_false]
    exact measurableSet_lt (measurable_jointEmpiricalMean i b) (measurable_jointEmpiricalMean i a)

def explorationGoodEvent {n k T : ℕ} (S : Finset (Fin k)) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | ∀ i : Fin n, localPopulationEstimate (explorationFeedback z.1 z.2 i) = n ∧
    localCandidateSet (explorationFeedback z.1 z.2 i) = S}

theorem explorationGoodEvent_eq_comparisons {n k T : ℕ} (S : Finset (Fin k))
    (hcard : S.card = n) : explorationGoodEvent (n := n) (T := T) S =
      (Prod.fst ⁻¹' populationRecovered) ∩
        {z | ∀ i : Fin n, ∀ a ∈ S, ∀ b ∉ S,
          scoreOrder (localEmpiricalMean (explorationFeedback z.1 z.2 i)) a b} := by
  ext z
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · intro i
      simpa only [localPopulationEstimate_eq] using (hz i).1
    · intro i
      exact (localCandidateSet_eq_iff _ S).mp (hz i).2 |>.2
  · rintro ⟨hp,hs⟩ i
    have hi : localPopulationEstimate (explorationFeedback z.1 z.2 i) = n := by
      simpa only [localPopulationEstimate_eq] using hp i
    exact ⟨hi, (localCandidateSet_eq_iff _ S).mpr ⟨hcard.trans hi.symm, hs i⟩⟩

theorem measurableSet_explorationGoodEvent {n k T : ℕ} (S : Finset (Fin k))
    (hcard : S.card = n) : MeasurableSet (explorationGoodEvent (n := n) (T := T) S) := by
  rw [explorationGoodEvent_eq_comparisons S hcard]
  apply MeasurableSet.inter ((Set.toFinite _).measurableSet.preimage measurable_fst)
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun a =>
    MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun b =>
      MeasurableSet.iInter (fun _ => measurableSet_localScoreOrder i a b)))))

theorem explorationEstimatesCorrect_subset_goodEvent {n k T : ℕ}
    (nu : Fin k → Measure ℝ) (S : Finset (Fin k)) (hcard : S.card = n) (hnk : n ≤ k)
    (eps gap : ℝ) (hepsgap : eps < gap)
    (hgap : ∀ a ∈ S, ∀ b ∉ S, gap ≤ armMean nu a - armMean nu b) :
    explorationEstimatesCorrect (n := n) (T := T) nu eps ⊆ explorationGoodEvent S := by
  intro z hz i
  exact ⟨hz.2 i, localCandidateSet_correct _ (armMean nu) S hcard hnk eps gap hepsgap hgap
    (hz.1 i) (hz.2 i)⟩

noncomputable def trueTopArms {k : ℕ} (nu : Fin k → Measure ℝ) (n : ℕ) : Finset (Fin k) :=
  topArms (armMean nu) n

theorem trueTopArms_eq_of_gap {n k : ℕ} (nu : Fin k → Measure ℝ)
    (S : Finset (Fin k)) (hcard : S.card = n) (hnk : n ≤ k) (gap : ℝ) (hgap0 : 0 < gap)
    (hgap : ∀ a ∈ S, ∀ b ∉ S, gap ≤ armMean nu a - armMean nu b) : trueTopArms nu n = S := by
  apply topArms_eq_of_strict_separation _ n S hcard hnk
  intro a ha b hb
  have h := hgap a ha b hb
  linarith

theorem explorationGoodEvent_probability {n k : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k)) (hcard : S.card = n)
    (eps gap delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hepsgap : eps < gap)
    (hgap : ∀ a ∈ S, ∀ b ∉ S, gap ≤ armMean nu a - armMean nu b)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - ENNReal.ofReal delta ≤ explorationRewardLaw (by omega) nu
      (explorationGoodEvent (n := n) (T := explorationLength k eps delta) S) :=
  (explorationEstimatesCorrect_probability hn (by omega) hnk.le nu hb eps delta heps heps1
    hdelta hdelta1).trans (measure_mono
      (explorationEstimatesCorrect_subset_goodEvent nu S hcard hnk.le eps gap hepsgap hgap))

theorem explorationGoodEvent_trueTop_probability {n k : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k)) (hcard : S.card = n)
    (eps gap delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hepsgap : eps < gap)
    (hgap : ∀ a ∈ S, ∀ b ∉ S, gap ≤ armMean nu a - armMean nu b)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - ENNReal.ofReal delta ≤ explorationRewardLaw (by omega) nu
      (explorationGoodEvent (n := n) (T := explorationLength k eps delta) (trueTopArms nu n)) := by
  rw [trueTopArms_eq_of_gap nu S hcard hnk.le gap (heps.trans hepsgap) hgap]
  exact explorationGoodEvent_probability hn hnk nu hb S hcard eps gap delta heps heps1 hepsgap hgap
    hdelta hdelta1

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem armMean_mem_unitInterval {k : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (a : Fin k) :
    armMean nu a ∈ Set.Icc (0 : ℝ) 1 := by
  have hi : Integrable (fun y : ℝ => y) (nu a) :=
    Integrable.of_bound measurable_id.aestronglyMeasurable 1
      ((hb a).mono (fun y hy => by simpa [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2))
  constructor
  · exact integral_nonneg_of_ae ((hb a).mono (fun _ hy => hy.1))
  · have h := integral_mono_ae hi (integrable_const (1 : ℝ)) ((hb a).mono (fun _ hy => hy.2))
    simpa [armMean] using h

theorem separating_gap_le_one {n k : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k)) (hcard : S.card = n) (gap : ℝ)
    (hgap : ∀ a ∈ S, ∀ b ∉ S, gap ≤ armMean nu a - armMean nu b) : gap ≤ 1 := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨b,_,hbS⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show S.card < (Finset.univ : Finset (Fin k)).card by simpa [hcard])
  have hg := hgap a ha b hbS
  have hua := (armMean_mem_unitInterval nu hb a).2
  have hlb := (armMean_mem_unitInterval nu hb b).1
  linarith

theorem source_exploration_good_probability {n k : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k)) (hcard : S.card = n)
    (eps gap delta : ℝ) (heps : 0 < eps) (hepsgap : eps < gap)
    (hgap : ∀ a ∈ S, ∀ b ∉ S, gap ≤ armMean nu a - armMean nu b)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - ENNReal.ofReal delta ≤ explorationRewardLaw (by omega) nu
      (explorationGoodEvent (n := n) (T := explorationLength k eps delta) (trueTopArms nu n)) :=
  explorationGoodEvent_trueTop_probability hn hnk nu hb S hcard eps gap delta heps
    (hepsgap.le.trans (separating_gap_le_one hn hnk nu hb S hcard gap hgap)) hepsgap hgap hdelta hdelta1

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs.RankingCanary

noncomputable def scrambledScores (a : Fin 3) : ℝ := if a = 0 then 1/2 else if a = 1 then 3/4 else 1/4

noncomputable def tiedScores (a : Fin 3) : ℝ := if a = 2 then 1/4 else 3/4

theorem scrambled_sort : rankedArms scrambledScores = [1,0,2] := by
  have hu : ([1,0,2] : List (Fin 3)).toFinset = Finset.univ := by decide
  unfold rankedArms
  rw [← hu]
  apply (List.toFinset_sort (r := scoreOrder scrambledScores) (by decide)).2
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [List.pairwise_cons, scoreOrder, scrambledScores, h20,h21,h20.symm,h21.symm]

theorem tie_sort : rankedArms tiedScores = [0,1,2] := by
  have hu : ([0,1,2] : List (Fin 3)).toFinset = Finset.univ := by decide
  unfold rankedArms
  rw [← hu]
  apply (List.toFinset_sort (r := scoreOrder tiedScores) (by decide)).2
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [List.pairwise_cons, scoreOrder, tiedScores, h20,h21,h20.symm,h21.symm]

theorem scrambled_candidates : topArms scrambledScores 2 = {0,1} := by
  simp [topArms, scrambled_sort, Finset.pair_comm]

theorem zero_request_empty : topArms scrambledScores 0 = ∅ := by
  simp [topArms]

theorem large_request_all : topArms scrambledScores 7 = Finset.univ := by
  rw [topArms, scrambled_sort]
  decide

noncomputable def allCollisionFeedback : Fin 2 → ExplorationFeedback 3 :=
  fun _ => ⟨0,true,0⟩

theorem all_collision_candidates : localCandidateSet allCollisionFeedback = Finset.univ := by
  have hpop : localPopulationEstimate allCollisionFeedback = 3 := by
    norm_num [localPopulationEstimate, localCollisionCount, allCollisionFeedback,
      populationEstimate]
  have hc := localCandidateSet_card allCollisionFeedback
  rw [hpop] at hc
  exact Finset.eq_univ_of_card _ (by simpa using hc)

end BanditRLProof.MusicalChairs.RankingCanary

namespace BanditRLProof.MusicalChairs.RankingCanary

def oneObservedScore (j a : Fin 3) : ℝ := if a = j then 1 else 0

theorem actual_player_zero_scores :
    localEmpiricalMean (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (0 : Fin 2)) =
      oneObservedScore 0 := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  funext a
  fin_cases a <;>
    norm_num [localEmpiricalMean, localObservationCount_eq, localRewardSum_eq,
      observationCount, FinitePMF.eventCount, observes, PopulationCanary.draws,
      CollisionFree, Fin.forall_fin_two, hu, oneObservedScore]

theorem actual_player_one_scores :
    localEmpiricalMean (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (1 : Fin 2)) =
      oneObservedScore 1 := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  funext a
  fin_cases a <;>
    norm_num [localEmpiricalMean, localObservationCount_eq, localRewardSum_eq,
      observationCount, FinitePMF.eventCount, observes, PopulationCanary.draws,
      CollisionFree, Fin.forall_fin_two, hu, oneObservedScore]

theorem actual_same_candidates :
    localCandidateSet (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (0 : Fin 2)) = {0,1} ∧
    localCandidateSet (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (1 : Fin 2)) = {0,1} := by
  have hc1 : collisionCount (1 : Fin 2) PopulationCanary.draws = 1 := by
    norm_num [collisionCount, FinitePMF.eventCount, PopulationCanary.draws, CollisionFree,
      Fin.forall_fin_two, Finset.filter_eq']
  have hp1 : localPopulationEstimate
      (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (1 : Fin 2)) = 2 := by
    rw [localPopulationEstimate_eq, hc1]
    apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    norm_num [collisionProbReal]
  constructor
  · rw [localCandidateSet, PopulationCanary.actual_local_estimate, actual_player_zero_scores]
    apply topArms_eq_of_order_separated _ 2 _ (by decide) (by decide)
    intro a ha b hb
    fin_cases a <;> fin_cases b <;> simp_all [oneObservedScore,scoreOrder]
  · rw [localCandidateSet, hp1, actual_player_one_scores]
    apply topArms_eq_of_order_separated _ 2 _ (by decide) (by decide)
    intro a ha b hb
    fin_cases a <;> fin_cases b <;> simp_all [oneObservedScore,scoreOrder]

end BanditRLProof.MusicalChairs.RankingCanary

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def rankedArm {k : ℕ} (score : Fin k → ℝ) (j : Fin k) : Fin k :=
  (rankedArms score).get ⟨j.val, by simp [rankedArms]⟩

noncomputable def rankIndex {k : ℕ} (score : Fin k → ℝ) (a : Fin k) : Fin k :=
  ⟨(rankedArms score).idxOf a, by
    have hm : a ∈ rankedArms score := by simp [rankedArms]
    have h := List.idxOf_lt_length_iff.mpr hm
    simpa [rankedArms] using h⟩

theorem rankedArm_rankIndex {k : ℕ} (score : Fin k → ℝ) (a : Fin k) :
    rankedArm score (rankIndex score a) = a := by
  unfold rankedArm rankIndex
  exact List.getElem_idxOf _

theorem rankIndex_rankedArm {k : ℕ} (score : Fin k → ℝ) (j : Fin k) :
    rankIndex score (rankedArm score j) = j := by
  apply Fin.ext
  exact List.get_idxOf (Finset.sort_nodup _ _) _

theorem mem_topArms_iff_rankIndex {k : ℕ} (score : Fin k → ℝ) (n : ℕ) (a : Fin k) :
    a ∈ topArms score n ↔ (rankIndex score a).val < n := by
  have hm : a ∈ rankedArms score := by simp [rankedArms]
  simpa only [topArms, List.mem_toFinset, rankIndex] using List.mem_take_iff_idxOf_lt (n := n) hm

theorem ranked_score_antitone {k : ℕ} (score : Fin k → ℝ) {i j : Fin k} (hij : i ≤ j) :
    score (rankedArm score j) ≤ score (rankedArm score i) := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · have h := (Finset.pairwise_sort (Finset.univ : Finset (Fin k)) (scoreOrder score)).rel_get_of_lt
      (a := ⟨i.val, by simp⟩)
      (b := ⟨j.val, by simp⟩) hlt
    rcases h with h | ⟨h,_⟩
    · exact h.le
    · exact h.ge
  · subst j
    rfl

noncomputable def boundaryGap {k : ℕ} (score : Fin k → ℝ) (n : ℕ)
    (hn : 0 < n) (hnk : n < k) : ℝ :=
  score (rankedArm score ⟨n-1, by omega⟩) - score (rankedArm score ⟨n,hnk⟩)

theorem boundaryGap_nonneg {k : ℕ} (score : Fin k → ℝ) (n : ℕ)
    (hn : 0 < n) (hnk : n < k) : 0 ≤ boundaryGap score n hn hnk := by
  exact sub_nonneg.mpr (ranked_score_antitone score (i := ⟨n-1,by omega⟩) (j := ⟨n,hnk⟩)
    (by show n-1 ≤ n; omega))

theorem boundaryGap_separates {k : ℕ} (score : Fin k → ℝ) (n : ℕ)
    (hn : 0 < n) (hnk : n < k) :
    ∀ a ∈ topArms score n, ∀ b ∉ topArms score n,
      boundaryGap score n hn hnk ≤ score a - score b := by
  intro a ha b hb
  have ha' := (mem_topArms_iff_rankIndex score n a).mp ha
  have hb' : n ≤ (rankIndex score b).val := by
    have h := (mem_topArms_iff_rankIndex score n b).not.mp hb
    omega
  have hleft := ranked_score_antitone score (i := rankIndex score a)
    (j := ⟨n-1,by omega⟩) (by show (rankIndex score a).val ≤ n-1; omega)
  have hright := ranked_score_antitone score (i := ⟨n,hnk⟩)
    (j := rankIndex score b) hb'
  rw [rankedArm_rankIndex] at hleft hright
  unfold boundaryGap
  linarith

theorem explorationGoodEvent_orderStatistic_probability {n k : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - ENNReal.ofReal delta ≤ explorationRewardLaw (by omega) nu
      (explorationGoodEvent (n := n) (T := explorationLength k eps delta) (trueTopArms nu n)) := by
  apply source_exploration_good_probability hn hnk nu hb (trueTopArms nu n)
    (by simp [trueTopArms, topArms_card, min_eq_left hnk.le])
    eps (boundaryGap (armMean nu) n hn hnk) delta heps hepsgap
    (boundaryGap_separates (armMean nu) n hn hnk) hdelta hdelta1

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem measurableSet_actualCandidate_eq {n k T : ℕ} (i : Fin n) (S : Finset (Fin k)) :
    MeasurableSet {z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ) |
      localCandidateSet (explorationFeedback z.1 z.2 i) = S} := by
  have he : {z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ) |
      localCandidateSet (explorationFeedback z.1 z.2 i) = S} =
      (Prod.fst ⁻¹' {x : Fin T → Fin n → Fin k | S.card = populationEstimate k T (collisionCount i x)}) ∩
        {z | ∀ a ∈ S, ∀ b ∉ S,
          scoreOrder (localEmpiricalMean (explorationFeedback z.1 z.2 i)) a b} := by
    ext z
    simp [localCandidateSet_eq_iff, localPopulationEstimate_eq]
  rw [he]
  apply MeasurableSet.inter ((Set.toFinite _).measurableSet.preimage measurable_fst)
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun b => MeasurableSet.iInter (fun _ => measurableSet_localScoreOrder i a b))))

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

def CandidateConfig (n k : ℕ) := {C : Fin n → Finset (Fin k) // ∀ i, (C i).Nonempty}

noncomputable instance candidateConfig_fintype (n k : ℕ) : Fintype (CandidateConfig n k) := by
  unfold CandidateConfig
  infer_instance

instance candidateConfig_measurableSpace (n k : ℕ) : MeasurableSpace (CandidateConfig n k) := ⊤

instance candidateConfig_measurableSingleton (n k : ℕ) : MeasurableSingletonClass (CandidateConfig n k) := by
  constructor
  intro C
  trivial

noncomputable def learnedConfig {n k T : ℕ} (hk : 1 < k)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) : CandidateConfig n k :=
  ⟨fun i => localCandidateSet (explorationFeedback z.1 z.2 i),
    fun i => localCandidateSet_nonempty hk (explorationFeedback z.1 z.2 i)⟩

theorem measurable_learnedConfig {n k T : ℕ} (hk : 1 < k) :
    Measurable (learnedConfig (n := n) (T := T) hk) := by
  apply measurable_to_countable'
  intro C
  have he : (learnedConfig (n := n) (T := T) hk) ⁻¹' {C} =
      ⋂ i : Fin n, {z | localCandidateSet (explorationFeedback z.1 z.2 i) = C.val i} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h i
      exact congrFun (congrArg Subtype.val h) i
    · intro h
      apply Subtype.ext
      funext i
      exact h i
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_actualCandidate_eq i (C.val i))

noncomputable def configDrawPathKernel (n k L : ℕ) :
    Kernel (CandidateConfig n k) (Fin L → Fin n → Fin k) :=
  Kernel.ofFunOfCountable (fun C => (FinitePMF.iid (jointDraw C.val C.property) L).toMeasure)

instance configDrawPathKernel_markov (n k L : ℕ) : IsMarkovKernel (configDrawPathKernel n k L) := by
  constructor
  intro C
  change IsProbabilityMeasure (FinitePMF.iid (jointDraw C.val C.property) L).toMeasure
  infer_instance

noncomputable def learnedDrawPathKernel {n k T : ℕ} (hk : 1 < k) (L : ℕ) :
    Kernel ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) (Fin L → Fin n → Fin k) :=
  (configDrawPathKernel n k L).comap (learnedConfig hk) (measurable_learnedConfig hk)

instance learnedDrawPathKernel_markov {n k T : ℕ} (hk : 1 < k) (L : ℕ) :
    IsMarkovKernel (learnedDrawPathKernel (n := n) (T := T) hk L) := by
  unfold learnedDrawPathKernel
  infer_instance

theorem learnedDrawPathKernel_apply {n k T L : ℕ} (hk : 1 < k)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :
    learnedDrawPathKernel hk L z =
      (FinitePMF.iid (jointDraw (learnedConfig hk z).val (learnedConfig hk z).property) L).toMeasure := rfl

theorem learnedDrawPathKernel_pi {n k T L : ℕ} (hk : 1 < k)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :
    learnedDrawPathKernel hk L z = Measure.pi (fun _ : Fin L =>
      (jointDraw (learnedConfig hk z).val (learnedConfig hk z).property).toMeasure) := by
  rw [learnedDrawPathKernel_apply, FinitePMF.iid_toMeasure_pi]

theorem learnedDrawPathKernel_time_independent {n k T L : ℕ} (hk : 1 < k)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :
    iIndepFun (fun t (draws : Fin L → Fin n → Fin k) => draws t) (learnedDrawPathKernel hk L z) := by
  rw [learnedDrawPathKernel_pi]
  apply iIndepFun_pi (Ω := fun _ : Fin L => Fin n → Fin k)
    (𝓧 := fun _ : Fin L => Fin n → Fin k)
    (μ := fun _ => (jointDraw (learnedConfig hk z).val (learnedConfig hk z).property).toMeasure)
    (X := fun _ x => x)
  intro t
  exact measurable_id.aemeasurable

noncomputable def commonConfig {n k : ℕ} (S : Finset (Fin k)) (hne : S.Nonempty) :
    CandidateConfig n k := ⟨fun _ => S,fun _ => hne⟩

theorem learnedConfig_eq_common_on_good {n k T : ℕ} (hk : 1 < k)
    (S : Finset (Fin k)) (hne : S.Nonempty)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))
    (hz : z ∈ explorationGoodEvent (n := n) S) : learnedConfig hk z = commonConfig S hne := by
  apply Subtype.ext
  funext i
  exact (hz i).2

theorem learnedDrawPathKernel_on_good {n k T L : ℕ} (hk : 1 < k)
    (S : Finset (Fin k)) (hne : S.Nonempty)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))
    (hz : z ∈ explorationGoodEvent (n := n) S) :
    learnedDrawPathKernel hk L z =
      (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L).toMeasure := by
  rw [learnedDrawPathKernel_apply, learnedConfig_eq_common_on_good hk S hne z hz]
  rfl

noncomputable def explorationContinuationLaw {n k T : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) (L : ℕ) :
    Measure (((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) × (Fin L → Fin n → Fin k)) :=
  (explorationRewardLaw (by omega) nu).compProd (learnedDrawPathKernel hk L)

instance explorationContinuationLaw_probability {n k T : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] (L : ℕ) :
    IsProbabilityMeasure (explorationContinuationLaw (n := n) (T := T) hk nu L) := by
  unfold explorationContinuationLaw
  infer_instance

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem explorationContinuationLaw_fst_event {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E) :
    explorationContinuationLaw hk nu L (Prod.fst ⁻¹' E) = explorationRewardLaw (by omega) nu E := by
  have he : (Prod.fst ⁻¹' E : Set (((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) ×
      (Fin L → Fin n → Fin k))) = E ×ˢ Set.univ := by ext z; simp
  rw [he, explorationContinuationLaw, Measure.compProd_apply_prod hE MeasurableSet.univ]
  simp

theorem explorationContinuationLaw_rectangle_on_good {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (S : Finset (Fin k)) (hne : S.Nonempty)
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) S) (B : Set (Fin L → Fin n → Fin k)) :
    explorationContinuationLaw hk nu L (E ×ˢ B) =
      explorationRewardLaw (by omega) nu E *
        (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L).toMeasure B := by
  rw [explorationContinuationLaw, Measure.compProd_apply_prod hE (Set.toFinite B).measurableSet]
  have he : ∀ᵐ z ∂(explorationRewardLaw (n := n) (T := T) (by omega) nu).restrict E,
      learnedDrawPathKernel hk L z B =
        (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L).toMeasure B :=
    (ae_restrict_mem hE).mono (fun z hz => by rw [learnedDrawPathKernel_on_good hk S hne z (hEG hz)])
  rw [lintegral_congr_ae he, lintegral_const, Measure.restrict_apply_univ]
  exact mul_comm _ _

theorem explorationContinuationLaw_good_probability {n k L : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - ENNReal.ofReal delta ≤ explorationContinuationLaw (by omega) nu L
      (Prod.fst ⁻¹' (explorationGoodEvent (n := n) (T := explorationLength k eps delta) (trueTopArms nu n))) := by
  rw [explorationContinuationLaw_fst_event _ _ _ (measurableSet_explorationGoodEvent _
    (by simp [trueTopArms,topArms_card,min_eq_left hnk.le]))]
  exact explorationGoodEvent_orderStatistic_probability hn hnk nu hb eps delta heps hepsgap hdelta hdelta1

theorem trajectory_eq_of_prefix {n k : ℕ} (d e : ℕ → Fin n → Fin k) (t : ℕ)
    (h : ∀ u < t, d u = e u) : trajectory d t = trajectory e t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trajectory, trajectory, ih (fun u hu => h u (by omega)), h t (by omega)]

noncomputable def extendedCoordinationDraws {n k L : ℕ} (hk : 0 < k)
    (d : Fin L → Fin n → Fin k) (t : ℕ) : Fin n → Fin k :=
  if ht : t < L then d ⟨t,ht⟩ else fun _ => ⟨0,hk⟩

noncomputable def continuationAction {n k L : ℕ} (hk : 0 < k)
    (d : Fin L → Fin n → Fin k) (t : Fin L) : Fin n → Fin k :=
  action (trajectory (extendedCoordinationDraws hk d) t.val) (d t)

theorem continuationAction_prefix {n k L : ℕ} (hk : 0 < k)
    (d e : Fin L → Fin n → Fin k) (t : Fin L)
    (h : ∀ u : Fin L, u ≤ t → d u = e u) : continuationAction hk d t = continuationAction hk e t := by
  have ht : trajectory (extendedCoordinationDraws hk d) t.val =
      trajectory (extendedCoordinationDraws hk e) t.val := by
    apply trajectory_eq_of_prefix
    intro u hu
    have huL : u < L := lt_trans hu t.isLt
    simp only [extendedCoordinationDraws, dif_pos huL]
    exact h ⟨u,huL⟩ (by show u ≤ t.val; omega)
  rw [continuationAction, continuationAction, ht, h t le_rfl]

theorem continuationAction_fixed_stays {n k L : ℕ} (hk : 0 < k)
    (d : Fin L → Fin n → Fin k) (t : Fin L) (i : Fin n) (a : Fin k)
    (hs : trajectory (extendedCoordinationDraws hk d) t.val i = some a) :
    continuationAction hk d t i = a := action_of_fixed _ _ i a hs

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem explorationGoodEvent_positive {n k : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    0 < explorationRewardLaw (by omega) nu
      (explorationGoodEvent (n := n) (T := explorationLength k eps delta) (trueTopArms nu n)) :=
  (tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr hdelta1)).trans_le
    (explorationGoodEvent_orderStatistic_probability hn hnk nu hb eps delta heps hepsgap hdelta hdelta1)

theorem explorationContinuationLaw_normalized_rectangle {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (S : Finset (Fin k)) (hne : S.Nonempty)
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) S)
    (hpos : 0 < explorationRewardLaw (by omega) nu E) (B : Set (Fin L → Fin n → Fin k)) :
    explorationContinuationLaw hk nu L (E ×ˢ B) /
      explorationContinuationLaw hk nu L (Prod.fst ⁻¹' E) =
      (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L).toMeasure B := by
  rw [explorationContinuationLaw_rectangle_on_good hk nu S hne E hE hEG,
    explorationContinuationLaw_fst_event hk nu E hE, mul_comm, ENNReal.mul_div_cancel_right
      (ne_of_gt hpos) (measure_ne_top _ _)]

namespace HandoffCanary

theorem scrambled_boundary_gap :
    boundaryGap RankingCanary.scrambledScores 2 (by decide) (by decide) = 1/4 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [boundaryGap,rankedArm,RankingCanary.scrambled_sort,RankingCanary.scrambledScores,h20,h21]

theorem within_top_tie_gap :
    boundaryGap RankingCanary.tiedScores 2 (by decide) (by decide) = 1/2 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [boundaryGap,rankedArm,RankingCanary.tie_sort,RankingCanary.tiedScores,h02,h12]

theorem constant_boundary_gap :
    boundaryGap (fun _ : Fin 3 => (1/2 : ℝ)) 2 (by decide) (by decide) = 0 := by
  simp [boundaryGap]

theorem learned_actual_config :
    learnedConfig (n := 2) (T := 3) (by decide)
      (PopulationCanary.draws, fun _ _ => (1 : ℝ)) =
      commonConfig ({0,1} : Finset (Fin 3)) (by simp) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · exact RankingCanary.actual_same_candidates.1
  · exact RankingCanary.actual_same_candidates.2

theorem actual_future_product (L : ℕ) :
    learnedDrawPathKernel (n := 2) (T := 3) (by decide) L
      (PopulationCanary.draws, fun _ _ => (1 : ℝ)) =
      (FinitePMF.iid (jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3))) (fun _ => by simp)) L).toMeasure := by
  rw [learnedDrawPathKernel_apply, learned_actual_config]
  rfl

def separatedDraws : Fin 2 → Fin 2 → Fin 3 := fun t i =>
  if t = 0 then (if i = 0 then 0 else 1) else 0

theorem actual_first_action : continuationAction (by decide) separatedDraws 0 = separatedDraws 0 := by
  funext i
  simp [continuationAction,trajectory,initial,action]

theorem actual_fixed_next_action : continuationAction (by decide) separatedDraws 1 = separatedDraws 0 := by
  funext i
  fin_cases i <;>
    norm_num [continuationAction,trajectory,extendedCoordinationDraws,initial,action,step,
      CollisionFree,separatedDraws,Fin.forall_fin_two]

end HandoffCanary
end BanditRLProof.MusicalChairs

namespace BanditRLProof.FinitePMF

theorem iid_sum_snoc {α : Type*} [Fintype α] (p : PMF α) (T : ℕ)
    (f : (Fin (T+1) → α) → ℝ≥0∞) :
    ∑ d, iid p (T+1) d * f d =
      ∑ x, iid p T x * ∑ a, p a * f (Fin.snoc x a) := by
  calc
    _ = ∑ z : α × (Fin T → α),
        iid p (T+1) (Fin.snoc z.2 z.1) * f (Fin.snoc z.2 z.1) := by
      exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T+1) => α))
        (fun z => iid p (T+1) (Fin.snoc z.2 z.1) * f (Fin.snoc z.2 z.1))
        (fun d => iid p (T+1) d * f d) (fun z => rfl)).symm
    _ = _ := by
      simp_rw [iid_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp_rw [Finset.mul_sum, mul_assoc]

theorem iid_snoc {α : Type*} [Fintype α] (p : PMF α) (T : ℕ) :
    iid p (T+1) = (iid p T).bind (fun x => p.map (Fin.snoc x)) := by
  classical
  ext d
  have h := iid_sum_snoc p T (fun x => if d = x then 1 else 0)
  simp [PMF.bind_apply, PMF.map_apply, tsum_fintype, mul_ite] at h ⊢
  refine h.trans (Finset.sum_congr rfl ?_)
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : d = Fin.snoc x a <;> simp [he]

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs

theorem trajectory_snoc_prefix {n k T : ℕ} (hk : 0 < k)
    (d : Fin T → Fin n → Fin k) (a : Fin n → Fin k) :
    trajectory (extendedCoordinationDraws hk (Fin.snoc d a)) T =
      trajectory (extendedCoordinationDraws hk d) T := by
  apply trajectory_eq_of_prefix
  intro u hu
  simp [extendedCoordinationDraws, hu, show u < T+1 by omega, Fin.snoc]

theorem trajectory_snoc_last {n k T : ℕ} (hk : 0 < k)
    (d : Fin T → Fin n → Fin k) (a : Fin n → Fin k) :
    trajectory (extendedCoordinationDraws hk (Fin.snoc d a)) (T+1) =
      step (trajectory (extendedCoordinationDraws hk d) T) a := by
  rw [trajectory, trajectory_snoc_prefix]
  congr 1
  simp only [extendedCoordinationDraws, dif_pos (Nat.lt_succ_self T)]
  change Fin.snoc (α := fun _ => Fin n → Fin k) d a (Fin.last T) = a
  simp

theorem iid_trajectory_stateLaw {n k : ℕ} (hk : 0 < k)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) (T : ℕ) :
    (FinitePMF.iid (jointDraw C hne) T).map
      (fun d => trajectory (extendedCoordinationDraws hk d) T) = stateLaw C hne T := by
  induction T with
  | zero =>
    simpa only [trajectory, stateLaw] using
      (PMF.map_const (FinitePMF.iid (jointDraw C hne) 0) (initial n k))
  | succ T ih =>
    rw [FinitePMF.iid_snoc, PMF.map_bind]
    simp_rw [PMF.map_comp, Function.comp_def, trajectory_snoc_last]
    rw [stateLaw, ← ih, PMF.bind_map]
    rfl

end BanditRLProof.MusicalChairs

namespace BanditRLProof.FinitePMF

theorem iid_take {α : Type*} [Fintype α] (p : PMF α) {T L : ℕ} (h : T ≤ L) :
    (iid p L).map (fun d t => d (Fin.castLE h t)) = iid p T := by
  induction L with
  | zero =>
    have hT : T = 0 := by omega
    subst T
    convert PMF.map_id (iid p 0) using 1
  | succ L ih =>
    by_cases heq : T = L+1
    · subst T
      convert PMF.map_id (iid p (L+1)) using 1
    · have hTL : T ≤ L := by omega
      rw [iid_snoc, PMF.map_bind]
      have he (d : Fin L → α) :
          (p.map (fun a : α => (Fin.snoc d a : Fin (L+1) → α))).map
            (fun (x : Fin (L+1) → α) (t : Fin T) => x (Fin.castLE h t)) =
            PMF.pure (fun t => d (Fin.castLE hTL t)) := by
        rw [PMF.map_comp]
        have hf : ((fun (x : Fin (L+1) → α) (t : Fin T) => x (Fin.castLE h t)) ∘
              (fun a : α => (Fin.snoc d a : Fin (L+1) → α))) =
            Function.const α (fun t => d (Fin.castLE hTL t)) := by
          funext a t
          have ht : Fin.castLE h t = (Fin.castLE hTL t).castSucc := by
            apply Fin.ext
            rfl
          simp only [Function.comp_apply, Function.const_apply, ht, Fin.snoc_castSucc]
        rw [hf, PMF.map_const]
      simp_rw [he]
      exact ih hTL

theorem sum_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑ b, p.map g b * f b = ∑ a, p a * f (g a) := by
  simp only [PMF.map_apply, tsum_fintype, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs

theorem trajectory_take {n k T L : ℕ} (hk : 0 < k) (h : T ≤ L)
    (d : Fin L → Fin n → Fin k) :
    trajectory (extendedCoordinationDraws hk d) T =
      trajectory (extendedCoordinationDraws hk (fun t => d (Fin.castLE h t))) T := by
  apply trajectory_eq_of_prefix
  intro u hu
  simp [extendedCoordinationDraws, hu, show u < L from lt_of_lt_of_le hu h]

theorem iid_trajectory_marginal {n k T L : ℕ} (hk : 0 < k) (h : T ≤ L)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) :
    (FinitePMF.iid (jointDraw C hne) L).map
      (fun d => trajectory (extendedCoordinationDraws hk d) T) = stateLaw C hne T := by
  simp_rw [trajectory_take hk h]
  change (FinitePMF.iid (jointDraw C hne) L).map
    ((fun d => trajectory (extendedCoordinationDraws hk d) T) ∘
      (fun d t => d (Fin.castLE h t))) = _
  rw [← PMF.map_comp, FinitePMF.iid_take]
  exact iid_trajectory_stateLaw hk C hne T

theorem iid_last_state_draw {n k T : ℕ} (hk : 0 < k)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) :
    (FinitePMF.iid (jointDraw C hne) (T+1)).map
      (fun d => (trajectory (extendedCoordinationDraws hk d) T, d (Fin.last T))) =
    (stateLaw C hne T).bind (fun s => (jointDraw C hne).map (fun a => (s,a))) := by
  rw [FinitePMF.iid_snoc, PMF.map_bind]
  simp_rw [PMF.map_comp, Function.comp_def, trajectory_snoc_prefix, Fin.snoc_last]
  rw [← iid_trajectory_stateLaw hk C hne T, PMF.bind_map]
  rfl

theorem iid_round_state_draw {n k L : ℕ} (hk : 0 < k) (t : Fin L)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) :
    (FinitePMF.iid (jointDraw C hne) L).map
      (fun d => (trajectory (extendedCoordinationDraws hk d) t.val, d t)) =
    (stateLaw C hne t.val).bind (fun s => (jointDraw C hne).map (fun a => (s,a))) := by
  let h : t.val+1 ≤ L := t.isLt
  have hf : (fun d : Fin L → Fin n → Fin k =>
      (trajectory (extendedCoordinationDraws hk d) t.val, d t)) =
    ((fun d : Fin (t.val+1) → Fin n → Fin k =>
      (trajectory (extendedCoordinationDraws hk d) t.val, d (Fin.last t.val))) ∘
        (fun d u => d (Fin.castLE h u))) := by
    funext d
    apply Prod.ext
    · apply trajectory_eq_of_prefix
      intro u hu
      simp [extendedCoordinationDraws, show u < t.val+1 by omega,
        show u < L from lt_trans hu t.isLt]
    · rfl
  rw [hf, ← PMF.map_comp, FinitePMF.iid_take]
  exact iid_last_state_draw hk C hne

end BanditRLProof.MusicalChairs

namespace BanditRLProof.FinitePMF

theorem sum_map_real {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    ∑ b, (p.map g b).toReal * f b = ∑ a, (p a).toReal * f (g a) := by
  have hb (b : β) : (p.map g b).toReal = ∑ a, if b = g a then (p a).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    · intro a _
      split_ifs <;> simp [PMF.apply_ne_top]
  simp_rw [hb, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem sum_bind_real {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    ∑ b, (p.bind q b).toReal * f b = ∑ a, (p a).toReal * ∑ b, (q a b).toReal * f b := by
  have hb (b : β) : (p.bind q b).toReal = ∑ a, (p a).toReal * (q a b).toReal := by
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp_rw [ENNReal.toReal_mul]
    · intro a _
      exact ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (q a) b)
  simp_rw [hb, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs

noncomputable def pathCoordinationRegret {n k L : ℕ} (hk : 0 < k)
    (S : Finset (Fin k)) (mu : Fin k → ℝ) (d : Fin L → Fin n → Fin k) : ℝ :=
  ∑ t : Fin L, roundPseudoRegret S mu
    (trajectory (extendedCoordinationDraws hk d) t.val) (d t)

theorem iid_round_regret_expectation {n k L : ℕ} (hk : 0 < k) (t : Fin L)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty)
    (S : Finset (Fin k)) (mu : Fin k → ℝ) :
    (∑ d, (FinitePMF.iid (jointDraw C hne) L d).toReal *
      roundPseudoRegret S mu (trajectory (extendedCoordinationDraws hk d) t.val) (d t)) =
    ∑ s, (stateLaw C hne t.val s).toReal *
      ∑ a, (jointDraw C hne a).toReal * roundPseudoRegret S mu s a := by
  rw [← FinitePMF.sum_map_real (FinitePMF.iid (jointDraw C hne) L)
    (fun d => (trajectory (extendedCoordinationDraws hk d) t.val,d t))
    (fun z => roundPseudoRegret S mu z.1 z.2), iid_round_state_draw,
    FinitePMF.sum_bind_real]
  simp_rw [FinitePMF.sum_map_real]

theorem iid_path_regret_expectation {n k L : ℕ} (hk : 0 < k)
    (S : Finset (Fin k)) (hne : S.Nonempty) (mu : Fin k → ℝ) :
    (∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L d).toReal *
      pathCoordinationRegret hk S mu d) =
    ∑ t ∈ Finset.range L, ∑ s,
      (stateLaw (fun _ : Fin n => S) (fun _ => hne) t s).toReal *
        ∑ a, (jointDraw (fun _ : Fin n => S) (fun _ => hne) a).toReal *
          roundPseudoRegret S mu s a := by
  simp only [pathCoordinationRegret, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro t _
  simpa only [Finset.mul_sum] using iid_round_regret_expectation hk t
    (fun _ : Fin n => S) (fun _ => hne) S mu

theorem iid_path_regret_le {n k L : ℕ} (hk : 0 < k)
    (S : Finset (Fin k)) (hne : S.Nonempty) (hcard : S.card = n)
    (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1) :
    (∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L d).toReal *
      pathCoordinationRegret hk S mu d) ≤ 8 * (n : ℝ)^2 := by
  rw [iid_path_regret_expectation]
  exact expectedCoordinationRegret_real_le S hne hcard mu hmu L

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

instance coordinationState_measurableSpace (n k : ℕ) : MeasurableSpace (State n k) := ⊤

instance coordinationState_measurableSingleton (n k : ℕ) : MeasurableSingletonClass (State n k) := by
  constructor
  intro s
  trivial

theorem learnedDrawPathKernel_state_marginal {n k T L t : ℕ} (hk : 1 < k) (ht : t ≤ L)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :
    (learnedDrawPathKernel hk L z).map
      (fun d => trajectory (extendedCoordinationDraws (by omega) d) t) =
    (stateLaw (learnedConfig hk z).val (learnedConfig hk z).property t).toMeasure := by
  rw [learnedDrawPathKernel_apply, PMF.toMeasure_map _ _ (measurable_of_countable _),
    iid_trajectory_marginal _ ht]

theorem learnedDrawPathKernel_round_marginal {n k T L : ℕ} (hk : 1 < k) (t : Fin L)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :
    (learnedDrawPathKernel hk L z).map
      (fun d => (trajectory (extendedCoordinationDraws (by omega) d) t.val, d t)) =
    ((stateLaw (learnedConfig hk z).val (learnedConfig hk z).property t.val).bind
      (fun s => (jointDraw (learnedConfig hk z).val (learnedConfig hk z).property).map
        (fun a => (s,a)))).toMeasure := by
  rw [learnedDrawPathKernel_apply, PMF.toMeasure_map _ _ (measurable_of_countable _),
    iid_round_state_draw]

theorem explorationContinuationLaw_restricted_path {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (S : Finset (Fin k)) (hne : S.Nonempty)
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) S) :
    ((explorationContinuationLaw hk nu L).restrict (Prod.fst ⁻¹' E)).map Prod.snd =
      explorationRewardLaw (by omega) nu E •
        (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L).toMeasure := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (measurable_snd hB)]
  have he : (Prod.snd ⁻¹' B) ∩ (Prod.fst ⁻¹' E) = E ×ˢ B := by
    ext x
    simp [and_comm]
  rw [he, explorationContinuationLaw_rectangle_on_good hk nu S hne E hE hEG]
  simp [Measure.smul_apply, smul_eq_mul]

theorem explorationContinuationLaw_good_regret_integral {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (S : Finset (Fin k)) (hne : S.Nonempty) (mu : Fin k → ℝ)
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) S) :
    (∫ z in Prod.fst ⁻¹' E, pathCoordinationRegret (by omega) S mu z.2
      ∂explorationContinuationLaw hk nu L) =
    (explorationRewardLaw (by omega) nu E).toReal *
      ∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L d).toReal *
        pathCoordinationRegret (by omega) S mu d := by
  rw [← integral_map measurable_snd.aemeasurable
    (measurable_of_countable (pathCoordinationRegret (by omega) S mu)).aestronglyMeasurable,
    explorationContinuationLaw_restricted_path hk nu S hne E hE hEG,
    integral_smul_measure, PMF.integral_eq_sum]
  rfl

theorem explorationContinuationLaw_conditional_coordination_regret {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (S : Finset (Fin k)) (hne : S.Nonempty) (hcard : S.card = n)
    (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) S)
    (hpos : 0 < explorationRewardLaw (by omega) nu E) :
    (∫ z in Prod.fst ⁻¹' E, pathCoordinationRegret (by omega) S mu z.2
      ∂explorationContinuationLaw hk nu L) /
      (explorationContinuationLaw hk nu L (Prod.fst ⁻¹' E)).toReal ≤ 8 * (n : ℝ)^2 := by
  rw [explorationContinuationLaw_good_regret_integral hk nu S hne mu E hE hEG,
    explorationContinuationLaw_fst_event hk nu E hE]
  have hp : (explorationRewardLaw (by omega) nu E).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _))
  rw [mul_comm, mul_div_cancel_right₀ _ hp]
  exact iid_path_regret_le (by omega) S hne hcard mu hmu

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

namespace MarginalCanary

noncomputable def means (a : Fin 3) : ℝ := if a = 0 then 3/4 else if a = 1 then 1/2 else 1/4

def transientDraws (t : Fin 2) (i : Fin 2) : Fin 3 :=
  if t = 0 then 0 else ⟨i.val, by omega⟩

theorem zero_horizon_regret (d : Fin 0 → Fin 2 → Fin 3) :
    pathCoordinationRegret (by decide) ({0,1} : Finset (Fin 3)) means d = 0 := by
  simp [pathCoordinationRegret]

theorem actual_transient_regret :
    pathCoordinationRegret (by decide) ({0,1} : Finset (Fin 3)) means transientDraws = 5/4 := by
  norm_num [pathCoordinationRegret, roundPseudoRegret, roundMeanReward,
    trajectory, extendedCoordinationDraws, transientDraws, step, initial, action,
    CollisionFree, means, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem fixed_draws_not_actions_regret :
    pathCoordinationRegret (by decide) ({0,1} : Finset (Fin 3)) means
      HandoffCanary.separatedDraws = 0 := by
  norm_num [pathCoordinationRegret, roundPseudoRegret, roundMeanReward,
    trajectory, extendedCoordinationDraws, HandoffCanary.separatedDraws, step,
    initial, action, CollisionFree, means, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem two_player_actual_path_bound (L : ℕ) :
    (∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3)))
      (fun _ => by simp)) L d).toReal *
      pathCoordinationRegret (by decide) ({0,1} : Finset (Fin 3)) means d) ≤ 32 := by
  have h := iid_path_regret_le (n := 2) (L := L) (by decide)
    ({0,1} : Finset (Fin 3)) (by decide) (by decide) means
    (by intro a; fin_cases a <;> norm_num [means])
  norm_num at h ⊢
  exact h

end MarginalCanary
end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs.MarginalCanary
open MeasureTheory ProbabilityTheory

theorem allowed_draw_mass (d : Fin 2 → Fin 3) (hd : ∀ i, d i ∈ ({0,1} : Finset (Fin 3))) :
    jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3))) (fun _ => by simp) d = (1/4 : ℝ≥0∞) := by
  have he : {x : Fin 2 → Fin 3 | ∀ i, x i ∈ ({d i} : Finset (Fin 3))} = {d} := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, Set.mem_singleton_iff]
    exact funext_iff.symm
  have h := jointDraw_rectangle_product
    (fun _ : Fin 2 => ({0,1} : Finset (Fin 3))) (fun i => {d i}) (fun _ => by simp)
  rw [he, PMF.toOuterMeasure_apply_singleton] at h
  norm_num [Finset.inter_singleton_of_mem, hd, Fin.prod_univ_two, ← ENNReal.inv_pow] at h ⊢
  exact h

theorem actual_transient_path_mass :
    learnedDrawPathKernel (n := 2) (T := 3) (by decide) 2
      (PopulationCanary.draws, fun _ _ => (1 : ℝ)) {transientDraws} = (1/16 : ℝ≥0∞) := by
  rw [HandoffCanary.actual_future_product, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    FinitePMF.iid_apply]
  have h (t : Fin 2) : jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3)))
      (fun _ => by simp) (transientDraws t) = (1/4 : ℝ≥0∞) := by
    apply allowed_draw_mass
    intro i
    fin_cases t <;> fin_cases i <;> norm_num [transientDraws]
  simp_rw [h]
  norm_num [Fin.prod_univ_two, ← ENNReal.inv_pow]

end BanditRLProof.MusicalChairs.MarginalCanary

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem iid_continuationAction_marginal {n k L : ℕ} (hk : 0 < k) (t : Fin L)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) :
    (FinitePMF.iid (jointDraw C hne) L).map (fun d => continuationAction hk d t) =
      (stateLaw C hne t.val).bind (fun s => (jointDraw C hne).map (action s)) := by
  change (FinitePMF.iid (jointDraw C hne) L).map
    ((fun z : State n k × (Fin n → Fin k) => action z.1 z.2) ∘
      (fun d => (trajectory (extendedCoordinationDraws hk d) t.val, d t))) = _
  rw [← PMF.map_comp, iid_round_state_draw, PMF.map_bind]
  simp_rw [PMF.map_comp]
  rfl

theorem source_conditional_coordination_regret {n k L : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (∫ z in Prod.fst ⁻¹' (explorationGoodEvent (n := n)
      (T := explorationLength k eps delta) (trueTopArms nu n)),
      pathCoordinationRegret (by omega) (trueTopArms nu n) (armMean nu) z.2
        ∂explorationContinuationLaw (by omega) nu L) /
      (explorationContinuationLaw (by omega) nu L
        (Prod.fst ⁻¹' (explorationGoodEvent (n := n)
          (T := explorationLength k eps delta) (trueTopArms nu n)))).toReal ≤ 8 * (n : ℝ)^2 := by
  have hc : (trueTopArms nu n).card = n := by
    simp [trueTopArms, topArms_card, min_eq_left hnk.le]
  have hne : (trueTopArms nu n).Nonempty := Finset.card_pos.mp (by omega)
  exact explorationContinuationLaw_conditional_coordination_regret (by omega) nu
    (trueTopArms nu n) hne hc (armMean nu) (fun a => armMean_mem_unitInterval nu hb a)
    _ (measurableSet_explorationGoodEvent _ hc) (Set.Subset.refl _)
    (explorationGoodEvent_positive hn hnk nu hb eps delta heps hepsgap hdelta hdelta1)

end BanditRLProof.MusicalChairs
