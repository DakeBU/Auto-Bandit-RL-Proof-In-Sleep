import BanditRLProof.Algorithms.MusicalChairsCoordinationTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Finset.Sort
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import BanditRLProof.Algorithms.MusicalChairsCoordinationRegret
import BanditRLProof.Algorithms.MusicalChairsLearnerRegret

open scoped Classical ENNReal
set_option autoImplicit false

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem reward_coordinate_integrable {k D : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (t : Fin D) (a : Fin k) :
    Integrable (fun r : Fin D → Fin k → ℝ => r t a) (rewardLaw nu D) := by
  apply (integrable_const (1 : ℝ)).mono'
    (reward_coordinate_preserving nu t a).measurable.aestronglyMeasurable
  filter_upwards [reward_coordinate_bounded nu hb t a] with r hr
  simpa [Real.norm_eq_abs, abs_of_nonneg hr.1] using hr.2

noncomputable def scheduleRealizedRegret {n k D T : ℕ} (mu : Fin k → ℝ)
    (j : Fin T → Fin D) (a : Fin T → Fin n → Fin k) (r : Fin D → Fin k → ℝ) : ℝ :=
  ∑ t : Fin T, ((∑ b ∈ topArms mu n, mu b) -
    ∑ i : Fin n, if CollisionFree (a t) i then r (j t) (a t i) else 0)

theorem integrable_scheduleRealizedRegret {n k D T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (mu : Fin k → ℝ) (j : Fin T → Fin D) (a : Fin T → Fin n → Fin k) :
    Integrable (scheduleRealizedRegret mu j a) (rewardLaw nu D) := by
  apply integrable_finset_sum
  intro t _
  apply (integrable_const _).sub
  apply integrable_finset_sum
  intro i _
  by_cases h : CollisionFree (a t) i
  · simpa [h] using reward_coordinate_integrable nu hb (j t) (a t i)
  · simp only [h, if_false]
    exact integrable_const _

theorem scheduleRealizedRegret_mean {n k D T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin T → Fin D) (a : Fin T → Fin n → Fin k) :
    (∫ r, scheduleRealizedRegret (armMean nu) j a r ∂rewardLaw nu D) =
      ∑ t : Fin T, globalRoundRegret (armMean nu) (a t) := by
  have hi (t : Fin T) (i : Fin n) : Integrable
      (fun r : Fin D → Fin k → ℝ => if CollisionFree (a t) i then r (j t) (a t i) else 0)
      (rewardLaw nu D) := by
    by_cases h : CollisionFree (a t) i
    · simpa [h] using reward_coordinate_integrable nu hb (j t) (a t i)
    · simp only [h, if_false]
      exact integrable_const _
  unfold scheduleRealizedRegret
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro t _
    rw [integral_sub (integrable_const _) (integrable_finset_sum _ (fun i _ => hi t i)),
      integral_const, integral_finset_sum _ (fun i _ => hi t i)]
    simp only [probReal_univ, one_smul, globalRoundRegret]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : CollisionFree (a t) i <;> simp [h,reward_coordinate_mean]
  · intro t _
    exact (integrable_const _).sub (integrable_finset_sum _ (fun i _ => hi t i))

theorem measurable_scheduleRealizedRegret {n k D T : ℕ} (mu : Fin k → ℝ)
    (j : Fin T → Fin D) :
    Measurable (fun z : (Fin T → Fin n → Fin k) × (Fin D → Fin k → ℝ) =>
      scheduleRealizedRegret mu j z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro a
  apply Finset.measurable_fun_sum
  intro t _
  apply measurable_const.sub
  apply Finset.measurable_fun_sum
  intro i _
  by_cases h : CollisionFree (a t) i
  · simp only [h,if_true]
    exact (measurable_pi_apply (a t i)).comp (measurable_pi_apply (j t))
  · simp only [h,if_false]
    exact measurable_const

theorem integrable_randomScheduleRegret {α : Type*} [MeasurableSpace α]
    {n k D T : ℕ} (P : Measure α) [IsFiniteMeasure P]
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (mu : Fin k → ℝ) (j : Fin T → Fin D)
    (a : α → Fin T → Fin n → Fin k) (ha : Measurable a) :
    Integrable (fun z : α × (Fin D → Fin k → ℝ) => scheduleRealizedRegret mu j (a z.1) z.2)
      (P.prod (rewardLaw nu D)) := by
  apply (integrable_prod_iff ((measurable_scheduleRealizedRegret mu j).comp
    ((ha.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => integrable_scheduleRealizedRegret nu hb mu j (a x))
  · let f : (Fin T → Fin n → Fin k) → ℝ :=
      fun b => ∫ r, ‖scheduleRealizedRegret mu j b r‖ ∂rewardLaw nu D
    have hi : Integrable f (P.map a) := Integrable.of_finite
    exact hi.comp_measurable ha

theorem randomScheduleRegret_mean {α : Type*} [MeasurableSpace α]
    {n k D T : ℕ} (P : Measure α) [IsFiniteMeasure P]
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin T → Fin D) (a : α → Fin T → Fin n → Fin k) (ha : Measurable a) :
    (∫ z, scheduleRealizedRegret (armMean nu) j (a z.1) z.2 ∂P.prod (rewardLaw nu D)) =
      ∫ x, ∑ t : Fin T, globalRoundRegret (armMean nu) (a x t) ∂P := by
  rw [integral_prod _ (integrable_randomScheduleRegret P nu hb (armMean nu) j a ha)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => scheduleRealizedRegret_mean nu hb j (a x))

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def explorationRealizedRegret {n k S : ℕ} (mu : Fin k → ℝ)
    (x : Fin S → Fin n → Fin k) (r : Fin S → Fin k → ℝ) (H : ℕ) : ℝ :=
  scheduleRealizedRegret mu (Fin.castLE (Nat.min_le_right H S))
    (fun t => x (Fin.castLE (Nat.min_le_right H S) t)) r

noncomputable def continuationRealizedRegret {n k L : ℕ} (hk : 0 < k) (mu : Fin k → ℝ)
    (d : Fin L → Fin n → Fin k) (r : Fin L → Fin k → ℝ) : ℝ :=
  scheduleRealizedRegret mu id (fun t => continuationAction hk d t) r

theorem exploration_schedule_pseudo {n k S : ℕ} (hk : 0 < k) (mu : Fin k → ℝ)
    (x : Fin S → Fin n → Fin k) (H : ℕ) :
    (∑ t : Fin (min H S), globalRoundRegret mu (x (Fin.castLE (Nat.min_le_right H S) t))) =
      explorationPrefixRegret hk mu x H := by
  rw [explorationPrefixRegret,Finset.sum_range]
  apply Finset.sum_congr rfl
  intro t _
  simp only [extendedCoordinationDraws,dif_pos (show t.val < S from lt_of_lt_of_le t.isLt (Nat.min_le_right H S))]
  rfl

theorem continuation_schedule_pseudo {n k L : ℕ} (hk : 0 < k) (mu : Fin k → ℝ)
    (d : Fin L → Fin n → Fin k) :
    (∑ t : Fin L, globalRoundRegret mu (continuationAction hk d t)) =
      pathCoordinationRegret hk (topArms mu n) mu d := rfl

theorem integrable_explorationRealizedRegret {n k S : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (mu : Fin k → ℝ) (H : ℕ) :
    Integrable (fun z : (Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ) =>
      explorationRealizedRegret mu z.1 z.2 H) (explorationRewardLaw hk nu) := by
  exact integrable_randomScheduleRegret (explorationLaw n k S hk).toMeasure nu hb mu
    (Fin.castLE (Nat.min_le_right H S)) (fun x t => x (Fin.castLE (Nat.min_le_right H S) t))
      (measurable_of_finite _)

theorem explorationRealizedRegret_mean {n k S : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (H : ℕ) :
    (∫ z : (Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ),
      explorationRealizedRegret (armMean nu) z.1 z.2 H ∂explorationRewardLaw hk nu) =
    ∫ z : (Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ),
      explorationPrefixRegret hk (armMean nu) z.1 H ∂explorationRewardLaw hk nu := by
  have h := randomScheduleRegret_mean (explorationLaw n k S hk).toMeasure nu hb
    (Fin.castLE (Nat.min_le_right H S)) (fun x t => x (Fin.castLE (Nat.min_le_right H S) t))
      (measurable_of_finite _)
  simp_rw [exploration_schedule_pseudo hk] at h
  unfold explorationRealizedRegret explorationRewardLaw
  rw [h]
  symm
  have hm : ((explorationLaw n k S hk).toMeasure.prod (rewardLaw nu S)).map Prod.fst =
      (explorationLaw n k S hk).toMeasure := by simp
  calc
    _ = ∫ x, explorationPrefixRegret hk (armMean nu) x H
        ∂(((explorationLaw n k S hk).toMeasure.prod (rewardLaw nu S)).map Prod.fst) :=
      (integral_map measurable_fst.aemeasurable (measurable_of_finite _).aestronglyMeasurable).symm
    _ = _ := by rw [hm]

abbrev FullSample (n k S H : ℕ) :=
  (((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ)) × (Fin (H-S) → Fin n → Fin k)) ×
    (Fin (H-S) → Fin k → ℝ)

noncomputable def completeLearnerLaw {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) : Measure (FullSample n k S H) :=
  (explorationContinuationLaw hk nu (H-S)).prod (rewardLaw nu (H-S))

instance completeLearnerLaw_probability {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] :
    IsProbabilityMeasure (completeLearnerLaw (n := n) (S := S) (H := H) hk nu) := by
  unfold completeLearnerLaw
  infer_instance

theorem completeLearnerLaw_first_preserving {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] :
    MeasurePreserving (Prod.fst : FullSample n k S H → _)
      (completeLearnerLaw hk nu) (explorationContinuationLaw hk nu (H-S)) := measurePreserving_fst

theorem explorationContinuationLaw_first_preserving {n k S L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] :
    MeasurePreserving (Prod.fst : ((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ)) ×
      (Fin L → Fin n → Fin k) → _) (explorationContinuationLaw hk nu L)
        (explorationRewardLaw (by omega) nu) := by
  refine ⟨measurable_fst, ?_⟩
  change ((explorationRewardLaw (by omega) nu).compProd (learnedDrawPathKernel hk L)).fst = _
  exact Measure.fst_compProd _ _

theorem completeLearnerLaw_exploration_preserving {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] :
    MeasurePreserving (fun z : FullSample n k S H => z.1.1)
      (completeLearnerLaw hk nu) (explorationRewardLaw (by omega) nu) :=
  (explorationContinuationLaw_first_preserving hk nu).comp (completeLearnerLaw_first_preserving hk nu)

noncomputable def realizedLearnerRegret {n k S H : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (z : FullSample n k S H) : ℝ :=
  explorationRealizedRegret mu z.1.1.1 z.1.1.2 H + continuationRealizedRegret hk mu z.1.2 z.2

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem integral_preserving_pullback {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} (g : α → β) (hg : MeasurePreserving g P Q)
    (f : β → ℝ) (hf : Integrable f Q) : (∫ x, f (g x) ∂P) = ∫ y, f y ∂Q := by
  have hm : AEStronglyMeasurable f (P.map g) := by rw [hg.map_eq]; exact hf.aestronglyMeasurable
  rw [← integral_map hg.measurable.aemeasurable hm, hg.map_eq]

theorem measurable_continuationSchedule {n k L : ℕ} (hk : 0 < k) :
    Measurable (fun d : Fin L → Fin n → Fin k => fun t : Fin L => continuationAction hk d t) :=
  measurable_of_finite _

theorem integrable_realizedLearnerRegret {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (mu : Fin k → ℝ) :
    Integrable (realizedLearnerRegret (n := n) (S := S) (H := H) (by omega) mu)
      (completeLearnerLaw hk nu) := by
  have hx := (completeLearnerLaw_exploration_preserving (n := n) (S := S) (H := H) hk nu).integrable_comp_of_integrable (integrable_explorationRealizedRegret (by omega) nu hb mu H)
  have hy := integrable_randomScheduleRegret
    (explorationContinuationLaw (n := n) (T := S) hk nu (H-S)) nu hb mu id
    (fun z t => continuationAction (by omega) z.2 t)
    ((measurable_continuationSchedule (L := H-S) (by omega)).comp measurable_snd)
  exact hx.add hy

theorem continuationRealizedRegret_mean_joint {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z : FullSample n k S H, continuationRealizedRegret (by omega) (armMean nu) z.1.2 z.2
      ∂completeLearnerLaw hk nu) =
    ∫ z, pathCoordinationRegret (by omega) (trueTopArms nu n) (armMean nu) z.2
      ∂explorationContinuationLaw (n := n) (T := S) hk nu (H-S) := by
  exact randomScheduleRegret_mean
    (explorationContinuationLaw (n := n) (T := S) hk nu (H-S)) nu hb id
    (fun z t => continuationAction (by omega) z.2 t)
    ((measurable_continuationSchedule (L := H-S) (by omega)).comp measurable_snd)

theorem realizedLearnerRegret_expected_eq_pseudo {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z : FullSample n k S H, realizedLearnerRegret (by omega) (armMean nu) z
      ∂completeLearnerLaw hk nu) =
    ∫ z, learnerRegret (n := n) (S := S) (H := H) (by omega) (armMean nu) z.1.1 z.2
      ∂explorationContinuationLaw (n := n) (T := S) hk nu (H-S) := by
  have hxe := integrable_explorationRealizedRegret (n := n) (S := S) (by omega) nu hb (armMean nu) H
  have hx := (completeLearnerLaw_exploration_preserving (n := n) (S := S) (H := H) hk nu).integrable_comp_of_integrable hxe
  have hy := integrable_randomScheduleRegret
    (explorationContinuationLaw (n := n) (T := S) hk nu (H-S)) nu hb (armMean nu) id
    (fun z t => continuationAction (by omega) z.2 t)
    ((measurable_continuationSchedule (L := H-S) (by omega)).comp measurable_snd)
  have hxp : Integrable (fun z : (Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ) =>
      explorationPrefixRegret (by omega) (armMean nu) z.1 H) (explorationRewardLaw (by omega) nu) :=
    (Integrable.of_finite (f := fun x : Fin S → Fin n → Fin k =>
      explorationPrefixRegret (by omega) (armMean nu) x H)
      (μ := (explorationRewardLaw (by omega) nu).map Prod.fst)).comp_measurable measurable_fst
  have hxp' := (explorationContinuationLaw_first_preserving (n := n) (S := S) (L := H-S) hk nu).integrable_comp_of_integrable hxp
  have hpp := integrable_pathRegret_projection (S := S) (L := H-S) (by omega)
    (trueTopArms nu n) (armMean nu) (explorationContinuationLaw (n := n) (T := S) hk nu (H-S))
  change Integrable (fun z : FullSample n k S H =>
    explorationRealizedRegret (armMean nu) z.1.1.1 z.1.1.2 H) (completeLearnerLaw hk nu) at hx
  change Integrable (fun z : FullSample n k S H =>
    continuationRealizedRegret (by omega) (armMean nu) z.1.2 z.2) (completeLearnerLaw hk nu) at hy
  change Integrable (fun z : ((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ)) × (Fin (H-S) → Fin n → Fin k) => explorationPrefixRegret (by omega) (armMean nu) z.1.1 H)
    (explorationContinuationLaw (n := n) (T := S) hk nu (H-S)) at hxp'
  have hxmean : (∫ z : FullSample n k S H,
      explorationRealizedRegret (armMean nu) z.1.1.1 z.1.1.2 H ∂completeLearnerLaw hk nu) =
      ∫ z, explorationPrefixRegret (by omega) (armMean nu) z.1.1 H
        ∂explorationContinuationLaw (n := n) (T := S) hk nu (H-S) := by
    calc
      _ = ∫ z, explorationRealizedRegret (armMean nu) z.1 z.2 H
          ∂explorationRewardLaw (n := n) (T := S) (by omega) nu :=
        integral_preserving_pullback _ (completeLearnerLaw_exploration_preserving hk nu) _ hxe
      _ = ∫ z, explorationPrefixRegret (by omega) (armMean nu) z.1 H
          ∂explorationRewardLaw (n := n) (T := S) (by omega) nu :=
        explorationRealizedRegret_mean (by omega) nu hb H
      _ = _ := (integral_preserving_pullback _
        (explorationContinuationLaw_first_preserving (L := H-S) hk nu) _ hxp).symm
  calc
    _ = (∫ z : FullSample n k S H,
          explorationRealizedRegret (armMean nu) z.1.1.1 z.1.1.2 H ∂completeLearnerLaw hk nu) +
        ∫ z : FullSample n k S H,
          continuationRealizedRegret (by omega) (armMean nu) z.1.2 z.2 ∂completeLearnerLaw hk nu :=
      integral_add hx hy
    _ = (∫ z, explorationPrefixRegret (by omega) (armMean nu) z.1.1 H
          ∂explorationContinuationLaw (n := n) (T := S) hk nu (H-S)) +
        ∫ z, pathCoordinationRegret (by omega) (trueTopArms nu n) (armMean nu) z.2
          ∂explorationContinuationLaw (n := n) (T := S) hk nu (H-S) := by
      rw [hxmean, continuationRealizedRegret_mean_joint hk nu hb]
    _ = ∫ z, (explorationPrefixRegret (by omega) (armMean nu) z.1.1 H +
        pathCoordinationRegret (by omega) (trueTopArms nu n) (armMean nu) z.2)
          ∂explorationContinuationLaw (n := n) (T := S) hk nu (H-S) := (integral_add hxp' hpp).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (fun z => (learnerRegret_split (n := n) (S := S) (H := H) (by omega) (armMean nu) z.1.1 z.2).symm))


theorem source_expected_realizedLearnerRegret_le {n k H : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (∫ z : FullSample n k (explorationLength k eps delta) H,
      realizedLearnerRegret (by omega) (armMean nu) z ∂completeLearnerLaw (by omega) nu) ≤
    min ((n : ℝ)*H) ((n : ℝ)*explorationLength k eps delta +
      8*(n : ℝ)^2 + delta*((n : ℝ)*H)) := by
  rw [realizedLearnerRegret_expected_eq_pseudo (by omega) nu hb]
  exact source_expected_learnerRegret_coarse hn hnk nu hb eps delta heps hepsgap hdelta hdelta1

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def continuationFeedback {n k L : ℕ} (hk : 0 < k)
    (d : Fin L → Fin n → Fin k) (r : Fin L → Fin k → ℝ) (i : Fin n) (t : Fin L) :
    ExplorationFeedback k :=
  ⟨continuationAction hk d t i, decide (¬ CollisionFree (continuationAction hk d t) i),
    if CollisionFree (continuationAction hk d t) i then r t (continuationAction hk d t i) else 0⟩

noncomputable def learnerFeedback {n k S H : ℕ} (hk : 0 < k)
    (z : FullSample n k S H) (i : Fin n) (t : Fin H) : ExplorationFeedback k :=
  if ht : t.val < S then explorationFeedback z.1.1.1 z.1.1.2 i ⟨t.val,ht⟩
  else continuationFeedback hk z.1.2 z.2 i ⟨t.val-S,by omega⟩

theorem learnerFeedback_explore {n k S H : ℕ} (hk : 0 < k)
    (z : FullSample n k S H) (i : Fin n) (t : Fin H) (ht : t.val < S) :
    learnerFeedback hk z i t = explorationFeedback z.1.1.1 z.1.1.2 i ⟨t.val,ht⟩ := by
  simp [learnerFeedback,ht]

theorem learnerFeedback_coordinate {n k S H : ℕ} (hk : 0 < k)
    (z : FullSample n k S H) (i : Fin n) (u : Fin (H-S)) :
    learnerFeedback hk z i ⟨S+u.val,by omega⟩ = continuationFeedback hk z.1.2 z.2 i u := by
  simp [learnerFeedback]

theorem learnerFeedback_arm {n k S H : ℕ} (hk : 0 < k)
    (z : FullSample n k S H) (i : Fin n) (t : Fin H) :
    (learnerFeedback hk z i t).arm = learnerAction hk z.1.1.1 z.1.2 t.val i := by
  by_cases ht : t.val < S
  · simp [learnerFeedback,explorationFeedback,learnerAction,ht]
  · let u : Fin (H-S) := ⟨t.val-S,by omega⟩
    have he : t.val = S+u.val := by dsimp [u]; omega
    rw [he,learnerAction_coordinate]
    simp [learnerFeedback,continuationFeedback,ht,u]

theorem learnerFeedback_collision {n k S H : ℕ} (hk : 0 < k)
    (z : FullSample n k S H) (i : Fin n) (t : Fin H) :
    (learnerFeedback hk z i t).collided =
      collisionBit (learnerAction hk z.1.1.1 z.1.2 t.val) i := by
  by_cases ht : t.val < S
  · simp [learnerFeedback,explorationFeedback,learnerAction,collisionBit,ht]
  · let u : Fin (H-S) := ⟨t.val-S,by omega⟩
    have he : t.val = S+u.val := by dsimp [u]; omega
    rw [he,learnerAction_coordinate]
    simp [learnerFeedback,continuationFeedback,collisionBit,ht,u]

theorem learnerFeedback_completed_exploration {n k S H : ℕ} (hk : 0 < k) (hSH : S ≤ H)
    (z : FullSample n k S H) (i : Fin n) :
    (fun t : Fin S => learnerFeedback hk z i (Fin.castLE hSH t)) =
      explorationFeedback z.1.1.1 z.1.1.2 i := by
  funext t
  rw [learnerFeedback_explore hk z i _ t.isLt]
  rfl

theorem learnedConfig_from_feedback {n k S H : ℕ} (hk : 1 < k) (hSH : S ≤ H)
    (z : FullSample n k S H) (i : Fin n) :
    (learnedConfig hk z.1.1).val i =
      localCandidateSet (fun t : Fin S => learnerFeedback (by omega) z i (Fin.castLE hSH t)) := by
  rw [learnerFeedback_completed_exploration]
  rfl

theorem continuationFeedback_local_update {n k L : ℕ} (hk : 0 < k)
    (d : Fin L → Fin n → Fin k) (r : Fin L → Fin k → ℝ) (i : Fin n) (t : Fin L) :
    trajectory (extendedCoordinationDraws hk d) (t.val+1) i =
      localUpdate (trajectory (extendedCoordinationDraws hk d) t.val i)
        (continuationFeedback hk d r i t).arm (continuationFeedback hk d r i t).collided := by
  rw [trajectory,step_localUpdate]
  simp [continuationFeedback,continuationAction,extendedCoordinationDraws,t.isLt,collisionBit]

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem learnerFeedback_prefix {n k S H : ℕ} (hk : 0 < k)
    (z w : FullSample n k S H) (i : Fin n) (t : Fin H)
    (hx : ∀ u : Fin S, u.val ≤ t.val → z.1.1.1 u = w.1.1.1 u)
    (hr : ∀ u : Fin S, u.val ≤ t.val → z.1.1.2 u = w.1.1.2 u)
    (hd : ∀ u : Fin (H-S), S+u.val ≤ t.val → z.1.2 u = w.1.2 u)
    (hy : ∀ u : Fin (H-S), S+u.val ≤ t.val → z.2 u = w.2 u) :
    learnerFeedback hk z i t = learnerFeedback hk w i t := by
  by_cases ht : t.val < S
  · simp only [learnerFeedback,dif_pos ht,explorationFeedback]
    rw [hx ⟨t.val,ht⟩ le_rfl,hr ⟨t.val,ht⟩ le_rfl]
  · let u : Fin (H-S) := ⟨t.val-S,by omega⟩
    have hca : continuationAction hk z.1.2 u = continuationAction hk w.1.2 u := by
      apply continuationAction_prefix
      intro v hv
      apply hd v
      change v.val ≤ t.val-S at hv
      omega
    have hry := hy u (by dsimp [u]; omega)
    change (if ht : t.val < S then _ else continuationFeedback hk z.1.2 z.2 i u) =
      (if ht : t.val < S then _ else continuationFeedback hk w.1.2 w.2 i u)
    simp only [dif_neg ht,continuationFeedback,hca,hry]

theorem finite_sum_split_at {H S : ℕ} (hSH : S ≤ H) (f : Fin H → ℝ) :
    (∑ t : Fin H, f t) = (∑ t : Fin S, f (Fin.castLE hSH t)) +
      ∑ u : Fin (H-S), f ⟨S+u.val,by omega⟩ := by
  obtain ⟨L,rfl⟩ := Nat.exists_eq_add_of_le hSH
  rw [Fin.sum_univ_add]
  congr 1
  symm
  refine Fintype.sum_equiv (finCongr (Nat.add_sub_cancel_left S L)) _ _ ?_
  intro t
  rfl

theorem realizedLearnerRegret_eq_feedback {n k S H : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (z : FullSample n k S H) :
    realizedLearnerRegret hk mu z =
      ∑ t : Fin H, ((∑ a ∈ topArms mu n, mu a) - ∑ i : Fin n, (learnerFeedback hk z i t).reward) := by
  by_cases hSH : S ≤ H
  · rw [finite_sum_split_at hSH]
    unfold realizedLearnerRegret explorationRealizedRegret continuationRealizedRegret scheduleRealizedRegret
    simp only [Function.id_def]
    congr 1
    · refine Fintype.sum_equiv (finCongr (Nat.min_eq_right hSH)) _ _ ?_
      intro t
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [learnerFeedback_explore hk z i _ (by simpa using (Fin.castLE (Nat.min_le_right H S) t).isLt)]
      rfl
    · apply Finset.sum_congr rfl
      intro t _
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [learnerFeedback_coordinate]
      rfl
  · have hHS : H ≤ S := by omega
    have hz : continuationRealizedRegret hk mu z.1.2 z.2 = 0 := by
      unfold continuationRealizedRegret scheduleRealizedRegret
      exact Finset.sum_eq_zero (fun t _ => Fin.elim0 (Fin.cast (Nat.sub_eq_zero_of_le hHS) t))
    rw [realizedLearnerRegret,hz,add_zero]
    unfold explorationRealizedRegret scheduleRealizedRegret
    refine Fintype.sum_equiv (finCongr (Nat.min_eq_left hHS)) _ _ ?_
    intro t
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [learnerFeedback_explore hk z i _ (lt_of_lt_of_le (finCongr (Nat.min_eq_left hHS) t).isLt hHS)]
    rfl

instance explorationFeedback_measurableSpace (k : ℕ) : MeasurableSpace (ExplorationFeedback k) :=
  MeasurableSpace.comap (fun f : ExplorationFeedback k => (f.arm,f.collided,f.reward)) inferInstance

theorem measurable_feedback_mk {α : Type*} [MeasurableSpace α] {k : ℕ}
    (a : α → Fin k) (c : α → Bool) (r : α → ℝ)
    (ha : Measurable a) (hc : Measurable c) (hr : Measurable r) :
    Measurable (fun x => (⟨a x,c x,r x⟩ : ExplorationFeedback k)) :=
  measurable_comap_iff.mpr (ha.prodMk (hc.prodMk hr))

theorem measurable_explorationFeedback {n k S : ℕ} (i : Fin n) (t : Fin S) :
    Measurable (fun z : (Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ) =>
      explorationFeedback z.1 z.2 i t) := by
  apply measurable_from_prod_countable_right
  intro x
  unfold explorationFeedback
  refine measurable_feedback_mk (fun _ => x t i)
    (fun _ => decide (¬ CollisionFree (x t) i))
    (fun r : Fin S → Fin k → ℝ => if CollisionFree (x t) i then r t (x t i) else 0)
    measurable_const measurable_const ?_
  by_cases h : CollisionFree (x t) i
  · simp only [h,if_true]
    exact (measurable_pi_apply (x t i)).comp (measurable_pi_apply t)
  · simp only [h,if_false]
    exact measurable_const

theorem measurable_continuationFeedback {n k L : ℕ} (hk : 0 < k) (i : Fin n) (t : Fin L) :
    Measurable (fun z : (Fin L → Fin n → Fin k) × (Fin L → Fin k → ℝ) =>
      continuationFeedback hk z.1 z.2 i t) := by
  apply measurable_from_prod_countable_right
  intro d
  unfold continuationFeedback
  refine measurable_feedback_mk (fun _ => continuationAction hk d t i)
    (fun _ => decide (¬ CollisionFree (continuationAction hk d t) i))
    (fun r : Fin L → Fin k → ℝ => if CollisionFree (continuationAction hk d t) i then r t (continuationAction hk d t i) else 0)
    measurable_const measurable_const ?_
  by_cases h : CollisionFree (continuationAction hk d t) i
  · simp only [h,if_true]
    exact (measurable_pi_apply (continuationAction hk d t i)).comp (measurable_pi_apply t)
  · simp only [h,if_false]
    exact measurable_const

theorem measurable_learnerFeedback {n k S H : ℕ} (hk : 0 < k) (i : Fin n) (t : Fin H) :
    Measurable (fun z : FullSample n k S H => learnerFeedback hk z i t) := by
  by_cases ht : t.val < S
  · simpa only [learnerFeedback,dif_pos ht] using
      (measurable_explorationFeedback i ⟨t.val,ht⟩).comp measurable_fst.fst
  · simpa only [learnerFeedback,dif_neg ht] using
      (measurable_continuationFeedback hk i ⟨t.val-S,by omega⟩).comp
        (measurable_fst.snd.prodMk measurable_snd)

theorem measurable_learnerTrace {n k S H : ℕ} (hk : 0 < k) :
    Measurable (fun z : FullSample n k S H => fun i t => learnerFeedback hk z i t) :=
  measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun t => measurable_learnerFeedback hk i t))

noncomputable def visibleLearnerLaw {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) : Measure (Fin n → Fin H → ExplorationFeedback k) :=
  (completeLearnerLaw hk nu).map (fun z : FullSample n k S H => fun i t => learnerFeedback (by omega) z i t)

instance visibleLearnerLaw_probability {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] :
    IsProbabilityMeasure (visibleLearnerLaw (n := n) (S := S) (H := H) hk nu) := by
  unfold visibleLearnerLaw
  exact Measure.isProbabilityMeasure_map (measurable_learnerTrace (n := n) (S := S) (H := H) (by omega)).aemeasurable

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def visibleRegret {n k H : ℕ} (mu : Fin k → ℝ)
    (f : Fin n → Fin H → ExplorationFeedback k) : ℝ :=
  ∑ t : Fin H, ((∑ a ∈ topArms mu n, mu a) - ∑ i : Fin n, (f i t).reward)

theorem measurable_feedback_reward {k : ℕ} :
    Measurable (ExplorationFeedback.reward : ExplorationFeedback k → ℝ) := by
  have h : Measurable (fun f : ExplorationFeedback k => (f.arm,f.collided,f.reward)) :=
    comap_measurable _
  exact h.snd.snd

theorem measurable_visibleRegret {n k H : ℕ} (mu : Fin k → ℝ) :
    Measurable (visibleRegret (n := n) (H := H) mu) := by
  apply Finset.measurable_sum
  intro t _
  apply measurable_const.sub
  apply Finset.measurable_sum
  intro i _
  exact measurable_feedback_reward.comp ((measurable_pi_apply t).comp (measurable_pi_apply i))

theorem visibleRegret_pullback {n k S H : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (z : FullSample n k S H) :
    visibleRegret mu (fun i t => learnerFeedback hk z i t) = realizedLearnerRegret hk mu z :=
  (realizedLearnerRegret_eq_feedback hk mu z).symm

theorem integrable_visibleRegret {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (mu : Fin k → ℝ) :
    Integrable (visibleRegret (n := n) (H := H) mu) (visibleLearnerLaw (S := S) hk nu) := by
  unfold visibleLearnerLaw
  apply (integrable_map_measure (measurable_visibleRegret mu).aestronglyMeasurable
    (measurable_learnerTrace (n := n) (S := S) (H := H) (by omega)).aemeasurable).mpr
  simpa only [Function.comp_def, visibleRegret_pullback] using integrable_realizedLearnerRegret (n := n) (S := S) (H := H) hk nu hb mu

theorem visibleRegret_expected_eq_realized {n k S H : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) (mu : Fin k → ℝ) :
    (∫ f, visibleRegret (n := n) (H := H) mu f ∂visibleLearnerLaw (S := S) hk nu) =
      ∫ z : FullSample n k S H, realizedLearnerRegret (by omega) mu z ∂completeLearnerLaw hk nu := by
  unfold visibleLearnerLaw
  rw [integral_map (measurable_learnerTrace (n := n) (S := S) (H := H) (by omega)).aemeasurable
    (measurable_visibleRegret mu).aestronglyMeasurable]
  simp only [visibleRegret_pullback]

theorem source_expected_visibleRegret_le {n k H : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (∫ f, visibleRegret (n := n) (H := H) (armMean nu) f
      ∂visibleLearnerLaw (S := explorationLength k eps delta) (by omega) nu) ≤
      min ((n : ℝ)*H) ((n : ℝ)*explorationLength k eps delta + 8*(n : ℝ)^2 + delta*((n : ℝ)*H)) := by
  rw [visibleRegret_expected_eq_realized]
  exact source_expected_realizedLearnerRegret_le hn hnk nu hb eps delta heps hepsgap hdelta hdelta1

end BanditRLProof.MusicalChairs
