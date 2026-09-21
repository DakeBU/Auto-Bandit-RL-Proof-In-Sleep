import BanditRLProof.Algorithms.MusicalChairsCoordinationTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Finset.Sort
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import BanditRLProof.Algorithms.MusicalChairsCoordinationRegret
import BanditRLProof.Algorithms.MusicalChairsMarginal

open scoped Classical ENNReal
set_option autoImplicit false

namespace BanditRLProof.MusicalChairs

theorem ordered_set_sum_max {α : Type*} [DecidableEq α] (score : α → ℝ)
    (S B : Finset α) (hcard : B.card ≤ S.card) (hnonneg : ∀ a, 0 ≤ score a)
    (horder : ∀ a ∈ S, ∀ b ∉ S, score b ≤ score a) :
    ∑ b ∈ B, score b ≤ ∑ a ∈ S, score a := by
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S score hS
    have hc : (B \ S).card ≤ (S \ B).card := by
      simp only [Finset.card_sdiff]
      rw [Finset.inter_comm S B]
      omega
    have hb : (∑ b ∈ B \ S, score b) ≤ ((B \ S).card : ℝ) * score a := by
      calc
        _ ≤ ∑ _b ∈ B \ S, score a := Finset.sum_le_sum
          (fun b hb => horder a ha b (Finset.mem_sdiff.mp hb).2)
        _ = _ := by simp
    have hs : ((S \ B).card : ℝ) * score a ≤ ∑ b ∈ S \ B, score b := by
      calc
        _ = ∑ _b ∈ S \ B, score a := by simp
        _ ≤ _ := Finset.sum_le_sum (fun b hb => hmin b (Finset.mem_sdiff.mp hb).1)
    have hmul : ((B \ S).card : ℝ) * score a ≤ ((S \ B).card : ℝ) * score a :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hnonneg a)
    have hB := Finset.sum_inter_add_sum_diff B S score
    have hA := Finset.sum_inter_add_sum_diff S B score
    rw [Finset.inter_comm S B] at hA
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hB : B = ∅ := Finset.card_eq_zero.mp (by simpa [he] using hcard)
    simp [he,hB]

theorem topArms_sum_max {k n : ℕ} (score : Fin k → ℝ) (hnk : n ≤ k)
    (hnonneg : ∀ a, 0 ≤ score a) (B : Finset (Fin k)) (hcard : B.card ≤ n) :
    ∑ b ∈ B, score b ≤ ∑ a ∈ topArms score n, score a := by
  apply ordered_set_sum_max score (topArms score n) B
    (by simpa [topArms_card, min_eq_left hnk] using hcard) hnonneg
  intro a ha b hb
  rcases topArms_before_unselected score n ha hb with hlt | heq
  · exact hlt.le
  · exact heq.1.symm.le

noncomputable def collisionFreePlayers {n k : ℕ} (a : Fin n → Fin k) : Finset (Fin n) :=
  Finset.univ.filter (CollisionFree a)

noncomputable def earnedArms {n k : ℕ} (a : Fin n → Fin k) : Finset (Fin k) :=
  (collisionFreePlayers a).image a

theorem collisionFree_action_injective {n k : ℕ} (a : Fin n → Fin k) :
    Set.InjOn a (collisionFreePlayers a) := by
  intro i hi j _ hij
  by_contra hne
  exact (Finset.mem_filter.mp hi).2 j (Ne.symm hne) hij.symm

theorem earnedArms_card_le {n k : ℕ} (a : Fin n → Fin k) : (earnedArms a).card ≤ n := by
  calc
    _ ≤ (collisionFreePlayers a).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by simp

theorem earnedArms_sum {n k : ℕ} (mu : Fin k → ℝ) (a : Fin n → Fin k) :
    ∑ b ∈ earnedArms a, mu b = ∑ i, if CollisionFree a i then mu (a i) else 0 := by
  rw [earnedArms, Finset.sum_image (collisionFree_action_injective a)]
  simp [collisionFreePlayers, Finset.sum_filter]

noncomputable def globalRoundRegret {n k : ℕ} (mu : Fin k → ℝ) (a : Fin n → Fin k) : ℝ :=
  (∑ b ∈ topArms mu n, mu b) - ∑ i, if CollisionFree a i then mu (a i) else 0

theorem globalRoundRegret_nonneg {n k : ℕ} (mu : Fin k → ℝ)
    (hnk : n ≤ k) (hmu : ∀ b, 0 ≤ mu b) (a : Fin n → Fin k) :
    0 ≤ globalRoundRegret mu a := by
  rw [globalRoundRegret, sub_nonneg, ← earnedArms_sum]
  exact topArms_sum_max mu hnk hmu (earnedArms a) (earnedArms_card_le a)

theorem globalRoundRegret_le {n k : ℕ} (mu : Fin k → ℝ)
    (hnk : n ≤ k) (hmu : ∀ b, 0 ≤ mu b ∧ mu b ≤ 1) (a : Fin n → Fin k) :
    globalRoundRegret mu a ≤ n := by
  have hs : (∑ b ∈ topArms mu n, mu b) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _b ∈ topArms mu n, (1 : ℝ) := Finset.sum_le_sum (fun b _ => (hmu b).2)
      _ = _ := by simp [topArms_card,min_eq_left hnk]
  have hr : 0 ≤ ∑ i, if CollisionFree a i then mu (a i) else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact (hmu _).1
    · rfl
  unfold globalRoundRegret
  linarith

theorem roundPseudoRegret_global {n k : ℕ} (mu : Fin k → ℝ)
    (s : State n k) (d : Fin n → Fin k) :
    roundPseudoRegret (topArms mu n) mu s d = globalRoundRegret mu (action s d) := rfl

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs

noncomputable def learnerAction {n k S L : ℕ} (hk : 0 < k)
    (x : Fin S → Fin n → Fin k) (d : Fin L → Fin n → Fin k) (t : ℕ) : Fin n → Fin k :=
  if ht : t < S then x ⟨t,ht⟩ else
    action (trajectory (extendedCoordinationDraws hk d) (t-S)) (extendedCoordinationDraws hk d (t-S))

theorem learnerAction_explore {n k S L : ℕ} (hk : 0 < k)
    (x : Fin S → Fin n → Fin k) (d : Fin L → Fin n → Fin k) (t : ℕ) (ht : t < S) :
    learnerAction hk x d t = x ⟨t,ht⟩ := by simp [learnerAction,ht]

theorem learnerAction_coordinate {n k S L : ℕ} (hk : 0 < k)
    (x : Fin S → Fin n → Fin k) (d : Fin L → Fin n → Fin k) (t : Fin L) :
    learnerAction hk x d (S+t.val) = continuationAction hk d t := by
  simp [learnerAction, continuationAction, extendedCoordinationDraws, t.isLt]

noncomputable def explorationPrefixRegret {n k S : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (x : Fin S → Fin n → Fin k) (H : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (min H S), globalRoundRegret mu (extendedCoordinationDraws hk x t)

noncomputable def learnerRegret {n k S H : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (x : Fin S → Fin n → Fin k) (d : Fin (H-S) → Fin n → Fin k) : ℝ :=
  ∑ t ∈ Finset.range H, globalRoundRegret mu (learnerAction hk x d t)

theorem learnerRegret_split {n k S H : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (x : Fin S → Fin n → Fin k) (d : Fin (H-S) → Fin n → Fin k) :
    learnerRegret hk mu x d = explorationPrefixRegret hk mu x H +
      pathCoordinationRegret hk (topArms mu n) mu d := by
  by_cases hSH : S ≤ H
  · have he : H = S + (H-S) := by omega
    calc
      _ = ∑ t ∈ Finset.range (S+(H-S)), globalRoundRegret mu (learnerAction hk x d t) :=
        congrArg (fun h => ∑ t ∈ Finset.range h, globalRoundRegret mu (learnerAction hk x d t)) he
      _ = (∑ t ∈ Finset.range S, globalRoundRegret mu (learnerAction hk x d t)) +
          ∑ t ∈ Finset.range (H-S), globalRoundRegret mu (learnerAction hk x d (S+t)) :=
        Finset.sum_range_add _ _ _
      _ = _ := by
        congr 1
        · unfold explorationPrefixRegret
          rw [min_eq_right hSH]
          apply Finset.sum_congr rfl
          intro t ht
          simp [learnerAction, extendedCoordinationDraws, Finset.mem_range.mp ht]
        · rw [Finset.sum_range]
          unfold pathCoordinationRegret
          apply Finset.sum_congr rfl
          intro t _
          rw [learnerAction_coordinate]
          rfl
  · have hHS : H ≤ S := by omega
    have hL : H-S = 0 := Nat.sub_eq_zero_of_le hHS
    have hz : pathCoordinationRegret hk (topArms mu n) mu d = 0 := by
      unfold pathCoordinationRegret
      exact Finset.sum_eq_zero (fun t _ => Fin.elim0 (Fin.cast hL t))
    rw [hz, add_zero]
    unfold learnerRegret explorationPrefixRegret
    rw [min_eq_left hHS]
    apply Finset.sum_congr rfl
    intro t ht
    have htS : t < S := lt_of_lt_of_le (Finset.mem_range.mp ht) hHS
    simp [learnerAction, extendedCoordinationDraws, htS]

theorem explorationPrefixRegret_bounds {n k S : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (hnk : n ≤ k) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (x : Fin S → Fin n → Fin k) (H : ℕ) :
    0 ≤ explorationPrefixRegret hk mu x H ∧
      explorationPrefixRegret hk mu x H ≤ (n : ℝ) * min H S := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ => globalRoundRegret_nonneg mu hnk (fun a => (hmu a).1) _)
  · calc
      _ ≤ ∑ _t ∈ Finset.range (min H S), (n : ℝ) :=
        Finset.sum_le_sum (fun _ _ => globalRoundRegret_le mu hnk hmu _)
      _ = _ := by simp [mul_comm]

theorem learnerRegret_bounds {n k S H : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (hnk : n ≤ k) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (x : Fin S → Fin n → Fin k) (d : Fin (H-S) → Fin n → Fin k) :
    0 ≤ learnerRegret hk mu x d ∧ learnerRegret hk mu x d ≤ (n : ℝ) * H := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ => globalRoundRegret_nonneg mu hnk (fun a => (hmu a).1) _)
  · calc
      _ ≤ ∑ _t ∈ Finset.range H, (n : ℝ) :=
        Finset.sum_le_sum (fun _ _ => globalRoundRegret_le mu hnk hmu _)
      _ = _ := by simp [mul_comm]

theorem learnerRegret_le_exploration_add {n k S H : ℕ} (hk : 0 < k)
    (mu : Fin k → ℝ) (hnk : n ≤ k) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (x : Fin S → Fin n → Fin k) (d : Fin (H-S) → Fin n → Fin k) :
    learnerRegret hk mu x d ≤ (n : ℝ)*min H S + pathCoordinationRegret hk (topArms mu n) mu d := by
  rw [learnerRegret_split]
  exact add_le_add (explorationPrefixRegret_bounds hk mu hnk hmu x H).2 le_rfl

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem learnerAction_prefix {n k S L : ℕ} (hk : 0 < k)
    (x y : Fin S → Fin n → Fin k) (d e : Fin L → Fin n → Fin k)
    (t : ℕ) (ht : t < S+L)
    (hx : ∀ u : Fin S, u.val ≤ t → x u = y u)
    (hd : ∀ u : Fin L, S+u.val ≤ t → d u = e u) :
    learnerAction hk x d t = learnerAction hk y e t := by
  by_cases htS : t < S
  · simp only [learnerAction, dif_pos htS]
    exact hx ⟨t,htS⟩ le_rfl
  · let u : Fin L := ⟨t-S, by omega⟩
    have he : t = S+u.val := by dsimp [u]; omega
    rw [he, learnerAction_coordinate, learnerAction_coordinate]
    apply continuationAction_prefix
    intro v hv
    apply hd v
    change v.val ≤ t-S at hv
    omega

theorem integrable_learnerRegret {n k S H : ℕ} (hk : 0 < k) (mu : Fin k → ℝ)
    (P : Measure (((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ)) ×
      (Fin (H-S) → Fin n → Fin k))) [IsFiniteMeasure P] :
    Integrable (fun z => learnerRegret hk mu z.1.1 z.2) P := by
  let f : ((Fin S → Fin n → Fin k) × (Fin (H-S) → Fin n → Fin k)) → ℝ :=
    fun w => learnerRegret hk mu w.1 w.2
  have hi : Integrable f (P.map (fun z => (z.1.1,z.2))) := Integrable.of_finite
  exact hi.comp_measurable (measurable_fst.fst.prodMk measurable_snd)

theorem integrable_pathRegret_projection {n k S L : ℕ} (hk : 0 < k)
    (A : Finset (Fin k)) (mu : Fin k → ℝ)
    (P : Measure (((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ)) ×
      (Fin L → Fin n → Fin k))) [IsFiniteMeasure P] :
    Integrable (fun z => pathCoordinationRegret hk A mu z.2) P := by
  exact (Integrable.of_finite (f := pathCoordinationRegret hk A mu)
    (μ := P.map Prod.snd)).comp_measurable measurable_snd

theorem learnerRegret_good_integral_le {n k S H : ℕ} (hk : 1 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (hne : (topArms mu n).Nonempty)
    (E : Set ((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) (topArms mu n)) :
    (∫ z in Prod.fst ⁻¹' E, learnerRegret (n := n) (by omega) mu z.1.1 z.2
      ∂explorationContinuationLaw hk nu (H-S)) ≤
    (explorationRewardLaw (by omega) nu E).toReal *
      ((n : ℝ)*min H S + 8*(n : ℝ)^2) := by
  let P := explorationContinuationLaw (n := n) (T := S) hk nu (H-S)
  have hi := integrable_learnerRegret (H := H) (S := S) (by omega) mu P
  have hp := integrable_pathRegret_projection (S := S) (L := H-S) (by omega) (topArms mu n) mu P
  have hm := integral_mono (μ := P.restrict (Prod.fst ⁻¹' E)) hi.integrableOn
    ((integrable_const ((n : ℝ)*min H S)).add hp.integrableOn)
    (fun z => learnerRegret_le_exploration_add (by omega) mu hnk hmu z.1.1 z.2)
  change (∫ z in Prod.fst ⁻¹' E, learnerRegret (n := n) (by omega) mu z.1.1 z.2 ∂P) ≤ _
  calc
    _ ≤ ∫ z in Prod.fst ⁻¹' E,
        ((n : ℝ)*min H S + pathCoordinationRegret (by omega) (topArms mu n) mu z.2) ∂P := hm
    _ = (explorationRewardLaw (by omega) nu E).toReal * ((n : ℝ)*min H S) +
        (explorationRewardLaw (by omega) nu E).toReal *
          ∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin n => topArms mu n) (fun _ => hne)) (H-S) d).toReal *
            pathCoordinationRegret (by omega) (topArms mu n) mu d := by
      rw [integral_add (integrable_const _) hp.integrableOn, integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      rw [explorationContinuationLaw_fst_event hk nu E hE,
        explorationContinuationLaw_good_regret_integral hk nu (topArms mu n) hne mu E hE hEG]
    _ ≤ _ := by
      have hb := iid_path_regret_le (n := n) (L := H-S) (by omega)
        (topArms mu n) hne (by simp [topArms_card, min_eq_left hnk]) mu hmu
      nlinarith [ENNReal.toReal_nonneg (a := explorationRewardLaw (by omega) nu E)]

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem learnerRegret_expected_le {n k S H : ℕ} (hk : 1 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (hne : (topArms mu n).Nonempty)
    (E : Set ((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) (topArms mu n))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hprob : 1-ENNReal.ofReal delta ≤ explorationRewardLaw (by omega) nu E) :
    (∫ z, learnerRegret (n := n) (by omega) mu z.1.1 z.2 ∂explorationContinuationLaw hk nu (H-S)) ≤
      min ((n : ℝ)*H) ((n : ℝ)*min H S + 8*(n : ℝ)^2 + delta*((n : ℝ)*H)) := by
  let P := explorationContinuationLaw (n := n) (T := S) hk nu (H-S)
  let F : Set (((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ)) ×
      (Fin (H-S) → Fin n → Fin k)) := Prod.fst ⁻¹' E
  have hF : MeasurableSet F := hE.preimage measurable_fst
  have hi := integrable_learnerRegret (H := H) (S := S) (by omega) mu P
  have hb (z : ((Fin S → Fin n → Fin k) × (Fin S → Fin k → ℝ)) ×
      (Fin (H-S) → Fin n → Fin k)) :=
    (learnerRegret_bounds (by omega) mu hnk hmu z.1.1 z.2).2
  apply le_min
  · have hm := integral_mono hi (integrable_const ((n : ℝ)*H)) hb
    simpa [P] using hm
  · have hpF : 1-ENNReal.ofReal delta ≤ P F := by
      rw [explorationContinuationLaw_fst_event hk nu E hE]
      exact hprob
    have hcompl : P Fᶜ ≤ ENNReal.ofReal delta := by
      rw [measure_compl hF (measure_ne_top _ _), measure_univ]
      apply tsub_le_iff_right.mpr
      simpa [add_comm] using (tsub_le_iff_right.mp hpF)
    have hcomplR : (P Fᶜ).toReal ≤ delta := ENNReal.toReal_le_of_le_ofReal hdelta hcompl
    have hbad : (∫ z in Fᶜ, learnerRegret (n := n) (by omega) mu z.1.1 z.2 ∂P) ≤
        delta*((n : ℝ)*H) := by
      have hm := integral_mono (μ := P.restrict Fᶜ) hi.integrableOn
        (integrable_const ((n : ℝ)*H)) hb
      rw [integral_const] at hm
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hm
      exact hm.trans (mul_le_mul_of_nonneg_right hcomplR (by positivity))
    have hmass : (explorationRewardLaw (by omega) nu E).toReal ≤ 1 := by
      apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
      simpa using (measure_mono (μ := explorationRewardLaw (by omega) nu) (Set.subset_univ E))
    have hgood : (∫ z in F, learnerRegret (n := n) (by omega) mu z.1.1 z.2 ∂P) ≤
        (n : ℝ)*min H S + 8*(n : ℝ)^2 := by
      apply (learnerRegret_good_integral_le hk hnk nu mu hmu hne E hE hEG).trans
      simpa using mul_le_mul_of_nonneg_right hmass
        (show 0 ≤ (n : ℝ)*min H S + 8*(n : ℝ)^2 by positivity)
    change (∫ z, learnerRegret (n := n) (by omega) mu z.1.1 z.2 ∂P) ≤ _
    rw [← integral_add_compl hF hi]
    exact add_le_add hgood hbad

theorem source_expected_learnerRegret_le {n k H : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (∫ z, learnerRegret (n := n) (S := explorationLength k eps delta) (H := H) (by omega)
      (armMean nu) z.1.1 z.2
      ∂explorationContinuationLaw (by omega) nu (H-explorationLength k eps delta)) ≤
    min ((n : ℝ)*H) ((n : ℝ)*min H (explorationLength k eps delta) +
      8*(n : ℝ)^2 + delta*((n : ℝ)*H)) := by
  have hc : (topArms (armMean nu) n).card = n := by
    simp [topArms_card,min_eq_left hnk.le]
  have hne : (topArms (armMean nu) n).Nonempty := Finset.card_pos.mp (by omega)
  exact learnerRegret_expected_le (by omega) hnk.le nu (armMean nu)
    (fun a => armMean_mem_unitInterval nu hb a) hne
    (explorationGoodEvent (n := n) (T := explorationLength k eps delta) (trueTopArms nu n))
    (measurableSet_explorationGoodEvent _ hc) (Set.Subset.refl _) delta hdelta.le
    (explorationGoodEvent_orderStatistic_probability hn hnk nu hb eps delta heps hepsgap hdelta hdelta1)

theorem source_conditional_learnerRegret_le {n k H : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (∫ z in Prod.fst ⁻¹' (explorationGoodEvent (n := n)
      (T := explorationLength k eps delta) (trueTopArms nu n)),
      learnerRegret (H := H) (by omega) (armMean nu) z.1.1 z.2
        ∂explorationContinuationLaw (by omega) nu (H-explorationLength k eps delta)) /
      (explorationContinuationLaw (by omega) nu (H-explorationLength k eps delta)
        (Prod.fst ⁻¹' (explorationGoodEvent (n := n)
          (T := explorationLength k eps delta) (trueTopArms nu n)))).toReal ≤
        (n : ℝ)*min H (explorationLength k eps delta) + 8*(n : ℝ)^2 := by
  have hc : (topArms (armMean nu) n).card = n := by
    simp [topArms_card,min_eq_left hnk.le]
  have hne : (topArms (armMean nu) n).Nonempty := Finset.card_pos.mp (by omega)
  have hE := measurableSet_explorationGoodEvent (T := explorationLength k eps delta) (trueTopArms nu n) hc
  rw [explorationContinuationLaw_fst_event _ nu _ hE]
  have hpos := explorationGoodEvent_positive hn hnk nu hb eps delta heps hepsgap hdelta hdelta1
  apply (div_le_iff₀ (ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _))).mpr
  simpa only [mul_comm] using learnerRegret_good_integral_le (H := H) (by omega) hnk.le nu
    (armMean nu) (fun a => armMean_mem_unitInterval nu hb a) hne _ hE (Set.Subset.refl _)

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem source_expected_learnerRegret_coarse {n k H : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (∫ z, learnerRegret (n := n) (S := explorationLength k eps delta) (H := H) (by omega)
      (armMean nu) z.1.1 z.2
      ∂explorationContinuationLaw (by omega) nu (H-explorationLength k eps delta)) ≤
    min ((n : ℝ)*H) ((n : ℝ)*explorationLength k eps delta +
      8*(n : ℝ)^2 + delta*((n : ℝ)*H)) := by
  apply (source_expected_learnerRegret_le hn hnk nu hb eps delta heps hepsgap hdelta hdelta1).trans
  apply min_le_min le_rfl
  have hc : ((min H (explorationLength k eps delta) : ℕ) : ℝ) ≤ explorationLength k eps delta :=
    by exact_mod_cast (Nat.min_le_right H (explorationLength k eps delta))
  nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ (n : ℝ) by positivity)]

theorem coordination_residual_source_constant (n : ℕ) :
    8*(n : ℝ)^2 ≤ 2*Real.exp 2*(n : ℝ)^2 := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    convert Real.exp_add (1 : ℝ) 1 using 1
    norm_num
  have hc : (8 : ℝ) ≤ 2*Real.exp 2 := by rw [hsq]; nlinarith
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem source_expected_learnerRegret_published_residual {n k H : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (∫ z, learnerRegret (n := n) (S := explorationLength k eps delta) (H := H) (by omega)
      (armMean nu) z.1.1 z.2
      ∂explorationContinuationLaw (by omega) nu (H-explorationLength k eps delta)) ≤
    min ((n : ℝ)*H) ((n : ℝ)*explorationLength k eps delta +
      2*Real.exp 2*(n : ℝ)^2 + delta*((n : ℝ)*H)) := by
  apply (source_expected_learnerRegret_coarse hn hnk nu hb eps delta heps hepsgap hdelta hdelta1).trans
  apply min_le_min le_rfl
  linarith [coordination_residual_source_constant n]

theorem source_expected_learnerRegret_inverse_horizon {n k H : ℕ} (hn : 0 < n) (hnk : n < k)
    (hH : 2 ≤ H) (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk) :
    (∫ z, learnerRegret (n := n) (S := explorationLength k eps (1/(H : ℝ))) (H := H) (by omega)
      (armMean nu) z.1.1 z.2
      ∂explorationContinuationLaw (by omega) nu (H-explorationLength k eps (1/(H : ℝ)))) ≤
    min ((n : ℝ)*H) ((n : ℝ)*explorationLength k eps (1/(H : ℝ)) +
      8*(n : ℝ)^2 + n) := by
  have hHr : (1 : ℝ) < H := by exact_mod_cast (show 1 < H by omega)
  have hz : (H : ℝ) ≠ 0 := by positivity
  have hd : 0 < 1/(H : ℝ) := by positivity
  have hd1 : 1/(H : ℝ) < 1 := (div_lt_one (by positivity)).mpr hHr
  have h := source_expected_learnerRegret_coarse (H := H) hn hnk nu hb eps
    (1/(H : ℝ)) heps hepsgap hd hd1
  have hr : 1/(H : ℝ)*((n : ℝ)*H) = n := by field_simp
  simpa only [hr] using h

end BanditRLProof.MusicalChairs


namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem source_conditional_learnerRegret_published_residual {n k H : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hSH : explorationLength k eps delta ≤ H) :
    (∫ z in Prod.fst ⁻¹' (explorationGoodEvent (n := n)
      (T := explorationLength k eps delta) (trueTopArms nu n)),
      learnerRegret (H := H) (by omega) (armMean nu) z.1.1 z.2
        ∂explorationContinuationLaw (by omega) nu (H-explorationLength k eps delta)) /
      (explorationContinuationLaw (by omega) nu (H-explorationLength k eps delta)
        (Prod.fst ⁻¹' (explorationGoodEvent (n := n)
          (T := explorationLength k eps delta) (trueTopArms nu n)))).toReal ≤
        (n : ℝ)*explorationLength k eps delta + 2*Real.exp 2*(n : ℝ)^2 := by
  have h := source_conditional_learnerRegret_le (H := H) hn hnk nu hb eps delta heps hepsgap hdelta hdelta1
  rw [min_eq_right hSH] at h
  exact h.trans (add_le_add le_rfl (coordination_residual_source_constant n))

end BanditRLProof.MusicalChairs
