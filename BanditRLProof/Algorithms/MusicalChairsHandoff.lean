import BanditRLProof.Algorithms.MusicalChairsCoordinationTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Finset.Sort
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import BanditRLProof.Algorithms.MusicalChairsRanking

open scoped Classical ENNReal
set_option autoImplicit false

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


end BanditRLProof.MusicalChairs
