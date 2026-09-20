import BanditRLProof.Algorithms.MusicalChairsCoordinationTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Finset.Sort
import BanditRLProof.Algorithms.MusicalChairsPopulation

open scoped Classical ENNReal
set_option autoImplicit false

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


