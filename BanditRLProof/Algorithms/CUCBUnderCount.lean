import BanditRLProof.Algorithms.CUCBGapInverse
import BanditRLProof.Algorithms.CUCBRegretDecomposition

/-! Actual distinct charged counters and the refined under-sampling gap-tail
cardinality. No count bound is supplied as a source-model hypothesis. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace ChargeData
variable {A : Type*} {m : ℕ} (C : ChargeData A m)

theorem counters_monotone (actions : ℕ → A) (i : Fin m) :
    Monotone (fun n => C.counters actions n i) :=
  monotone_nat_of_le_succ (fun n => C.counters_mono_step actions n i)

theorem counters_strict_of_charge (actions : ℕ → A) (i : Fin m) {t s : ℕ}
    (hts : t<s) (ht : C.choose (C.counters actions t) (actions t)=some i) :
    C.counters actions t i<C.counters actions s i := by
  have h := C.counters_monotone actions i (Nat.succ_le_of_lt hts)
  change C.counters actions (t+1) i≤C.counters actions s i at h
  rw [counters_succ, if_pos ht] at h
  omega

theorem counters_injOn_charges (actions : ℕ → A) (i : Fin m) :
    Set.InjOn (fun t => C.counters actions t i)
      {t | C.choose (C.counters actions t) (actions t)=some i} := by
  intro t ht s hs he
  change C.counters actions t i=C.counters actions s i at he
  rcases lt_trichotomy t s with h | h | h
  · have := C.counters_strict_of_charge actions i h ht
    omega
  · exact h
  · have := C.counters_strict_of_charge actions i h hs
    omega

theorem card_charges_le (actions : ℕ → A) (i : Fin m) (times : Finset ℕ)
    (B : ℝ) (hB : 0≤B)
    (hc : ∀t∈times, C.choose (C.counters actions t) (actions t)=some i)
    (hb : ∀t∈times, (C.counters actions t i : ℝ)≤B) : (times.card:ℝ)≤B+1 := by
  have hcard : times.card≤(Finset.range (⌊B⌋₊+1)).card := by
    apply Finset.card_le_card_of_injOn (fun t => C.counters actions t i)
    · intro t ht
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hB).mpr (hb t ht)))
    · exact (C.counters_injOn_charges actions i).mono hc
  rw [Finset.card_range] at hcard
  have hr : (times.card:ℝ)≤(⌊B⌋₊:ℝ)+1 := by exact_mod_cast hcard
  exact hr.trans (add_le_add (Nat.floor_le hB) le_rfl)

end ChargeData

namespace SourceModel
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

noncomputable def underChargeTimes (H : ℕ) (actions : ℕ → A) (i : Fin m) : Finset ℕ := by
  classical
  exact (Finset.range H).filter (fun t =>
    S.chargeData.choose (S.chargeData.counters actions t) (actions t)=some i ∧
    (S.chargeData.counters actions t i:ℝ)≤
      samplingThreshold H (S.inverseGap (actions t)) (M.minTrigger i))

theorem underChargeTimes_spec (H : ℕ) (actions : ℕ → A) (i : Fin m) {t : ℕ}
    (ht : t∈S.underChargeTimes H actions i) :
    t<H ∧ S.chargeData.choose (S.chargeData.counters actions t) (actions t)=some i ∧
      0<S.gap (actions t) ∧ i∈M.possible (actions t) ∧
      (S.chargeData.counters actions t i:ℝ)≤S.gapThreshold H (M.minTrigger i) (S.gap (actions t)) := by
  classical
  have h := Finset.mem_filter.mp ht
  have hb := S.chargeData.choose_mem _ _ i h.2.1
  have hg : 0<S.gap (actions t) := by
    simpa [chargeData, FeedbackModel.chargeData, bad] using hb.1
  refine ⟨Finset.mem_range.mp h.1,h.2.1,hg,hb.2,?_⟩
  simpa [gapThreshold,S.inverseAt_gap _ hg] using h.2.2

noncomputable def underChargeGapTail (H : ℕ) (actions : ℕ → A) (i : Fin m) (x : ℝ) : Finset ℕ := by
  classical
  exact (S.underChargeTimes H actions i).filter (fun t => x≤S.gap (actions t))

theorem card_underChargeGapTail_le (H : ℕ) (hH : 1≤H) (actions : ℕ → A) (i : Fin m)
    (x : ℝ) (hx : x∈S.gapDomain) :
    ((S.underChargeGapTail H actions i x).card:ℝ)≤S.gapThreshold H (M.minTrigger i) x+1 := by
  classical
  apply S.chargeData.card_charges_le actions i _ _
    (S.gapThreshold_nonneg H hH _ (M.minTrigger_pos i) hx)
  · intro t ht
    exact (S.underChargeTimes_spec H actions i (Finset.mem_filter.mp ht).1).2.1
  · intro t ht
    have h := Finset.mem_filter.mp ht
    have hs := S.underChargeTimes_spec H actions i h.1
    exact hs.2.2.2.2.trans (S.gapThreshold_antitone H hH _ (M.minTrigger_pos i) hx
      ⟨hs.2.2.1,gap_le_maxPositiveGap S.score M.trueInput S.alpha (actions t)⟩ h.2)

noncomputable def badActions (i : Fin m) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => 0<S.gap a ∧ i∈M.possible a)

theorem underChargeTimes_mem_badActions (H : ℕ) (actions : ℕ → A) (i : Fin m) {t : ℕ}
    (ht : t∈S.underChargeTimes H actions i) : actions t∈S.badActions i := by
  classical
  have h := S.underChargeTimes_spec H actions i ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.2.1,h.2.2.2.1⟩

theorem underChargeTimes_empty_of_no_bad (H : ℕ) (actions : ℕ → A) (i : Fin m)
    (hi : S.badActions i=∅) : S.underChargeTimes H actions i=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h := S.underChargeTimes_mem_badActions H actions i ht
  rw [hi] at h
  exact Finset.notMem_empty _ h

noncomputable def minBadGap (i : Fin m) (hi : (S.badActions i).Nonempty) : ℝ :=
  (S.badActions i).inf' hi S.gap

noncomputable def maxBadGap (i : Fin m) (hi : (S.badActions i).Nonempty) : ℝ :=
  (S.badActions i).sup' hi S.gap

theorem badGap_bounds (i : Fin m) (hi : (S.badActions i).Nonempty) :
    S.minBadGap i hi∈S.gapDomain ∧ S.maxBadGap i hi∈S.gapDomain ∧
      S.minBadGap i hi≤S.maxBadGap i hi := by
  classical
  have hpos : 0<S.minBadGap i hi := (Finset.lt_inf'_iff hi).mpr
    (fun a ha => (Finset.mem_filter.mp ha).2.1)
  have hmax : S.maxBadGap i hi≤maxPositiveGap S.score M.trueInput S.alpha :=
    Finset.sup'_le _ _ (fun a _ => gap_le_maxPositiveGap S.score M.trueInput S.alpha a)
  have hiCopy := hi
  obtain ⟨a,ha⟩ := hiCopy
  have hle : S.minBadGap i hi≤S.maxBadGap i hi :=
    (Finset.inf'_le S.gap ha).trans (Finset.le_sup' S.gap ha)
  exact ⟨⟨hpos,hle.trans hmax⟩,⟨hpos.trans_le hle,hmax⟩,hle⟩

end SourceModel
end BanditRLProof.CUCB
