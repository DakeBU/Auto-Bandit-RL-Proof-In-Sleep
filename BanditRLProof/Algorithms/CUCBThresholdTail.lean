import BanditRLProof.Algorithms.CUCBSourceModel

/-! Exact source threshold crossing converted into an actual fixed-count
observation-shortfall probability, with decision time n+1 and horizon H. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem probabilistic_threshold_crossing (H n : ℕ) (hH : n+1≤H)
    (u p k : ℝ) (hu : 0<u) (hp : 0<p) (hp1 : p≠1)
    (hk : samplingThreshold H u p<k) :
    0<k ∧ 6*Real.log ((n:ℝ)+1)/u^2<k*p/2 ∧
      -k*p/8≤-(3*Real.log ((n:ℝ)+1)) := by
  have hH1 : 1≤H := by omega
  have hlogH : 0≤Real.log (H:ℝ) := Real.log_nonneg (by exact_mod_cast hH1)
  have hlog : Real.log ((n:ℝ)+1)≤Real.log (H:ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hH)
  rw [samplingThreshold_probabilistic hH1 hp1] at hk
  have h1 := lt_of_le_of_lt (le_max_left _ _) hk
  have h2 := lt_of_le_of_lt (le_max_right _ _) hk
  have hkp := (div_lt_iff₀ hp).1 h2
  have hx := (div_lt_iff₀ (mul_pos (sq_pos_of_pos hu) hp)).1 h1
  refine ⟨lt_of_le_of_lt (by positivity : (0:ℝ)≤24*Real.log (H:ℝ)/p) h2, ?_, ?_⟩
  · apply (div_lt_iff₀ (sq_pos_of_pos hu)).2
    nlinarith
  · nlinarith

namespace FeedbackModel
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] {m : ℕ}
variable (M : FeedbackModel A m)

include M in
omit [Fintype A] in
theorem arms_nonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
  obtain ⟨a⟩ := ‹Nonempty A›
  obtain ⟨i, _⟩ := M.possible_nonempty a
  exact ⟨i, Finset.mem_univ i⟩

noncomputable def globalMinTrigger : ℝ := Finset.univ.inf' M.arms_nonempty M.minTrigger

theorem globalMinTrigger_pos : 0<M.globalMinTrigger :=
  (Finset.lt_inf'_iff M.arms_nonempty).mpr (fun i _ => M.minTrigger_pos i)

theorem globalMinTrigger_le (i : Fin m) : M.globalMinTrigger≤M.minTrigger i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem globalMinTrigger_le_one : M.globalMinTrigger≤1 := by
  obtain ⟨i, _⟩ := M.arms_nonempty
  exact (M.globalMinTrigger_le i).trans (M.minTrigger_le_one i)

theorem globalMinTrigger_eq_one_iff : M.globalMinTrigger=1 ↔ ∀i, M.minTrigger i=1 := by
  constructor
  · intro h i
    exact le_antisymm (M.minTrigger_le_one i) (h ▸ M.globalMinTrigger_le i)
  · intro h
    apply le_antisymm M.globalMinTrigger_le_one
    exact Finset.le_inf' M.arms_nonempty M.minTrigger (fun i _ => (h i).ge)

end FeedbackModel

namespace SourceModel
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [StandardBorelSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

theorem trigger_shortfall_fixed_count (H n : ℕ) (hH : n+1≤H) (i : Fin m)
    (u k : ℝ) (hu : 0<u) (hp1 : M.minTrigger i≠1)
    (hk : samplingThreshold H u (M.minTrigger i)<k) :
    (cucbTrajectory S.oracle M.environment) {Y |
      k≤(S.chargeData.counters (fun t => (Y t).1) n i : ℝ) ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤6*Real.log ((n:ℝ)+1)/u^2} ≤
        ENNReal.ofReal (((n:ℝ)+1)^3)⁻¹ := by
  have h := probabilistic_threshold_crossing H n hH u (M.minTrigger i) k hu
    (M.minTrigger_pos i) hp1 hk
  have hs : {Y : ℕ → Round A m |
      k≤(S.chargeData.counters (fun t => (Y t).1) n i : ℝ) ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤6*Real.log ((n:ℝ)+1)/u^2} ⊆
      {Y | k≤(S.chargeData.counters (fun t => (Y t).1) n i : ℝ) ∧
        (observationCount (fun t => (Y t).2) n i : ℝ)≤k*M.minTrigger i/2} := by
    intro Y hY
    exact ⟨hY.1, hY.2.trans h.2.1.le⟩
  calc
    _ ≤ (cucbTrajectory S.oracle M.environment) {Y |
      k≤(S.chargeData.counters (fun t => (Y t).1) n i : ℝ) ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤k*M.minTrigger i/2} := measure_mono hs
    _ ≤ ENNReal.ofReal (Real.exp (-k*M.minTrigger i/8)) :=
      M.charged_observation_tail S.oracle S.bad S.inverseGap i n k h.1.le
    _ ≤ ENNReal.ofReal (Real.exp (-(3*Real.log ((n:ℝ)+1)))) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h.2.2)
    _ = _ := by
      rw [Real.exp_neg, show (3:ℝ)=((3:ℕ):ℝ) by norm_num, Real.exp_nat_mul,
        Real.exp_log (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]

/-- A single fixed-count tail covers every eligible action: minimize its positive
inverse gap before taking probabilities, instead of unioning over actions. -/
theorem trigger_shortfall_slice (H n : ℕ) (hH : n+1≤H) (i : Fin m)
    (hp1 : M.minTrigger i≠1) (k : ℕ) :
    (cucbTrajectory S.oracle M.environment) {Y |
      S.chargeData.counters (fun t => (Y t).1) n i=k ∧
      ∃a, 0<S.gap a ∧ i∈M.possible a ∧
        samplingThreshold H (S.inverseGap a) (M.minTrigger i)<k ∧
        (observationCount (fun t => (Y t).2) n i : ℝ)≤
          6*Real.log ((n:ℝ)+1)/(S.inverseGap a)^2} ≤
      ENNReal.ofReal (((n:ℝ)+1)^3)⁻¹ := by
  classical
  let eligible := Finset.univ.filter (fun a => 0<S.gap a ∧ i∈M.possible a ∧
    samplingThreshold H (S.inverseGap a) (M.minTrigger i)<k)
  by_cases he : eligible.Nonempty
  · obtain ⟨a₀, ha₀, hmin⟩ := eligible.exists_min_image S.inverseGap he
    have ha₀' := (Finset.mem_filter.mp ha₀).2
    have hu₀ := (S.inverseGap_spec a₀ ha₀'.1).1
    apply le_trans (measure_mono ?_) (S.trigger_shortfall_fixed_count H n hH i
      (S.inverseGap a₀) k hu₀ hp1 ha₀'.2.2)
    intro Y hY
    rcases hY with ⟨hk, a, ha, hi, hthreshold, hobs⟩
    refine ⟨by simp [hk], hobs.trans ?_⟩
    have hu := (S.inverseGap_spec a ha).1
    have hle := hmin a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hi, hthreshold⟩)
    apply div_le_div_of_nonneg_left
    · exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    · positivity
    · nlinarith
  · have hempty : {Y : ℕ → Round A m |
        S.chargeData.counters (fun t => (Y t).1) n i=k ∧
        ∃a, 0<S.gap a ∧ i∈M.possible a ∧
          samplingThreshold H (S.inverseGap a) (M.minTrigger i)<k ∧
          (observationCount (fun t => (Y t).2) n i : ℝ)≤
            6*Real.log ((n:ℝ)+1)/(S.inverseGap a)^2} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro Y ⟨_, a, ha, hi, ht, _⟩
      exact he ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hi, ht⟩⟩
    rw [hempty, measure_empty]
    exact bot_le

/-- The actual observation shortfall after crossing the source horizon threshold. -/
def TriggerShortfall (H n : ℕ) (i : Fin m) : Set (ℕ → Round A m) := {Y |
  ∃a, 0<S.gap a ∧ i∈M.possible a ∧
    samplingThreshold H (S.inverseGap a) (M.minTrigger i)<
      (S.chargeData.counters (fun t => (Y t).1) n i : ℝ) ∧
    (observationCount (fun t => (Y t).2) n i : ℝ)≤
      6*Real.log ((n:ℝ)+1)/(S.inverseGap a)^2}

theorem trigger_shortfall_probability (H n : ℕ) (hH : n+1≤H) (i : Fin m)
    (hp1 : M.minTrigger i≠1) :
    (cucbTrajectory S.oracle M.environment) (S.TriggerShortfall H n i) ≤
      ENNReal.ofReal ((((n:ℝ)+1)^2)⁻¹) := by
  let E : ℕ → Set (ℕ → Round A m) := fun k => {Y |
    S.chargeData.counters (fun t => (Y t).1) n i=k ∧
    ∃a, 0<S.gap a ∧ i∈M.possible a ∧
      samplingThreshold H (S.inverseGap a) (M.minTrigger i)<k ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤
        6*Real.log ((n:ℝ)+1)/(S.inverseGap a)^2}
  have hs : S.TriggerShortfall H n i ⊆ ⋃k∈Finset.range (n+1), E k := by
    intro Y hY
    refine Set.mem_iUnion.mpr ⟨S.chargeData.counters (fun t => (Y t).1) n i, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_, rfl, hY⟩
    exact Nat.lt_succ_of_le (S.chargeData.counters_le_time _ n i)
  calc
    _ ≤ (cucbTrajectory S.oracle M.environment) (⋃k∈Finset.range (n+1), E k) :=
      measure_mono hs
    _ ≤ ∑k∈Finset.range (n+1), (cucbTrajectory S.oracle M.environment) (E k) :=
      ProbabilityUnionBound.measure_biUnion_finset_le _ _ E
    _ ≤ ∑_k∈Finset.range (n+1), ENNReal.ofReal (((n:ℝ)+1)^3)⁻¹ := by
      exact Finset.sum_le_sum (fun k _ => S.trigger_shortfall_slice H n hH i hp1 k)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : (↑(n+1) : ENNReal)=ENNReal.ofReal ((n:ℝ)+1) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp
      rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

omit [StandardBorelSpace A] in
theorem trigger_shortfall_probability_of_one (H n : ℕ) (hH : n+1≤H) (i : Fin m)
    (hp : M.minTrigger i=1) :
    (cucbTrajectory S.oracle M.environment) (S.TriggerShortfall H n i)=0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [M.deterministic_counter_bound S.oracle S.bad S.inverseGap i hp] with Y hY
  rintro ⟨a, ha, hi, ht, hobs⟩
  have hu := (S.inverseGap_spec a ha).1
  have hlog : Real.log ((n:ℝ)+1)≤Real.log (H:ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hH)
  rw [hp, samplingThreshold_deterministic] at ht
  have hcount : (S.chargeData.counters (fun t => (Y t).1) n i : ℝ)≤
      (observationCount (fun t => (Y t).2) n i : ℝ) := by exact_mod_cast hY n
  have hdiv : 6*Real.log ((n:ℝ)+1)/(S.inverseGap a)^2≤
      6*Real.log (H:ℝ)/(S.inverseGap a)^2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num))
      (sq_nonneg (S.inverseGap a))
  linarith

/-- Sum only over base arms; the action family has already been absorbed in each
fixed-count tail. Deterministically observed arms contribute zero. -/
theorem trigger_shortfall_union_probability (H n : ℕ) (hH : n+1≤H) :
    (cucbTrajectory S.oracle M.environment) (⋃i, S.TriggerShortfall H n i) ≤
      ENNReal.ofReal ((m:ℝ)/((n:ℝ)+1)^2) := by
  classical
  calc
    _ ≤ ∑i:Fin m, (cucbTrajectory S.oracle M.environment) (S.TriggerShortfall H n i) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑_i:Fin m, ENNReal.ofReal ((((n:ℝ)+1)^2)⁻¹) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hp : M.minTrigger i=1
      · rw [S.trigger_shortfall_probability_of_one H n hH i hp]
        exact bot_le
      · exact S.trigger_shortfall_probability H n hH i hp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
      congr 1

omit [StandardBorelSpace A] in
theorem trigger_shortfall_union_probability_of_all_one (H n : ℕ) (hH : n+1≤H)
    (hp : ∀i, M.minTrigger i=1) :
    (cucbTrajectory S.oracle M.environment) (⋃i, S.TriggerShortfall H n i)=0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ ∑i:Fin m, (cucbTrajectory S.oracle M.environment) (S.TriggerShortfall H n i) :=
      measure_iUnion_fintype_le _ _
    _ = 0 := by simp [S.trigger_shortfall_probability_of_one H n hH, hp]

end SourceModel
end BanditRLProof.CUCB
