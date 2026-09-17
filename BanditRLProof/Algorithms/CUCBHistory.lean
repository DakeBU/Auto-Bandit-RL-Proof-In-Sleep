import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The source CUCB statistics computed from chronological triggered feedback.
Index `n` uses exactly rounds `0,...,n-1`, so its source round number is `n+1`.
The reward coordinate is not used to estimate individual arm means. -/
namespace BanditRLProof.CUCB
open MeasureTheory
set_option autoImplicit false

abbrev UnitOutcome := Set.Icc (0 : ℝ) 1
abbrev Feedback (m : ℕ) := (Fin m → Bool) × ((Fin m → UnitOutcome) × ℝ)

def observation {m : ℕ} (z : Feedback m) (i : Fin m) : ℝ :=
  if z.1 i then (z.2.1 i : ℝ) else 0

def observationCount {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) : ℕ :=
  ∑ t ∈ Finset.range n, if (Y t).1 i then 1 else 0

noncomputable def observationSum {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) : ℝ :=
  ∑ t ∈ Finset.range n, observation (Y t) i

noncomputable def empiricalMean {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) : ℝ :=
  if observationCount Y n i = 0 then 1 else observationSum Y n i / observationCount Y n i

noncomputable def upperIndex {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) : ℝ :=
  if observationCount Y n i = 0 then 1 else
    min (empiricalMean Y n i + Real.sqrt (3*Real.log (n+1)/(2*observationCount Y n i))) 1

theorem observation_nonneg {m : ℕ} (z : Feedback m) (i : Fin m) :
    0≤observation z i := by
  unfold observation
  split_ifs
  · exact (z.2.1 i).property.1
  · rfl

theorem observationCount_succ {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) :
    observationCount Y (n+1) i = observationCount Y n i + if (Y n).1 i then 1 else 0 := by
  simp only [observationCount, Finset.sum_range_succ]

theorem observationSum_succ {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) :
    observationSum Y (n+1) i = observationSum Y n i + observation (Y n) i := by
  simp [observationSum, Finset.sum_range_succ]

theorem observationSum_nonneg {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) :
    0≤observationSum Y n i :=
  Finset.sum_nonneg (fun t _ => observation_nonneg (Y t) i)

theorem observationSum_le_count {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) :
    observationSum Y n i ≤ (observationCount Y n i : ℝ) := by
  induction n with
  | zero => simp [observationSum, observationCount]
  | succ n ih =>
    rw [observationSum_succ, observationCount_succ, Nat.cast_add]
    cases hm : (Y n).1 i
    · simpa [observation, hm] using ih
    · simp only [observation, hm, ↓reduceIte, Nat.cast_one]
      exact add_le_add ih ((Y n).2.1 i).property.2

theorem empiricalMean_le_one {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) :
    empiricalMean Y n i ≤ 1 := by
  unfold empiricalMean
  split_ifs with h
  · rfl
  · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).2
      (observationSum_le_count Y n i)

theorem empiricalMean_unobserved {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m)
    (h : (Y n).1 i=false) : empiricalMean Y (n+1) i=empiricalMean Y n i := by
  simp [empiricalMean, observationCount_succ, observationSum_succ, observation, h]

theorem empiricalMean_observed {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m)
    (h : (Y n).1 i=true) :
    empiricalMean Y (n+1) i =
      (observationSum Y n i + ((Y n).2.1 i : ℝ)) / ((observationCount Y n i : ℝ)+1) := by
  simp [empiricalMean, observationCount_succ, observationSum_succ, observation, h]

theorem empiricalMean_nonneg {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) :
    0≤empiricalMean Y n i := by
  unfold empiricalMean
  split_ifs
  · norm_num
  · exact div_nonneg (observationSum_nonneg Y n i) (Nat.cast_nonneg _)

theorem upperIndex_mem {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) :
    upperIndex Y n i ∈ Set.Icc (0:ℝ) 1 := by
  unfold upperIndex
  split_ifs
  · simp
  · exact ⟨le_min (add_nonneg (empiricalMean_nonneg Y n i) (Real.sqrt_nonneg _))
      (by norm_num), min_le_right _ _⟩

noncomputable def oracleInput {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) : Fin m → UnitOutcome :=
  fun i => ⟨upperIndex Y n i, upperIndex_mem Y n i⟩

theorem statistics_causal {m : ℕ} (Y Z : ℕ → Feedback m) (n : ℕ)
    (h : ∀t<n, Y t=Z t) (i : Fin m) :
    observationCount Y n i=observationCount Z n i ∧
    observationSum Y n i=observationSum Z n i := by
  constructor
  · apply Finset.sum_congr rfl
    intro t ht
    rw [h t (Finset.mem_range.mp ht)]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [h t (Finset.mem_range.mp ht)]

theorem oracleInput_causal {m : ℕ} (Y Z : ℕ → Feedback m) (n : ℕ)
    (h : ∀t<n, Y t=Z t) : oracleInput Y n=oracleInput Z n := by
  funext i
  apply Subtype.ext
  have hs := statistics_causal Y Z n h i
  simp only [oracleInput, upperIndex, empiricalMean, hs.1, hs.2]

/-- Masked latent values and the aggregate reward cannot leak into CUCB's
choice: only matching masks and matching observed arm values are needed. -/
theorem oracleInput_visible {m : ℕ} (Y Z : ℕ → Feedback m) (n : ℕ)
    (hm : ∀t<n, ∀i, (Y t).1 i=(Z t).1 i)
    (hx : ∀t<n, ∀i, (Y t).1 i=true → (Y t).2.1 i=(Z t).2.1 i) :
    oracleInput Y n=oracleInput Z n := by
  have hc (i : Fin m) : observationCount Y n i=observationCount Z n i := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hm t (Finset.mem_range.mp ht) i]
  have hs (i : Fin m) : observationSum Y n i=observationSum Z n i := by
    apply Finset.sum_congr rfl
    intro t ht
    have htm := hm t (Finset.mem_range.mp ht) i
    by_cases ho : (Y t).1 i=true
    · simp only [observation, ho, ← htm, ↓reduceIte, hx t (Finset.mem_range.mp ht) i ho]
    · simp [observation, ← htm, ho]
  funext i
  apply Subtype.ext
  simp only [oracleInput, upperIndex, empiricalMean, hc i, hs i]

theorem measurable_observation {m : ℕ} (i : Fin m) :
    Measurable (fun z : Feedback m => observation z i) := by
  unfold observation
  have hm : Measurable (fun z : Feedback m => z.1 i) := by fun_prop
  exact (by fun_prop : Measurable (fun z : Feedback m => (z.2.1 i : ℝ))).ite
    (hm (measurableSet_singleton true)) measurable_const

theorem measurable_observationCount {m : ℕ} (n : ℕ) (i : Fin m) :
    Measurable (fun Y : ℕ → Feedback m => observationCount Y n i) := by
  unfold observationCount
  apply Finset.measurable_sum
  intro t ht
  have hm : Measurable (fun Y : ℕ → Feedback m => (Y t).1 i) := by fun_prop
  exact measurable_const.ite (hm (measurableSet_singleton true)) measurable_const

theorem measurable_observationCount_real {m : ℕ} (n : ℕ) (i : Fin m) :
    Measurable (fun Y : ℕ → Feedback m => (observationCount Y n i : ℝ)) :=
  (measurable_of_countable (f := fun k : ℕ => (k:ℝ))).comp (measurable_observationCount n i)

theorem measurable_observationSum {m : ℕ} (n : ℕ) (i : Fin m) :
    Measurable (fun Y : ℕ → Feedback m => observationSum Y n i) := by
  unfold observationSum
  apply Finset.measurable_sum
  intro t ht
  exact (measurable_observation i).comp (measurable_pi_apply t)

theorem measurable_empiricalMean {m : ℕ} (n : ℕ) (i : Fin m) :
    Measurable (fun Y : ℕ → Feedback m => empiricalMean Y n i) := by
  unfold empiricalMean
  exact measurable_const.ite ((measurable_observationCount n i) (measurableSet_singleton 0))
    ((measurable_observationSum n i).div (measurable_observationCount_real n i))

theorem measurable_upperIndex {m : ℕ} (n : ℕ) (i : Fin m) :
    Measurable (fun Y : ℕ → Feedback m => upperIndex Y n i) := by
  unfold upperIndex
  apply measurable_const.ite ((measurable_observationCount n i) (measurableSet_singleton 0))
  exact ((measurable_empiricalMean n i).add
    (measurable_const.div (measurable_const.mul (measurable_observationCount_real n i))).sqrt).min
    measurable_const

theorem measurable_oracleInput {m : ℕ} (n : ℕ) :
    Measurable (fun Y : ℕ → Feedback m => oracleInput Y n) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_upperIndex n i).subtype_mk

end BanditRLProof.CUCB
