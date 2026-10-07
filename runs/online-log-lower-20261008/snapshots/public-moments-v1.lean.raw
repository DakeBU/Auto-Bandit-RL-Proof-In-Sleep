import BanditRLProof.OnlineLearningMean
import BanditRLProof.OnlineLearningRegret
import BanditRLProof.Exp3ConditionalMoments
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Vector
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Finset Set
namespace BanditRL.OnlineLearning.GuessingLower

/-- History is newest-first: adding b records the next revealed bit after the prediction. -/
noncomputable def polyaNext (h : List Bool) : ℝ :=
  ((h.count true : ℝ) + 1) / ((h.length : ℝ) + 2)

/-- Actual recursively generated path mass; it does not depend on a learner or seed. -/
noncomputable def pathWeight (h : List Bool) : ℝ :=
  match h with
  | [] => 1
  | b :: past => pathWeight past * (if b then polyaNext past else 1 - polyaNext past)

/-- Convert newest-first finite history into chronological labels, padded by false after its end. -/
def binaryStream (h : List Bool) (t : ℕ) : Bool :=
  (h.reverse[t]?).getD false

def binaryValues (h : List Bool) (t : ℕ) : ℝ :=
  if binaryStream h t then 1 else 0

/-- One policy of strict-past labels; no current label or future sequence is passed to A. -/
noncomputable def causalPredict (A : List Bool → ℝ) (y : ℕ → Bool) (t : ℕ) : ℝ :=
  A (List.ofFn (fun i : Fin t => y i)).reverse

/-- Actual shared comparator regret against the feasible empirical-mean hindsight minimizer. -/
noncomputable def pathRegret (A : List Bool → ℝ) (h : List Bool) : ℝ :=
  comparatorRegret (fun t x => (x - binaryValues h t)^2)
    (causalPredict A (binaryStream h)) (empiricalMean (binaryValues h) h.length) h.length

noncomputable def pathExpectation (T : ℕ) (f : List Bool → ℝ) : ℝ :=
  ∑ v : List.Vector Bool T, pathWeight v.toList * f v.toList

/-- Same finite-action Dirac law as the shared Bandit library, instantiated at binary histories. -/
noncomputable def prefixMeasure (T : ℕ) [MeasurableSpace (List.Vector Bool T)] :
    Measure (List.Vector Bool T) :=
  BanditRLProof.Exp3.finiteActionMeasure univ (fun v => pathWeight v.toList)

theorem probability_mem (h : List Bool) :
    polyaNext h ∈ Ioo (0 : ℝ) 1 := by
  have hc : (h.count true : ℝ) ≤ (h.length : ℝ) := by
    exact_mod_cast (List.count_le_length (a := true) (l := h))
  have hd : (0 : ℝ) < (h.length : ℝ) + 2 := by positivity
  change 0 < ((h.count true : ℝ) + 1) / ((h.length : ℝ) + 2) ∧
    ((h.count true : ℝ) + 1) / ((h.length : ℝ) + 2) < 1
  constructor
  · exact div_pos (by positivity) hd
  · exact (div_lt_one hd).mpr (by linarith)

theorem branch_mass (h : List Bool) :
    pathWeight (false :: h) + pathWeight (true :: h) = pathWeight h := by
  simp only [pathWeight, Bool.false_eq_true, ↓reduceIte]
  ring

theorem pathWeight_nonneg (h : List Bool) :
    0 ≤ pathWeight h := by
  induction h with
  | nil => norm_num [pathWeight]
  | cons b h ih =>
    cases b
    · exact mul_nonneg ih (sub_nonneg.mpr (probability_mem h).2.le)
    · exact mul_nonneg ih (probability_mem h).1.le

/-- Split all newest-first histories into the next bit and the prior history. -/
private def vectorConsEquiv (T : ℕ) :
    Bool × List.Vector Bool T ≃ List.Vector Bool (T + 1) where
  toFun p := p.1 ::ᵥ p.2
  invFun v := (v.head, v.tail)
  left_inv p := by cases p; simp
  right_inv v := List.Vector.cons_head_tail v

theorem sum_vectors_succ (T : ℕ) (f : List Bool → ℝ) :
    (∑ v : List.Vector Bool (T + 1), f v.toList) =
      ∑ v : List.Vector Bool T, (f (false :: v.toList) + f (true :: v.toList)) := by
  rw [← (vectorConsEquiv T).sum_comp (fun v => f v.toList)]
  rw [Fintype.sum_prod_type]
  simp [vectorConsEquiv, Finset.sum_add_distrib, add_comm]

theorem prefix_mass_one (T : ℕ) :
    (∑ v : List.Vector Bool T, pathWeight v.toList) = 1 := by
  induction T with
  | zero => simp [pathWeight]
  | succ T ih =>
    rw [sum_vectors_succ]
    simpa only [branch_mass] using ih

theorem prefix_distribution (T : ℕ) :
    BanditRLProof.Exp3.FiniteActionDistribution (univ : Finset (List.Vector Bool T)) (fun v => pathWeight v.toList) := by
  constructor
  · intro v _
    exact pathWeight_nonneg v.toList
  · exact prefix_mass_one T

theorem prefixMeasure_probability (T : ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] :
    IsProbabilityMeasure (prefixMeasure T) := by
  exact BanditRLProof.Exp3.finiteActionMeasure_isProbabilityMeasure
    univ (fun v : List.Vector Bool T => pathWeight v.toList) (prefix_distribution T)

theorem pathExpectation_integral (T : ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] (f : List Bool → ℝ) :
    (∫ v, f v.toList ∂prefixMeasure T) = pathExpectation T f := by
  exact BanditRLProof.Exp3.integral_finiteActionMeasure_eq_sum
    univ (fun v : List.Vector Bool T => pathWeight v.toList) (prefix_distribution T) (fun v => f v.toList)


theorem pathExpectation_congr (T : ℕ) (f g : List Bool → ℝ)
    (hfg : ∀ h, h.length = T → f h = g h) :
    pathExpectation T f = pathExpectation T g := by
  apply Finset.sum_congr rfl
  intro v _
  rw [hfg v.toList v.toList_length]

theorem pathExpectation_const (T : ℕ) (c : ℝ) :
    pathExpectation T (fun _ => c) = c := by
  simp only [pathExpectation, ← Finset.sum_mul, prefix_mass_one, one_mul]

theorem pathExpectation_add (T : ℕ) (f g : List Bool → ℝ) :
    pathExpectation T (fun h => f h + g h) = pathExpectation T f + pathExpectation T g := by
  simp only [pathExpectation, mul_add, Finset.sum_add_distrib]

theorem pathExpectation_sub (T : ℕ) (f g : List Bool → ℝ) :
    pathExpectation T (fun h => f h - g h) = pathExpectation T f - pathExpectation T g := by
  simp only [pathExpectation, mul_sub, Finset.sum_sub_distrib]

theorem pathExpectation_const_mul (T : ℕ) (c : ℝ) (f : List Bool → ℝ) :
    pathExpectation T (fun h => c * f h) = c * pathExpectation T f := by
  simp only [pathExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem pathExpectation_div (T : ℕ) (f : List Bool → ℝ) (c : ℝ) :
    pathExpectation T (fun h => f h / c) = pathExpectation T f / c := by
  simp only [pathExpectation, mul_div_assoc, Finset.sum_div]

/-- Actual successor expectation under the recursively generated branch masses. -/
theorem pathExpectation_succ (T : ℕ) (f : List Bool → ℝ) :
    pathExpectation (T + 1) f = pathExpectation T
      (fun h => (1 - polyaNext h) * f (false :: h) + polyaNext h * f (true :: h)) := by
  rw [pathExpectation, sum_vectors_succ T (fun h => pathWeight h * f h)]
  unfold pathExpectation
  apply Finset.sum_congr rfl
  intro v _
  simp only [pathWeight, Bool.false_eq_true, ↓reduceIte]
  ring

theorem heads_succ (T : ℕ) :
    pathExpectation (T + 1) (fun h => (h.count true : ℝ)) =
      pathExpectation T (fun h => (h.count true : ℝ)) +
        (pathExpectation T (fun h => (h.count true : ℝ)) + 1) / ((T : ℝ) + 2) := by
  rw [pathExpectation_succ]
  have eq := pathExpectation_congr T
    (fun h => (1 - polyaNext h) * ((false :: h).count true : ℝ) +
      polyaNext h * ((true :: h).count true : ℝ))
    (fun h => (h.count true : ℝ) + ((h.count true : ℝ) + 1) / ((T : ℝ) + 2))
    (by
      intro h hl
      simp [List.count_cons, polyaNext, hl]
      ring)
  rw [eq]
  simp only [pathExpectation_add, pathExpectation_div, pathExpectation_const]

theorem heads_sq_succ (T : ℕ) :
    pathExpectation (T + 1) (fun h => (h.count true : ℝ)^2) =
      pathExpectation T (fun h => (h.count true : ℝ)^2) +
        (2 * pathExpectation T (fun h => (h.count true : ℝ)^2) +
         3 * pathExpectation T (fun h => (h.count true : ℝ)) + 1) / ((T : ℝ) + 2) := by
  rw [pathExpectation_succ]
  have eq := pathExpectation_congr T
    (fun h => (1 - polyaNext h) * ((false :: h).count true : ℝ)^2 +
      polyaNext h * ((true :: h).count true : ℝ)^2)
    (fun h => (h.count true : ℝ)^2 +
      (2 * (h.count true : ℝ)^2 + 3 * (h.count true : ℝ) + 1) / ((T : ℝ) + 2))
    (by
      intro h hl
      have hd : (T : ℝ) + 2 ≠ 0 := by positivity
      simp [polyaNext, hl]
      field_simp <;> ring)
  rw [eq]
  simp only [pathExpectation_add, pathExpectation_div, pathExpectation_const,
    pathExpectation_const_mul]

theorem expected_heads (T : ℕ) :
    pathExpectation T (fun h => (h.count true : ℝ)) = (T : ℝ) / 2 := by
  induction T with
  | zero => simp [pathExpectation, pathWeight]
  | succ T ih =>
    rw [heads_succ, ih]
    push_cast
    have hd : (T : ℝ) + 2 ≠ 0 := by positivity
    field_simp <;> ring

theorem expected_heads_sq (T : ℕ) :
    pathExpectation T (fun h => (h.count true : ℝ)^2) = (T : ℝ) * (2 * (T : ℝ) + 1) / 6 := by
  induction T with
  | zero => simp [pathExpectation, pathWeight]
  | succ T ih =>
    rw [heads_sq_succ, ih, expected_heads]
    push_cast
    have hd : (T : ℝ) + 2 ≠ 0 := by positivity
    field_simp <;> ring

theorem expected_next_variance (T : ℕ) :
    pathExpectation T (fun h => polyaNext h * (1 - polyaNext h)) = ((T : ℝ) + 3) / (6 * ((T : ℝ) + 2)) := by
  have hd : (T : ℝ) + 2 ≠ 0 := by positivity
  have eq := pathExpectation_congr T
    (fun h => polyaNext h * (1 - polyaNext h))
    (fun h => ((T : ℝ) * (h.count true : ℝ) + ((T : ℝ) + 1) -
      (h.count true : ℝ)^2) / ((T : ℝ) + 2)^2)
    (by
      intro h hl
      dsimp only
      simp only [polyaNext, hl]
      field_simp
      ring)
  rw [eq]
  simp only [pathExpectation_div, pathExpectation_sub, pathExpectation_add,
    pathExpectation_const_mul, pathExpectation_const, expected_heads, expected_heads_sq]
  field_simp <;> ring

end BanditRL.OnlineLearning.GuessingLower
