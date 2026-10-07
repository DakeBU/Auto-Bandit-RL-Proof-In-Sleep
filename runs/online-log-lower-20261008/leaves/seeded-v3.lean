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

theorem causalPredict_prefix (A : List Bool → ℝ) (y z : ℕ → Bool) (t : ℕ) (hpast : ∀ i < t, y i = z i) :
    causalPredict A y t = causalPredict A z t := by
  have hprefix : List.ofFn (fun i : Fin t => y i) = List.ofFn (fun i : Fin t => z i) := by
    apply congrArg List.ofFn
    funext i
    exact hpast i i.isLt
  exact congrArg (fun l => A l.reverse) hprefix

theorem binary_mean_minimizer (h : List Bool) (hpos : 0 < h.length) :
    empiricalMean (binaryValues h) h.length ∈ Icc (0 : ℝ) 1 ∧ ∀ u ∈ Icc (0 : ℝ) 1, (∑ t ∈ range h.length, (empiricalMean (binaryValues h) h.length - binaryValues h t)^2) ≤ ∑ t ∈ range h.length, (u - binaryValues h t)^2 := by
  have hy : ∀ t < h.length, binaryValues h t ∈ Icc (0 : ℝ) 1 := by
    intro t _
    unfold binaryValues
    split_ifs <;> norm_num
  exact ⟨empiricalMean_mem (binaryValues h) h.length hpos hy,
    fun u _ => empiricalMean_minimizes (binaryValues h) h.length hpos u⟩

theorem conditional_square_lower (h : List Bool) (x : ℝ) :
    polyaNext h * (1 - polyaNext h) ≤ (1 - polyaNext h) * x^2 + polyaNext h * (x - 1)^2 := by
  nlinarith [sq_nonneg (x - polyaNext h)]

theorem binaryStream_cons_prefix (b : Bool) (h : List Bool) (t : ℕ) (ht : t < h.length) :
    binaryStream (b :: h) t = binaryStream h t := by
  unfold binaryStream
  simp only [List.reverse_cons]
  rw [List.getElem?_append_left (by simpa using ht)]

theorem binaryStream_cons_last (b : Bool) (h : List Bool) :
    binaryStream (b :: h) h.length = b := by
  simp [binaryStream, List.reverse_cons, List.getElem?_append_right]

theorem binaryValues_cons_prefix (b : Bool) (h : List Bool) (t : ℕ) (ht : t < h.length) :
    binaryValues (b :: h) t = binaryValues h t := by
  simp only [binaryValues, binaryStream_cons_prefix b h t ht]

theorem causalPredict_history (A : List Bool → ℝ) (h : List Bool) :
    causalPredict A (binaryStream h) h.length = A h := by
  have hp : List.ofFn (fun i : Fin h.length => binaryStream h i) = h.reverse := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn]
      simp only [binaryStream, List.getElem?_eq_getElem hj, Option.getD_some]
  simp only [causalPredict, hp, List.reverse_reverse]

theorem causalPredict_cons_last (A : List Bool → ℝ) (b : Bool) (h : List Bool) :
    causalPredict A (binaryStream (b :: h)) h.length = A h := by
  rw [causalPredict_prefix A (binaryStream (b :: h)) (binaryStream h) h.length
    (binaryStream_cons_prefix b h)]
  exact causalPredict_history A h



/-- Source cumulative learner squared loss on exactly the decoded path. -/
noncomputable def pathLearnerLoss (A : List Bool → ℝ) (h : List Bool) : ℝ :=
  ∑ t ∈ range h.length, (causalPredict A (binaryStream h) t - binaryValues h t)^2

/-- Source best fixed squared loss, at the actual shared empirical-mean minimizer. -/
noncomputable def pathBestLoss (h : List Bool) : ℝ :=
  ∑ t ∈ range h.length, (empiricalMean (binaryValues h) h.length - binaryValues h t)^2

theorem pathRegret_eq_losses (A : List Bool → ℝ) (h : List Bool) :
    pathRegret A h = pathLearnerLoss A h - pathBestLoss h := rfl

theorem pathLearnerLoss_cons (A : List Bool → ℝ) (b : Bool) (h : List Bool) :
    pathLearnerLoss A (b :: h) = pathLearnerLoss A h + (A h - if b then 1 else 0)^2 := by
  unfold pathLearnerLoss
  rw [List.length_cons, Finset.sum_range_succ]
  have hp : (∑ t ∈ range h.length,
      (causalPredict A (binaryStream (b :: h)) t - binaryValues (b :: h) t)^2) =
      ∑ t ∈ range h.length, (causalPredict A (binaryStream h) t - binaryValues h t)^2 := by
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [binaryValues_cons_prefix b h t ht']
    rw [causalPredict_prefix A (binaryStream (b :: h)) (binaryStream h) t
      (fun i hi => binaryStream_cons_prefix b h i (hi.trans ht'))]
  rw [hp, causalPredict_cons_last]
  simp only [binaryValues, binaryStream_cons_last]

theorem binaryValues_sum (h : List Bool) :
    (∑ t ∈ range h.length, binaryValues h t) = (h.count true : ℝ) := by
  induction h with
  | nil => simp
  | cons b h ih =>
    rw [List.length_cons, Finset.sum_range_succ]
    have hp : (∑ t ∈ range h.length, binaryValues (b :: h) t) =
        ∑ t ∈ range h.length, binaryValues h t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact binaryValues_cons_prefix b h t (Finset.mem_range.mp ht)
    rw [hp, ih]
    cases b <;> simp [binaryValues, binaryStream_cons_last]

theorem binaryValues_sq (h : List Bool) (t : ℕ) :
    (binaryValues h t)^2 = binaryValues h t := by
  unfold binaryValues
  split_ifs <;> norm_num

theorem pathBestLoss_count (h : List Bool) (hpos : 0 < h.length) :
    pathBestLoss h = (h.count true : ℝ) - (h.count true : ℝ)^2 / (h.length : ℝ) := by
  have hn : (h.length : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hpos
  have hm : empiricalMean (binaryValues h) h.length = (h.count true : ℝ) / h.length := by
    simp only [empiricalMean, binaryValues_sum]
  have hz : (∑ t ∈ range h.length, ((0 : ℝ) - binaryValues h t)^2) = (h.count true : ℝ) := by
    calc
      _ = ∑ t ∈ range h.length, (binaryValues h t)^2 := by
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = ∑ t ∈ range h.length, binaryValues h t := by simp only [binaryValues_sq]
      _ = _ := binaryValues_sum h
  have hd := empiricalMean_decomposition (binaryValues h) h.length hpos 0
  have hr : (h.length : ℝ) * (0 - (h.count true : ℝ) / h.length)^2 =
      (h.count true : ℝ)^2 / h.length := by
    field_simp <;> ring
  rw [hz, hm, hr] at hd
  have hb : pathBestLoss h = ∑ t ∈ range h.length,
      ((h.count true : ℝ) / h.length - binaryValues h t)^2 := by
    simp only [pathBestLoss, hm]
  rw [← hb] at hd
  linarith

theorem expected_pathBestLoss (T : ℕ) (hT : 0 < T) :
    pathExpectation T pathBestLoss = ((T : ℝ) - 1) / 6 := by
  have hn : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  have eq := pathExpectation_congr T pathBestLoss
    (fun h => (h.count true : ℝ) - (h.count true : ℝ)^2 / (T : ℝ))
    (by
      intro h hl
      dsimp only
      rw [pathBestLoss_count h (by omega), hl])
  rw [eq]
  simp only [pathExpectation_sub, pathExpectation_div, expected_heads, expected_heads_sq]
  field_simp <;> ring

theorem pathExpectation_mono (T : ℕ) (f g : List Bool → ℝ)
    (hfg : ∀ h, h.length = T → f h ≤ g h) :
    pathExpectation T f ≤ pathExpectation T g := by
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (hfg v.toList v.toList_length) (pathWeight_nonneg v.toList)

theorem expected_pathLearnerLoss_succ (A : List Bool → ℝ) (T : ℕ) :
    pathExpectation (T + 1) (pathLearnerLoss A) =
      pathExpectation T (pathLearnerLoss A) + pathExpectation T
        (fun h => (1 - polyaNext h) * (A h)^2 + polyaNext h * (A h - 1)^2) := by
  rw [pathExpectation_succ]
  have eq := pathExpectation_congr T
    (fun h => (1 - polyaNext h) * pathLearnerLoss A (false :: h) +
      polyaNext h * pathLearnerLoss A (true :: h))
    (fun h => pathLearnerLoss A h +
      ((1 - polyaNext h) * (A h)^2 + polyaNext h * (A h - 1)^2))
    (by
      intro h _
      simp only [pathLearnerLoss_cons, Bool.false_eq_true, ↓reduceIte, sub_zero]
      ring)
  rw [eq, pathExpectation_add]

theorem expected_pathLearnerLoss_step (A : List Bool → ℝ) (T : ℕ) :
    pathExpectation T (pathLearnerLoss A) + ((T : ℝ) + 3) / (6 * ((T : ℝ) + 2)) ≤
      pathExpectation (T + 1) (pathLearnerLoss A) := by
  rw [expected_pathLearnerLoss_succ, ← expected_next_variance]
  exact add_le_add le_rfl (pathExpectation_mono T _ _
    (fun h _ => conditional_square_lower h (A h)))



theorem variance_sum (T : ℕ) :
    (∑ t ∈ range T, ((t : ℝ) + 3) / (6 * ((t : ℝ) + 2))) =
      (T : ℝ) / 6 + ((harmonic (T + 1) : ℝ) - 1) / 6 := by
  induction T with
  | zero => norm_num [harmonic]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ (T + 1)]
    push_cast
    have hd : (T : ℝ) + 2 ≠ 0 := by positivity
    field_simp <;> ring

theorem expected_pathLearnerLoss_lower (A : List Bool → ℝ) (T : ℕ) :
    (∑ t ∈ range T, ((t : ℝ) + 3) / (6 * ((t : ℝ) + 2))) ≤
      pathExpectation T (pathLearnerLoss A) := by
  induction T with
  | zero => simp [pathExpectation, pathLearnerLoss]
  | succ T ih =>
    rw [Finset.sum_range_succ]
    exact (add_le_add ih le_rfl).trans (expected_pathLearnerLoss_step A T)

theorem expected_pathRegret_lower (A : List Bool → ℝ) (T : ℕ) (hT : 0 < T) :
    (harmonic (T + 1) : ℝ) / 6 ≤ pathExpectation T (pathRegret A) := by
  have hl := expected_pathLearnerLoss_lower A T
  rw [variance_sum] at hl
  have ho := expected_pathBestLoss T hT
  have eq := pathExpectation_congr T (pathRegret A)
    (fun h => pathLearnerLoss A h - pathBestLoss h)
    (fun h _ => pathRegret_eq_losses A h)
  rw [eq, pathExpectation_sub, ho]
  linarith


theorem pathWeight_pos (h : List Bool) : 0 < pathWeight h := by
  induction h with
  | nil => norm_num [pathWeight]
  | cons b h ih =>
    cases b
    · exact mul_pos ih (sub_pos.mpr (probability_mem h).2)
    · exact mul_pos ih (probability_mem h).1

theorem square_loss_mem (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    (x - y)^2 ∈ Icc (0 : ℝ) 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have hleft : 0 ≤ 1 - (x - y) := by linarith [hx.1,hx.2,hy.1,hy.2]
  have hright : 0 ≤ 1 + (x - y) := by linarith [hx.1,hx.2,hy.1,hy.2]
  nlinarith [mul_nonneg hleft hright]

theorem square_loss_sum_mem (T : ℕ) (p y : ℕ → ℝ)
    (hp : ∀ t < T, p t ∈ Icc (0 : ℝ) 1) (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1) :
    (∑ t ∈ range T, (p t - y t)^2) ∈ Icc (0 : ℝ) T := by
  constructor
  · exact Finset.sum_nonneg (fun t _ => sq_nonneg _)
  · calc
      _ ≤ ∑ _t ∈ range T, (1 : ℝ) := Finset.sum_le_sum
        (fun t ht => (square_loss_mem _ _ (hp t (Finset.mem_range.mp ht))
          (hy t (Finset.mem_range.mp ht))).2)
      _ = _ := by simp

theorem pathRegret_abs_le (A : List Bool → ℝ) (h : List Bool)
    (hbound : ∀ k, A k ∈ Icc (0 : ℝ) 1) : |pathRegret A h| ≤ (h.length : ℝ) := by
  by_cases he : h.length = 0
  · have hn : h = [] := List.length_eq_zero_iff.mp he
    subst h
    simp [pathRegret, comparatorRegret]
  have hpos : 0 < h.length := Nat.pos_of_ne_zero he
  have hy : ∀ t < h.length, binaryValues h t ∈ Icc (0 : ℝ) 1 := by
    intro t _
    unfold binaryValues
    split_ifs <;> norm_num
  have hp : ∀ t < h.length, causalPredict A (binaryStream h) t ∈ Icc (0 : ℝ) 1 :=
    fun _ _ => hbound _
  have hm := (binary_mean_minimizer h hpos).1
  have hl := square_loss_sum_mem h.length (causalPredict A (binaryStream h)) (binaryValues h) hp hy
  have hb := square_loss_sum_mem h.length (fun _ => empiricalMean (binaryValues h) h.length)
    (binaryValues h) (fun _ _ => hm) hy
  rw [pathRegret_eq_losses, abs_le]
  change -(h.length : ℝ) ≤ _ ∧ _ ≤ (h.length : ℝ)
  constructor <;> dsimp [pathLearnerLoss,pathBestLoss] <;> linarith [hl.1,hl.2,hb.1,hb.2]

theorem pathRegret_measurable {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (h : List Bool) :
    Measurable (fun ω => pathRegret (A ω) h) := by
  unfold pathRegret comparatorRegret
  refine Measurable.sub ?_ measurable_const
  refine Finset.measurable_fun_sum _ (fun t _ => ?_)
  have hx : Measurable (fun ω => causalPredict (A ω) (binaryStream h) t - binaryValues h t) :=
    (hA _).sub measurable_const
  simpa only [pow_two] using hx.mul hx

theorem pathRegret_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ)
    (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1)
    (h : List Bool) : Integrable (fun ω => pathRegret (A ω) h) μ := by
  apply Integrable.of_bound (pathRegret_measurable A hA h).aestronglyMeasurable (h.length : ℝ)
  exact ae_of_all μ (fun ω => by
    simpa only [Real.norm_eq_abs] using pathRegret_abs_le (A ω) h (hbound ω))

theorem randomized_harmonic_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) :
    ∃ v : List.Vector Bool T, (harmonic (T + 1) : ℝ) / 6 ≤ ∫ ω, pathRegret (A ω) v.toList ∂μ := by
  classical
  let C : ℝ := (harmonic (T + 1) : ℝ) / 6
  let B : List.Vector Bool T → ℝ := fun v => ∫ ω, pathRegret (A ω) v.toList ∂μ
  have hi (v : List.Vector Bool T) : Integrable
      (fun ω => pathWeight v.toList * pathRegret (A ω) v.toList) μ :=
    (pathRegret_integrable μ A hA hbound v.toList).const_mul _
  have he : Integrable (fun ω => pathExpectation T (pathRegret (A ω))) μ :=
    integrable_finset_sum univ (fun v _ => hi v)
  have hmean : C ≤ ∑ v : List.Vector Bool T, pathWeight v.toList * B v := by
    have hb := integral_mono (integrable_const C) he
      (fun ω => expected_pathRegret_lower (A ω) T hT)
    rw [integral_const] at hb
    rw [show (∫ ω, pathExpectation T (pathRegret (A ω)) ∂μ) =
      ∑ v : List.Vector Bool T, pathWeight v.toList * B v from by
        unfold pathExpectation
        rw [integral_finset_sum univ (fun v _ => hi v)]
        simp only [integral_const_mul]
        rfl] at hb
    simpa only [probReal_univ, one_smul] using hb
  by_contra hnone
  have hlt : ∀ v : List.Vector Bool T, B v < C := by
    intro v
    exact lt_of_not_ge (fun hv => hnone ⟨v,hv⟩)
  have hsum : (∑ v : List.Vector Bool T, pathWeight v.toList * B v) < C := by
    calc
      _ < ∑ v : List.Vector Bool T, pathWeight v.toList * C :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun v _ => mul_lt_mul_of_pos_left (hlt v) (pathWeight_pos v.toList))
      _ = C := by rw [← Finset.sum_mul, prefix_mass_one, one_mul]
  exact (not_lt_of_ge hmean) hsum

theorem randomized_log_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) :
    ∃ v : List.Vector Bool T, Real.log ((T : ℝ) + 2) / 6 ≤ ∫ ω, pathRegret (A ω) v.toList ∂μ := by
  obtain ⟨v,hv⟩ := randomized_harmonic_lower μ A hA hbound T hT
  refine ⟨v,le_trans ?_ hv⟩
  have hl := log_add_one_le_harmonic (T + 1)
  have he : Real.log ((T : ℝ) + 2) ≤ (harmonic (T + 1) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hl
  exact div_le_div_of_nonneg_right he (by norm_num)


end BanditRL.OnlineLearning.GuessingLower
