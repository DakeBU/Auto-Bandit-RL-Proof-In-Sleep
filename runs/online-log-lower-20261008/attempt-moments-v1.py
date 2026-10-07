from common_v1 import *
headers=load(CONTRACT/'planned-public-headers-v1.json')
aux='''
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
  rw [pathExpectation, sum_vectors_succ]
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
      simp only [List.count_cons, Bool.false_eq_true, Bool.true_eq_true, ↓reduceIte,
        Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, polyaNext, hl]
      field_simp
      ring)
  rw [eq]
  simp only [pathExpectation_add, pathExpectation_div, pathExpectation_const,
    pathExpectation_const_mul]

'''
bodies={
'expected_heads':''' := by
  induction T with
  | zero => simp [pathExpectation, pathWeight]
  | succ T ih =>
    rw [heads_succ, ih]
    push_cast
    have hd : (T : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
''',
'expected_heads_sq':''' := by
  induction T with
  | zero => simp [pathExpectation, pathWeight]
  | succ T ih =>
    rw [heads_sq_succ, ih, expected_heads]
    push_cast
    have hd : (T : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
''',
'expected_next_variance':''' := by
  have hd : (T : ℝ) + 2 ≠ 0 := by positivity
  have eq := pathExpectation_congr T
    (fun h => polyaNext h * (1 - polyaNext h))
    (fun h => ((T : ℝ) * (h.count true : ℝ) + ((T : ℝ) + 1) -
      (h.count true : ℝ)^2) / ((T : ℝ) + 2)^2)
    (by
      intro h hl
      unfold polyaNext
      rw [hl]
      field_simp
      ring)
  rw [eq]
  simp only [pathExpectation_div, pathExpectation_sub, pathExpectation_add,
    pathExpectation_const_mul, pathExpectation_const, expected_heads, expected_heads_sq]
  field_simp
  ring
'''}
addition=aux+'\n'.join(headers[n]+body for n,body in bodies.items())
ending='end BanditRL.OnlineLearning.GuessingLower'
source=PUBLIC.read_text(encoding='utf-8')
write(RUN/'moments-addition-v1.lean.txt',addition)
write(RUN/'leaves/moments-v1.lean',source[:source.rindex(ending)]+addition+'\n'+ending+'\n')
gate('moments-attempt-v1','lake','env','lean',RUN/'leaves/moments-v1.lean')
