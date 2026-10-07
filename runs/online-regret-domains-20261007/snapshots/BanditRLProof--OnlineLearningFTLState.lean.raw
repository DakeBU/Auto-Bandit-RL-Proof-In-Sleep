import BanditRLProof.OnlineLearningFTL

namespace BanditRL.OnlineLearning

noncomputable def ftlPredict (initial : ℝ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then initial else empiricalMean y t

noncomputable def ftlMeanStep (state : ℕ × ℝ) (target : ℝ) : ℕ × ℝ :=
  (state.1 + 1, state.2 + (target - state.2) / ((state.1 : ℝ) + 1))

noncomputable def ftlState (initial : ℝ) (y : ℕ → ℝ) : ℕ → ℕ × ℝ
  | 0 => (0, initial)
  | t + 1 => ftlMeanStep (ftlState initial y t) (y t)

theorem ftlPredict_prefix (initial : ℝ) (y z : ℕ → ℝ) (t : ℕ)
    (h : ∀ i < t, y i = z i) :
    ftlPredict initial y t = ftlPredict initial z t := by
  unfold ftlPredict empiricalMean
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact h i (Finset.mem_range.mp hi)

theorem ftlPredict_mem (initial : ℝ) (y : ℕ → ℝ) (t : ℕ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ i < t, y i ∈ Set.Icc (0 : ℝ) 1) :
    ftlPredict initial y t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold ftlPredict
  split_ifs with h
  · exact hi
  · exact empiricalMean_mem y t (Nat.pos_of_ne_zero h) hy

theorem ftlPredict_half (y : ℕ → ℝ) (t : ℕ) :
    ftlPredict ((1 : ℝ) / 2) y t = meanPredict y t := by
  rfl

theorem ftlState_first (initial : ℝ) (y : ℕ → ℝ) :
    ftlState initial y 1 = (1, y 0) := by
  simp [ftlState, ftlMeanStep]

theorem ftlState_eq_predict (initial : ℝ) (y : ℕ → ℝ) (t : ℕ) :
    ftlState initial y t = (t, ftlPredict initial y t) := by
  induction t with
  | zero => simp [ftlState, ftlPredict]
  | succ t ih =>
    by_cases ht : t = 0
    · subst t
      simpa [ftlPredict, empiricalMean] using ftlState_first initial y
    · rw [ftlState, ih]
      apply Prod.ext
      · rfl
      · simpa [ftlMeanStep, ftlPredict, ht] using (empiricalMean_succ y t).symm

theorem ftlState_prefix (initial : ℝ) (y z : ℕ → ℝ) (t : ℕ)
    (h : ∀ i < t, y i = z i) :
    ftlState initial y t = ftlState initial z t := by
  rw [ftlState_eq_predict initial y t, ftlState_eq_predict initial z t,
    ftlPredict_prefix initial y z t h]

theorem ftlState_mem (initial : ℝ) (y : ℕ → ℝ) (t : ℕ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ i < t, y i ∈ Set.Icc (0 : ℝ) 1) :
    (ftlState initial y t).2 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ftlState_eq_predict]
  exact ftlPredict_mem initial y t hi hy

theorem ftlState_half (y : ℕ → ℝ) (t : ℕ) :
    ftlState ((1 : ℝ) / 2) y t = (t, meanPredict y t) := by
  rw [ftlState_eq_predict, ftlPredict_half]

end BanditRL.OnlineLearning
