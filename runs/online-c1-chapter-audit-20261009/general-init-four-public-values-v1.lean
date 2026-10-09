import BanditRLProof.OnlineFTLInitializationRegret

open Filter BanditRL.OnlineLearning

#check BanditRL.OnlineLearning.ftlPredict_bestRegret_initial_correction
#print axioms BanditRL.OnlineLearning.ftlPredict_bestRegret_initial_correction
example (initial : ℝ) (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T) :
    squaredBestRegret y (ftlPredict initial y) T =
      squaredBestRegret y (meanPredict y) T +
        ((initial - y 0)^2 - ((1 : ℝ) / 2 - y 0)^2) :=
  BanditRL.OnlineLearning.ftlPredict_bestRegret_initial_correction initial y T hT

#check BanditRL.OnlineLearning.ftlPredict_bestRegret_refined
#print axioms BanditRL.OnlineLearning.ftlPredict_bestRegret_refined
example (initial : ℝ) (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    squaredBestRegret y (ftlPredict initial y) T ≤
      (1 : ℝ) + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2) :=
  BanditRL.OnlineLearning.ftlPredict_bestRegret_refined initial y T hT hi hy

#check BanditRL.OnlineLearning.ftlPredict_upperNoRegret
#print axioms BanditRL.OnlineLearning.ftlPredict_upperNoRegret
example (initial : ℝ) (y : ℕ → ℝ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) :
    NoRegret (Set.Icc (0 : ℝ) 1)
      (fun t x => (x - y t)^2) (ftlPredict initial y) :=
  BanditRL.OnlineLearning.ftlPredict_upperNoRegret initial y hi hy

#check BanditRL.OnlineLearning.ftlPredict_bestRegret_average_tendsto_zero
#print axioms BanditRL.OnlineLearning.ftlPredict_bestRegret_average_tendsto_zero
example (initial : ℝ) (y : ℕ → ℝ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun T : ℕ =>
      squaredBestRegret y (ftlPredict initial y) T / (T : ℝ))
        atTop (nhds (0 : ℝ)) :=
  BanditRL.OnlineLearning.ftlPredict_bestRegret_average_tendsto_zero initial y hi hy
