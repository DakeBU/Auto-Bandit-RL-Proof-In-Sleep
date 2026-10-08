import BanditRLProof.OnlineFTLOscillation

open Filter BanditRL.OnlineLearning
namespace Tests.OnlineFTLOscillation


#check (    (∀ t, dyadicObservation t ∈ Set.Icc (0 : ℝ) 1) ∧
    dyadicObservation 0 = 0 ∧ dyadicObservation 1 = 1 ∧
    dyadicObservation 2 = 1 ∧ dyadicObservation 3 = 0)

#check (    meanPredict dyadicObservation 0 = (1 : ℝ)/2 ∧
    meanPredict dyadicObservation 1 = 0 ∧
    meanPredict dyadicObservation 2 = (1 : ℝ)/2 ∧
    meanPredict dyadicObservation 3 = (2 : ℝ)/3)

#check (    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 0 = 0 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 1 = (1 : ℝ)/4 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 2 = (3 : ℝ)/4 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 3 = (5 : ℝ)/6 ∧
    comparatorRegret (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) 0 3 / (3 : ℝ) = -(1 : ℝ)/6)

#check (    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ↔
    ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean dyadicObservation) atTop (nhds m))

#check (    ¬ ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean dyadicObservation) atTop (nhds m))

#check (    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (4^(n + 1) - 1))
      atTop (nhds ((2 : ℝ)/3)) ∧
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (2 * 4^n - 1))
      atTop (nhds ((1 : ℝ)/3)))

#check (    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ∧
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
    (¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation))

#check (    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation))

#check (    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)))

#check (    ¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a))

#check (    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation))

end Tests.OnlineFTLOscillation
