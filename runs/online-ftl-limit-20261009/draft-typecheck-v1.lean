import BanditRLProof.OnlineSquareMinimum
import BanditRLProof.OnlineNoRegretSemantics

open Filter

namespace BanditRL.OnlineLearning

#check (∀ (y : ℕ → ℝ) (T : ℕ),
    0 ≤ comparatorRegret (fun t x => (x - y t)^2)
      (meanPredict y) (empiricalMean y T) T)

#check (∀ (y : ℕ → ℝ) (u : ℝ) (T : ℕ),
    comparatorRegret (fun t x => (x - y t)^2) (meanPredict y) u T =
      comparatorRegret (fun t x => (x - y t)^2)
        (meanPredict y) (empiricalMean y T) T -
      (T : ℝ) * (u - empiricalMean y T)^2)

#check (∀ (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1),
    Tendsto (fun T : ℕ => squaredBestRegret y (meanPredict y) T / (T : ℝ))
      atTop (nhds (0 : ℝ)))

#check (∀ (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) (u a : ℝ),
    Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - y t)^2) (meanPredict y) u T / (T : ℝ))
      atTop (nhds a) ↔
    Tendsto (fun T : ℕ => (u - empiricalMean y T)^2) atTop (nhds (-a)))

#check (∀ (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) (m : ℝ)
    (hm : Tendsto (empiricalMean y) atTop (nhds m)),
    (∀ u : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - y t)^2) (meanPredict y) u T / (T : ℝ))
      atTop (nhds (-(u - m)^2))) ∧
    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - y t)^2) (meanPredict y))

end BanditRL.OnlineLearning
