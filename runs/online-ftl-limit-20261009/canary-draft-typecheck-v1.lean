import BanditRLProof.OnlineSquareMinimum
import BanditRLProof.OnlineNoRegretSemantics

open Filter
open BanditRL.OnlineLearning

namespace Tests.OnlineFTLLimitSemantics

def alternatingObservation (t : ℕ) : ℝ := if t % 2 = 0 then 0 else 1


#check (    (∀ t, alternatingObservation t ∈ Set.Icc (0 : ℝ) 1) ∧
    alternatingObservation 0 = 0 ∧ alternatingObservation 1 = 1)

#check (∀ (T : ℕ),
    (∑ t ∈ Finset.range T, alternatingObservation t) = ((T / 2 : ℕ) : ℝ))

#check (    Tendsto (empiricalMean alternatingObservation) atTop (nhds ((1 : ℝ) / 2)))

#check (    meanPredict alternatingObservation 0 = (1 : ℝ) / 2 ∧
    meanPredict alternatingObservation 1 = 0 ∧
    meanPredict alternatingObservation 2 = (1 : ℝ) / 2 ∧
    meanPredict alternatingObservation 3 = (1 : ℝ) / 3)

#check (    squaredBestRegret alternatingObservation (meanPredict alternatingObservation) 0 = 0 ∧
    squaredBestRegret alternatingObservation (meanPredict alternatingObservation) 1 = (1 : ℝ) / 4 ∧
    squaredBestRegret alternatingObservation (meanPredict alternatingObservation) 2 = (3 : ℝ) / 4)

#check (∀ (T : ℕ),
    0 ≤ comparatorRegret (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) (empiricalMean alternatingObservation T) T)

#check (∀ (u : ℝ) (T : ℕ),
    comparatorRegret (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) u T =
    comparatorRegret (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) (empiricalMean alternatingObservation T) T -
      (T : ℝ) * (u - empiricalMean alternatingObservation T)^2)

#check (    Tendsto (fun T : ℕ =>
      squaredBestRegret alternatingObservation (meanPredict alternatingObservation) T / (T : ℝ))
      atTop (nhds (0 : ℝ)))

#check (∀ (u a : ℝ),
    Tendsto (fun T : ℕ => comparatorRegret
      (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) u T / (T : ℝ)) atTop (nhds a) ↔
    Tendsto (fun T : ℕ => (u - empiricalMean alternatingObservation T)^2)
      atTop (nhds (-a)))

#check (    Tendsto (fun T : ℕ => comparatorRegret
      (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) 0 T / (T : ℝ))
      atTop (nhds (-(1 : ℝ) / 4)))

#check (    Tendsto (fun T : ℕ => comparatorRegret
      (fun t x => (x - alternatingObservation t)^2)
      (meanPredict alternatingObservation) ((1 : ℝ) / 2) T / (T : ℝ))
      atTop (nhds (0 : ℝ)))

#check (    LimitNoRegret (Set.Icc (0 : ℝ) 1)
      (fun t x => (x - alternatingObservation t)^2) (meanPredict alternatingObservation))

end Tests.OnlineFTLLimitSemantics
