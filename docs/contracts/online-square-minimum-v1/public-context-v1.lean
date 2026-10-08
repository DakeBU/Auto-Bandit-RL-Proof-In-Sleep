import BanditRLProof.OnlineLearningFTL
import BanditRLProof.OnlineLearningRegret
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace BanditRL.OnlineLearning
noncomputable def squaredBestRegret (y prediction : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (prediction t - y t)^2) -
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1)

end BanditRL.OnlineLearning
