import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section
open Set Finset MeasureTheory

namespace NeutralIntegralBoundPacketV2

#check (∀ (b : ℝ) (d : ℕ → ℝ) (q : ℝ → ℝ) (N : ℕ),
    0 ≤ b → (∀ t < N, 0 ≤ d t) →
    ContinuousOn q (Set.Ici 0) → AntitoneOn q (Set.Ici 0) →
    (∀ x ∈ Set.Ici 0, 0 ≤ q x) →
    (∑ t ∈ range N, d t * q (b + ∑ i ∈ range (t + 1), d i)) ≤
      ∫ x in b..(b + ∑ i ∈ range N, d i), q x)
end NeutralIntegralBoundPacketV2
