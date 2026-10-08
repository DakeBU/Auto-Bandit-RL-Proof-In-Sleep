import BanditRLProof.OnlineLearningAsymptotic
import Mathlib.Tactic

open Filter
namespace BanditRL.OnlineLearning

/-- Literal ordinary-real-limit reading, kept separate from the shared upper condition. -/
def LimitNoRegret {X : Type*} (V : Set X) (loss : ℕ → X → ℝ)
    (prediction : ℕ → X) : Prop :=
  ∀ u ∈ V, ∃ a : ℝ, a ≤ 0 ∧
    Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)

namespace NoRegretCounterexample

/-- A nonnegative horizon potential with alternating normalized values. -/
noncomputable def potential (T : ℕ) : ℝ :=
  if T % 2 = 0 then (T : ℝ) else 0

/-- Actual exogenous real affine losses; no horizon-dependent learner. -/
noncomputable def loss (t : ℕ) (x : ℝ) : ℝ :=
  (potential (t + 1) - potential t) * x

end NoRegretCounterexample
end BanditRL.OnlineLearning
