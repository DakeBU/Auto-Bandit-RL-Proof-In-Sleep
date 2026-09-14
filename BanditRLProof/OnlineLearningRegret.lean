import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Filter

namespace BanditRL.OnlineLearning

/-- Comparator is an evaluation parameter, separate from the prediction sequence. -/
noncomputable def comparatorRegret {X : Type*} (loss : ℕ → X → ℝ)
    (prediction : ℕ → X) (u : X) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, loss t (prediction t)) - ∑ t ∈ Finset.range T, loss t u

/-- Upper sublinear regret. This does not require nonnegative regret or existence of its limit. -/
def NoRegret {X : Type*} (V : Set X) (loss : ℕ → X → ℝ) (prediction : ℕ → X) : Prop :=
  ∀ u ∈ V, ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop,
    comparatorRegret loss prediction u T / T ≤ ε

/-- The sum-of-differences form agrees exactly with the source's difference of sums. -/
theorem comparatorRegret_eq_sum {X : Type*} (loss : ℕ → X → ℝ)
    (prediction : ℕ → X) (u : X) (T : ℕ) :
    comparatorRegret loss prediction u T =
      ∑ t ∈ Finset.range T, (loss t (prediction t) - loss t u) := by
  exact (Finset.sum_sub_distrib _ _).symm

/-- Any comparator-wise vanishing upper bound certifies no-regret. -/
theorem noRegret_of_vanishing_bound {X : Type*} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (bound : X → ℕ → ℝ)
    (hb : ∀ u ∈ V, ∀ᶠ T in atTop, comparatorRegret loss prediction u T / T ≤ bound u T)
    (hl : ∀ u ∈ V, Tendsto (bound u) atTop (nhds 0)) :
    NoRegret V loss prediction := by
  intro u hu ε hε
  have he : ∀ᶠ T in atTop, bound u T < ε := (tendsto_order.mp (hl u hu)).2 ε hε
  exact (hb u hu).and he |>.mono (fun T h => h.1.trans h.2.le)

end BanditRL.OnlineLearning
