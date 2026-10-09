import Tests.OnlinePrescientLinearCanary

noncomputable section
open Set Finset
open scoped InnerProductSpace
open BanditRL.OnlinePrescientLinear Tests.OnlinePrescientLinear
namespace Audit.PrescientNondegenerate

-- These are concrete VALUE instantiations of the public production API.
-- They add no source theorem or canonical Book node.
def sharpTwoRound : regret interval (1 / 2) signals 1 0 2 ≤ -(7 / 2) := by
  have h := regret_sharp_bound interval (1 / 2) (by norm_num) signals 1 0 2
    (by norm_num [interval])
  rw [active_projection_values.2.2.2.2.2] at h
  exact h

def sourceTwoRound : regret interval (1 / 2) signals 1 0 2 ≤ -(13 / 4) := by
  have h := regret_source_bound interval (1 / 2) (by norm_num) signals 1 0 2
    (by norm_num [interval])
  rw [active_projection_values.2.2.2.1] at h
  norm_num [Real.norm_eq_abs] at h
  exact h

def proximalSelected :
    advance interval (1 / 2) (signals 0) 1 ∈ interval.carrier ∧
    ∀ u ∈ interval.carrier,
      inner ℝ (signals 0) (advance interval (1 / 2) (signals 0) 1) + 3 +
          ‖advance interval (1 / 2) (signals 0) 1 - 1‖ ^ 2 / (2 * (1 / 2)) ≤
        inner ℝ (signals 0) u + 3 + ‖u - 1‖ ^ 2 / (2 * (1 / 2)) :=
  advance_proximal_minimizer interval (1 / 2) (by norm_num) (signals 0) 1 3

#print axioms sharpTwoRound
#print axioms sourceTwoRound
#print axioms proximalSelected
end Audit.PrescientNondegenerate
