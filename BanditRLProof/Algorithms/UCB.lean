import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import BanditRLProof.Regret

/-!
# UCB surfaces
-/

namespace BanditRLProof
namespace UCB

/-- Parameters for a finite-arm UCB run. -/
structure Spec (K : Nat) where
  hK : 0 < K
  explorationScale : Rat

/-- State visible to an index policy at one time step. -/
structure IndexState (K : Nat) where
  empiricalMean : Fin K → Rat
  pulls : Fin K → Nat

/--
Placeholder score surface for the first dependency-light layer.

The Mathlib/LML migration will refine this to
`mean + sqrt (2 * c * log n / pulls)`.
-/
def score (_spec : Spec K) (state : IndexState K) (arm : Fin K) : Rat :=
  state.empiricalMean arm

@[simp] theorem score_eq_empiricalMean (spec : Spec K) (state : IndexState K)
    (arm : Fin K) :
    score spec state arm = state.empiricalMean arm := rfl

/-- Real-valued UCB confidence score `empirical mean + radius`. -/
def confidenceScore {Arm : Type} (empiricalMean radius : Arm -> Real)
    (arm : Arm) : Real :=
  empiricalMean arm + radius arm

@[simp] theorem confidenceScore_apply
    {Arm : Type} (empiricalMean radius : Arm -> Real) (arm : Arm) :
    confidenceScore empiricalMean radius arm =
      empiricalMean arm + radius arm := rfl

/-- Mean gap against a designated best arm for Real-valued UCB algebra. -/
def meanGap {Arm : Type} (trueMean : Arm -> Real) (best arm : Arm) : Real :=
  trueMean best - trueMean arm

@[simp] theorem meanGap_apply
    {Arm : Type} (trueMean : Arm -> Real) (best arm : Arm) :
    meanGap trueMean best arm = trueMean best - trueMean arm := rfl

/--
UCB good-event algebra: if the best arm's true mean is below its upper
confidence score, the chosen arm's true mean is above its lower confidence
score, and the chosen arm maximizes the confidence score against the best arm,
then the chosen arm's mean gap is at most twice its radius.
-/
theorem meanGap_le_two_radius_of_confidenceScore_max
    {Arm : Type} (trueMean empiricalMean radius : Arm -> Real)
    (best chosen : Arm)
    (hbest_upper :
      trueMean best <= confidenceScore empiricalMean radius best)
    (hchosen_lower :
      empiricalMean chosen - radius chosen <= trueMean chosen)
    (hscore :
      confidenceScore empiricalMean radius best <=
        confidenceScore empiricalMean radius chosen) :
    meanGap trueMean best chosen <= 2 * radius chosen := by
  unfold meanGap confidenceScore at *
  linarith

/--
Contrapositive consumer for the UCB good-event algebra: under the same good
event and score-maximality hypotheses, a strict `2 * radius < gap` certificate
rules out choosing that arm.
-/
theorem not_two_radius_lt_meanGap_of_confidenceScore_max
    {Arm : Type} (trueMean empiricalMean radius : Arm -> Real)
    (best chosen : Arm)
    (hbest_upper :
      trueMean best <= confidenceScore empiricalMean radius best)
    (hchosen_lower :
      empiricalMean chosen - radius chosen <= trueMean chosen)
    (hscore :
      confidenceScore empiricalMean radius best <=
        confidenceScore empiricalMean radius chosen)
    (hgap_large : 2 * radius chosen < meanGap trueMean best chosen) :
    False := by
  have hgap_le := meanGap_le_two_radius_of_confidenceScore_max
    trueMean empiricalMean radius best chosen hbest_upper hchosen_lower hscore
  linarith

/-- The proof-DAG leaves usually needed for UCB regret formalization. -/
def obligationNames : List String :=
  [ "initial_round_robin_count_positive"
  , "ucb_index_maximality"
  , "good_event_gap_implies_count_bound"
  , "subgaussian_upper_tail"
  , "subgaussian_lower_tail"
  , "expected_pull_count_bound"
  , "regret_from_pull_count_bounds"
  ]

end UCB
end BanditRLProof
