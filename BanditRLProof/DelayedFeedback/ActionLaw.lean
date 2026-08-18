import BanditRLProof.DelayedFeedback.Elimination
import BanditRLProof.Exp3ConditionalMoments

namespace BanditRLProof

namespace DelayedFeedback

open MeasureTheory

/-- A line-15 allocation together with the exact hypotheses needed to make
its coordinates a probability distribution.  EAP must eventually construct
these fields; this structure does not assume that obligation away. -/
structure DelayedSAPOAllocation (K : Nat) where
  active : Finset (Fin K)
  inactiveProbability : Fin K → ℝ
  active_nonempty : active.Nonempty
  inactive_nonnegative :
    ∀ i ∈ inactiveArms active, 0 ≤ inactiveProbability i
  inactive_mass_le_one :
    (∑ i ∈ inactiveArms active, inactiveProbability i) ≤ 1

namespace DelayedSAPOAllocation

/-- The Algorithm 5 line-15 probability coordinate associated with a
certified allocation. -/
noncomputable def probability {K : Nat}
    (allocation : DelayedSAPOAllocation K) (i : Fin K) : ℝ :=
  delayedSAPOProbability allocation.active allocation.inactiveProbability i

theorem probability_nonnegative {K : Nat}
    (allocation : DelayedSAPOAllocation K) (i : Fin K) :
    0 ≤ allocation.probability i := by
  exact delayedSAPOProbability_nonneg allocation.active
    allocation.inactiveProbability allocation.inactive_nonnegative
    allocation.inactive_mass_le_one i

theorem sum_probability_eq_one {K : Nat}
    (allocation : DelayedSAPOAllocation K) :
    ∑ i, allocation.probability i = 1 := by
  exact sum_delayedSAPOProbability_eq_one allocation.active
    allocation.inactiveProbability allocation.active_nonempty

/-- Reuse the library's finite-action probability-vector interface instead
of introducing a second ad hoc sampling semantics for Delayed SAPO. -/
theorem finiteActionDistribution {K : Nat}
    (allocation : DelayedSAPOAllocation K) :
    Exp3.FiniteActionDistribution (Finset.univ : Finset (Fin K))
      allocation.probability where
  nonneg := by
    intro i _hi
    exact allocation.probability_nonnegative i
  sum_eq_one := allocation.sum_probability_eq_one

/-- One-round randomized action law induced by the certified line-15
allocation.  A measurable history kernel and recursive generated trajectory
remain separate obligations. -/
noncomputable def actionMeasure {K : Nat}
    (allocation : DelayedSAPOAllocation K) : Measure (Fin K) :=
  Exp3.finiteActionMeasure Finset.univ allocation.probability

theorem actionMeasure_isProbabilityMeasure {K : Nat}
    (allocation : DelayedSAPOAllocation K) :
    IsProbabilityMeasure allocation.actionMeasure := by
  exact Exp3.finiteActionMeasure_isProbabilityMeasure Finset.univ
    allocation.probability allocation.finiteActionDistribution

end DelayedSAPOAllocation

/-- Convert a causal allocation rule into a causal, measure-valued action
rule.  The only input remains `ActionTimeView`; hidden delays and unobserved
losses are not added to the algorithm interface. -/
noncomputable def causalDelayedSAPOActionMeasureRule
    {K : Nat} {Loss : Type*}
    (rule : CausalDecisionRule (Fin K) Loss (DelayedSAPOAllocation K)) :
    CausalDecisionRule (Fin K) Loss (Measure (Fin K)) :=
  fun t view => (rule t view).actionMeasure

/-- Every output of the causal measure-valued rule is a probability measure. -/
theorem causalDelayedSAPOActionMeasureRule_isProbabilityMeasure
    {K : Nat} {Loss : Type*}
    (rule : CausalDecisionRule (Fin K) Loss (DelayedSAPOAllocation K))
    (t : Nat) (view : ActionTimeView (Fin K) Loss) :
    IsProbabilityMeasure (causalDelayedSAPOActionMeasureRule rule t view) := by
  exact DelayedSAPOAllocation.actionMeasure_isProbabilityMeasure
    (rule t view)

/-- Observation-equivalent hidden worlds induce exactly the same one-round
Delayed SAPO action law for every allocation rule typed on the causal view. -/
theorem causalDelayedSAPOActionMeasureRule_eq_of_observation_equivalent
    {K : Nat} {Loss : Type*}
    (rule : CausalDecisionRule (Fin K) Loss (DelayedSAPOAllocation K))
    (delay₁ delay₂ : Nat → Nat)
    (action₁ action₂ : Nat → Fin K) (loss₁ loss₂ : Nat → Loss)
    (t : Nat)
    (hvisible : observedBefore delay₁ t = observedBefore delay₂ t)
    (haction : ∀ s, s < t → action₁ s = action₂ s)
    (hloss : ∀ s, s ∈ observedBefore delay₁ t → loss₁ s = loss₂ s) :
    causalDelayedSAPOActionMeasureRule rule t
        (actionTimeViewAt delay₁ action₁ loss₁ t) =
      causalDelayedSAPOActionMeasureRule rule t
        (actionTimeViewAt delay₂ action₂ loss₂ t) := by
  rw [actionTimeViewAt_eq_of_observation_equivalent
    delay₁ delay₂ action₁ action₂ loss₁ loss₂ t hvisible haction hloss]

end DelayedFeedback

end BanditRLProof
