import BanditRLProof.DelayedFeedback.Accounting

namespace BanditRLProof

namespace DelayedFeedback

universe uAction uLoss uDecision

/-- The information exposed to an action rule immediately before a delayed
bandit action.  Past actions are visible, while a loss is exposed only when
its source round belongs to the source-faithful strict-availability set.

The view deliberately has no delay field and no total loss trace field.  A
future Delayed SAPO implementation must consume this view (or a proved
equivalent), rather than the environment's hidden delay/loss functions. -/
structure ActionTimeView (Action : Type uAction) (Loss : Type uLoss) where
  pastAction : Nat → Option Action
  observedLoss : Nat → Option Loss

@[ext]
theorem ActionTimeView.ext
    {Action : Type uAction} {Loss : Type uLoss}
    {left right : ActionTimeView Action Loss}
    (hpast : left.pastAction = right.pastAction)
    (hloss : left.observedLoss = right.observedLoss) :
    left = right := by
  cases left
  cases right
  cases hpast
  cases hloss
  rfl

/-- Construct the pre-action view at round `t` from an environment trace.
Actions before `t` are known to the learner.  A source loss is known exactly
when `s + delay s < t`; future and outstanding losses return `none`. -/
def actionTimeViewAt
    {Action : Type uAction} {Loss : Type uLoss}
    (delay : Nat → Nat) (action : Nat → Action) (loss : Nat → Loss)
    (t : Nat) : ActionTimeView Action Loss where
  pastAction := fun s => if s < t then some (action s) else none
  observedLoss := fun s =>
    if s ∈ observedBefore delay t then some (loss s) else none

/-- A causal decision rule receives only the round number and its action-time
view.  `Decision` can later be instantiated by an action distribution, a
kernel, or a deterministic action. -/
abbrev CausalDecisionRule
    (Action : Type uAction) (Loss : Type uLoss) (Decision : Type uDecision) :=
  (t : Nat) → ActionTimeView Action Loss → Decision

@[simp]
theorem actionTimeViewAt_pastAction_of_lt
    {Action : Type uAction} {Loss : Type uLoss}
    (delay : Nat → Nat) (action : Nat → Action) (loss : Nat → Loss)
    {s t : Nat} (hs : s < t) :
    (actionTimeViewAt delay action loss t).pastAction s = some (action s) := by
  simp [actionTimeViewAt, hs]

@[simp]
theorem actionTimeViewAt_pastAction_of_not_lt
    {Action : Type uAction} {Loss : Type uLoss}
    (delay : Nat → Nat) (action : Nat → Action) (loss : Nat → Loss)
    {s t : Nat} (hs : ¬ s < t) :
    (actionTimeViewAt delay action loss t).pastAction s = none := by
  simp [actionTimeViewAt, hs]

@[simp]
theorem actionTimeViewAt_observedLoss_of_mem
    {Action : Type uAction} {Loss : Type uLoss}
    (delay : Nat → Nat) (action : Nat → Action) (loss : Nat → Loss)
    {s t : Nat} (hs : s ∈ observedBefore delay t) :
    (actionTimeViewAt delay action loss t).observedLoss s = some (loss s) := by
  simp [actionTimeViewAt, hs]

@[simp]
theorem actionTimeViewAt_observedLoss_of_not_mem
    {Action : Type uAction} {Loss : Type uLoss}
    (delay : Nat → Nat) (action : Nat → Action) (loss : Nat → Loss)
    {s t : Nat} (hs : s ∉ observedBefore delay t) :
    (actionTimeViewAt delay action loss t).observedLoss s = none := by
  simp [actionTimeViewAt, hs]

/-- Outstanding feedback is absent from the action-time view. -/
theorem actionTimeViewAt_outstanding_loss_hidden
    {Action : Type uAction} {Loss : Type uLoss}
    (delay : Nat → Nat) (action : Nat → Action) (loss : Nat → Loss)
    {s t : Nat} (hs : s ∈ outstandingAt delay t) :
    (actionTimeViewAt delay action loss t).observedLoss s = none := by
  apply actionTimeViewAt_observedLoss_of_not_mem
  intro hobserved
  exact (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp hobserved).2

/-- Two environment traces yield exactly the same pre-action view whenever
their visible source sets, past actions, and revealed losses agree.  Hidden
delays and unobserved losses may differ. -/
theorem actionTimeViewAt_eq_of_observation_equivalent
    {Action : Type uAction} {Loss : Type uLoss}
    (delay₁ delay₂ : Nat → Nat)
    (action₁ action₂ : Nat → Action) (loss₁ loss₂ : Nat → Loss)
    (t : Nat)
    (hvisible : observedBefore delay₁ t = observedBefore delay₂ t)
    (haction : ∀ s, s < t → action₁ s = action₂ s)
    (hloss : ∀ s, s ∈ observedBefore delay₁ t → loss₁ s = loss₂ s) :
    actionTimeViewAt delay₁ action₁ loss₁ t =
      actionTimeViewAt delay₂ action₂ loss₂ t := by
  apply ActionTimeView.ext
  · funext s
    by_cases hs : s < t
    · simp [actionTimeViewAt, hs, haction s hs]
    · simp [actionTimeViewAt, hs]
  · funext s
    by_cases hs : s ∈ observedBefore delay₁ t
    · have hs₂ : s ∈ observedBefore delay₂ t := by
        simpa [← hvisible] using hs
      simp [actionTimeViewAt, hs, hs₂, hloss s hs]
    · have hs₂ : s ∉ observedBefore delay₂ t := by
        simpa [← hvisible] using hs
      simp [actionTimeViewAt, hs, hs₂]

/-- A decision rule consuming only `ActionTimeView` cannot distinguish two
worlds that agree on all information visible before the action. -/
theorem causalDecision_eq_of_observation_equivalent
    {Action : Type uAction} {Loss : Type uLoss}
    {Decision : Type uDecision}
    (rule : CausalDecisionRule Action Loss Decision)
    (delay₁ delay₂ : Nat → Nat)
    (action₁ action₂ : Nat → Action) (loss₁ loss₂ : Nat → Loss)
    (t : Nat)
    (hvisible : observedBefore delay₁ t = observedBefore delay₂ t)
    (haction : ∀ s, s < t → action₁ s = action₂ s)
    (hloss : ∀ s, s ∈ observedBefore delay₁ t → loss₁ s = loss₂ s) :
    rule t (actionTimeViewAt delay₁ action₁ loss₁ t) =
      rule t (actionTimeViewAt delay₂ action₂ loss₂ t) := by
  rw [actionTimeViewAt_eq_of_observation_equivalent
    delay₁ delay₂ action₁ action₂ loss₁ loss₂ t hvisible haction hloss]

end DelayedFeedback

end BanditRLProof
