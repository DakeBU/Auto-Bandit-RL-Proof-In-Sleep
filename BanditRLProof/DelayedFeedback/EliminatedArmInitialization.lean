import BanditRLProof.DelayedFeedback.OrderedProcessingTransition

/-!
# Algorithm 5 line-10 initialization for eliminated Delayed-SAPO arms

This module records the numerical state created for each arm in the line-7
elimination set after line 8 of the frozen Delayed-SAPO algorithm.  It follows
physical PDF page 22, Algorithm 5 lines 9--10: the elimination round and
processed prefix are frozen, the initial inactive-arm probability is formed
from the processed pull count, the surrogate gap is eight empirical widths,
and the first EAP phase is initialized.

The definitions below do not run EAP, prove BSC, construct a generated
trajectory, or establish any stochastic good-event probability.  In
particular, totalized real division makes the displayed source formula a Lean
term even at a zero surrogate gap; positivity of the first phase target is
proved only under the explicit positive-width condition that the mathematical
analysis needs.
-/

namespace BanditRLProof

namespace DelayedFeedback

/-- Algorithm 5 line 10's initial sampling probability
`p_i^1 = 1/(2K) + n_i(S)/(2T)`. -/
noncomputable def delayedSAPOInitialEliminatedProbability
    (armCount horizon pullCount : Nat) : Real :=
  1 / (2 * (armCount : Real)) +
    (pullCount : Real) / (2 * (horizon : Real))

/-- Algorithm 5 line 10's first EAP phase target
`N_i^1 = 1280/(p_i^1 * (Delta-tilde_i)^2)`. -/
noncomputable def delayedSAPOInitialPhaseTarget
    (probability surrogateGap : Real) : Real :=
  1280 / (probability * surrogateGap ^ 2)

/-- A positive source scale makes the capped inverse-square-root width
strictly positive, including the zero-count branch where the width is one. -/
theorem sourceEmpiricalWidthScale_pos (scale count : Real)
    (hscale : 0 < scale) :
    0 < sourceEmpiricalWidthScale scale count := by
  by_cases hcount : count <= 0
  · simp [sourceEmpiricalWidthScale, hcount]
  · rw [sourceEmpiricalWidthScale, if_neg hcount]
    exact lt_min (by norm_num)
      (Real.sqrt_pos.2 (div_pos hscale (lt_of_not_ge hcount)))

/-- Per-arm data created by Algorithm 5 line 10.

`processedAtProbabilityLevel j` represents the source sets
`C_i^(p_i^1 * 2^(-j))`; line 10 initializes every represented level to the
empty set.  Later EAP calls and their phase transitions remain a separate
state-machine leaf. -/
structure DelayedSAPOEliminatedArmInitialization (K : Nat) where
  arm : Fin K
  eliminationRound : Nat
  initialProbability : Real
  eliminationProcessedOrder : List Nat
  eliminationEmpiricalMean : Real
  surrogateGap : Real
  initialPhaseTarget : Real
  errorCount : Nat
  phaseIndex : Nat
  phaseSamples : List Nat
  processedAtProbabilityLevel : Nat -> Finset Nat

/-- Registry of EAP data.  Active arms have not yet entered EAP and are
therefore represented by `none`. -/
abbrev DelayedSAPOEliminatedArmBank (K : Nat) :=
  Fin K -> Option (DelayedSAPOEliminatedArmInitialization K)

/-- Round-start invariant needed to justify that line 10 initializes rather
than resets every arm in the newly eliminated set. -/
def ActiveArmsUninitialized {K : Nat}
    (state : DelayedSAPOStructuralRoundState K)
    (bank : DelayedSAPOEliminatedArmBank K) : Prop :=
  forall i, i ∈ state.currentActive -> bank i = none

namespace DelayedSAPOEliminatedArmInitialization

/-- Construct exactly the line-10 data for one candidate arm from the
post-line-4 numerical snapshot.  Membership in the line-7 elimination set is
enforced by `initializeIfEliminated` below. -/
noncomputable def ofProcessOne {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    DelayedSAPOEliminatedArmInitialization K :=
  let summary := step.toPreEliminationSummary
  let pullCount := summary.toProcessedPrefix.processedPullCount i
  let probability :=
    delayedSAPOInitialEliminatedProbability K horizon pullCount
  let gap := 8 * summary.empiricalWidthAt horizon i
  {
    arm := i
    eliminationRound := state.currentActionRound
    initialProbability := probability
    eliminationProcessedOrder := step.extendedOrder
    eliminationEmpiricalMean := summary.empiricalMean i
    surrogateGap := gap
    initialPhaseTarget := delayedSAPOInitialPhaseTarget probability gap
    errorCount := 0
    phaseIndex := 1
    phaseSamples := []
    processedAtProbabilityLevel := fun _ => {}
  }

/-- Algorithm 5 lines 9--10 initialize precisely the arms selected by the
line-7 elimination set.  Returning `Option` keeps that domain visible instead
of silently producing EAP state for an arm that remains active. -/
noncomputable def initializeIfEliminated {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    Option (DelayedSAPOEliminatedArmInitialization K) :=
  if i ∈ (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated
  then some (ofProcessOne step horizon i)
  else none

/-- Pointwise line-10 update of an existing EAP registry.  Arms in the new
line-7 elimination set receive the literal source initializer; every other
arm keeps its prior state. -/
noncomputable def initializeNewlyEliminated {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat)
    (prior : DelayedSAPOEliminatedArmBank K) :
    DelayedSAPOEliminatedArmBank K :=
  fun i =>
    if i ∈ (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated
    then some (ofProcessOne step horizon i)
    else prior i

@[simp]
theorem initializeIfEliminated_eq_some_iff {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    initializeIfEliminated step horizon i =
        some (ofProcessOne step horizon i) <->
      i ∈ (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated := by
  classical
  by_cases hi :
      i ∈ (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated
  · constructor
    · intro _heq
      exact hi
    · intro _hmem
      rw [initializeIfEliminated, if_pos hi]
  · constructor
    · intro heq
      rw [initializeIfEliminated, if_neg hi] at heq
      cases heq
    · intro hmem
      exact (hi hmem).elim

@[simp]
theorem initializeIfEliminated_eq_none_iff {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    initializeIfEliminated step horizon i = none <->
      i ∉ (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated := by
  classical
  by_cases hi :
      i ∈ (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated
  · constructor
    · intro heq
      rw [initializeIfEliminated, if_pos hi] at heq
      cases heq
    · intro hnot
      exact (hnot hi).elim
  · constructor
    · intro _heq
      exact hi
    · intro _hnot
      rw [initializeIfEliminated, if_neg hi]

@[simp]
theorem initializeNewlyEliminated_of_mem {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat)
    (prior : Fin K -> Option (DelayedSAPOEliminatedArmInitialization K))
    (i : Fin K)
    (hi : i ∈
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated) :
    initializeNewlyEliminated step horizon prior i =
      some (ofProcessOne step horizon i) := by
  simp [initializeNewlyEliminated, hi]

@[simp]
theorem initializeNewlyEliminated_of_not_mem {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat)
    (prior : Fin K -> Option (DelayedSAPOEliminatedArmInitialization K))
    (i : Fin K)
    (hi : i ∉
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated) :
    initializeNewlyEliminated step horizon prior i = prior i := by
  simp [initializeNewlyEliminated, hi]

/-- Line 10 can change an arm's EAP-bank entry only when line 7 selected that
arm for elimination in the same snapshot. -/
theorem mem_eliminated_of_initializeNewlyEliminated_ne_prior {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat)
    (prior : Fin K -> Option (DelayedSAPOEliminatedArmInitialization K))
    (i : Fin K)
    (hchanged : initializeNewlyEliminated step horizon prior i ≠ prior i) :
    i ∈ (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated := by
  by_contra hnot
  exact hchanged
    (initializeNewlyEliminated_of_not_mem step horizon prior i hnot)

/-- An arm that remains active after line 8 is not reset by line 10. -/
theorem initializeNewlyEliminated_eq_prior_of_mem_remainingActive {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat)
    (prior : Fin K -> Option (DelayedSAPOEliminatedArmInitialization K))
    (i : Fin K)
    (hi : i ∈
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).remainingActive) :
    initializeNewlyEliminated step horizon prior i = prior i := by
  have hnot : i ∉
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated :=
    (Finset.mem_sdiff.mp hi).2
  exact initializeNewlyEliminated_of_not_mem step horizon prior i hnot

/-- Every arm selected by line 7 was active immediately before line 8, so a
valid prior bank has no EAP state for it yet. -/
theorem prior_eq_none_of_mem_eliminated {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat)
    (prior : DelayedSAPOEliminatedArmBank K)
    (hprior : ActiveArmsUninitialized state prior)
    (i : Fin K)
    (hi : i ∈
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated) :
    prior i = none := by
  have hactive : i ∈ state.currentActive :=
    (DelayedSAPOEliminationSnapshot.mem_eliminated_iff
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).toDelayedSAPOEliminationSnapshot
      i).mp hi |>.1
  exact hprior i hactive

/-- After line 10, every arm that survives line 8 is still uninitialized in
the EAP bank. -/
theorem remainingActive_uninitialized_after_initialize {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat)
    (prior : DelayedSAPOEliminatedArmBank K)
    (hprior : ActiveArmsUninitialized state prior)
    (i : Fin K)
    (hi : i ∈
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).remainingActive) :
    initializeNewlyEliminated step horizon prior i = none := by
  have hactive : i ∈ state.currentActive :=
    (DelayedSAPOEliminationSnapshot.mem_remainingActive_iff
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).toDelayedSAPOEliminationSnapshot
      i).mp hi |>.1
  rw [initializeNewlyEliminated_eq_prior_of_mem_remainingActive
    step horizon prior i hi]
  exact hprior i hactive

@[simp]
theorem ofProcessOne_arm {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    (ofProcessOne step horizon i).arm = i := rfl

@[simp]
theorem ofProcessOne_eliminationRound {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    (ofProcessOne step horizon i).eliminationRound =
      state.currentActionRound := rfl

@[simp]
theorem ofProcessOne_eliminationProcessedOrder {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    (ofProcessOne step horizon i).eliminationProcessedOrder =
      step.extendedOrder := rfl

@[simp]
theorem ofProcessOne_errorCount {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    (ofProcessOne step horizon i).errorCount = 0 := rfl

@[simp]
theorem ofProcessOne_phaseIndex {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    (ofProcessOne step horizon i).phaseIndex = 1 := rfl

@[simp]
theorem ofProcessOne_phaseSamples {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    (ofProcessOne step horizon i).phaseSamples = [] := rfl

@[simp]
theorem ofProcessOne_processedAtProbabilityLevel {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) (j : Nat) :
    (ofProcessOne step horizon i).processedAtProbabilityLevel j = {} := rfl

/-- The source initial eliminated-arm probability is strictly positive when
there is an arm and the horizon is positive.  No count upper bound is needed
for this lower endpoint. -/
theorem initialProbability_pos {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    0 < (ofProcessOne step horizon i).initialProbability := by
  have hK : 0 < (K : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hfirst :
      0 < (1 : Real) / (2 * (K : Real)) := by positivity
  have hsecond :
      0 <=
        ((step.toPreEliminationSummary.toProcessedPrefix.processedPullCount i : Nat) : Real) /
          (2 * (horizon : Real)) := by positivity
  change 0 < (1 : Real) / (2 * (K : Real)) +
    ((step.toPreEliminationSummary.toProcessedPrefix.processedPullCount i : Nat) : Real) /
      (2 * (horizon : Real))
  linarith

/-- With the source-side count bound `n_i(S) <= T`, the initial probability
is at most one.  The count bound will be generated by the full Algorithm-5
trajectory; it is not manufactured by this numerical initializer. -/
theorem initialProbability_le_one {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) (hhorizon : 0 < horizon)
    (hcount :
      step.toPreEliminationSummary.toProcessedPrefix.processedPullCount i <=
        horizon) :
    (ofProcessOne step horizon i).initialProbability <= 1 := by
  have hK : (1 : Real) <= (K : Real) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i.isLt))
  have hT : 0 < (horizon : Real) := by
    exact_mod_cast hhorizon
  have hfirst :
      (1 : Real) / (2 * (K : Real)) <= 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have hcountReal :
      ((step.toPreEliminationSummary.toProcessedPrefix.processedPullCount i : Nat) : Real) <=
        (horizon : Real) := by exact_mod_cast hcount
  have hsecond :
      ((step.toPreEliminationSummary.toProcessedPrefix.processedPullCount i : Nat) : Real) /
          (2 * (horizon : Real)) <= 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : Real) < 2 * (horizon : Real))).2
    nlinarith
  change (1 : Real) / (2 * (K : Real)) +
      ((step.toPreEliminationSummary.toProcessedPrefix.processedPullCount i : Nat) : Real) /
        (2 * (horizon : Real)) <= 1
  linarith

/-- The line-10 surrogate gap is nonnegative because the exact source width
is capped below by zero. -/
theorem surrogateGap_nonneg {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    0 <= (ofProcessOne step horizon i).surrogateGap := by
  change 0 <= 8 * step.toPreEliminationSummary.empiricalWidthAt horizon i
  exact mul_nonneg (by norm_num)
    (DelayedSAPOProcessedPrefixCountCertificate.sourceEmpiricalWidthScale_nonneg
      _ _)

/-- For the nontrivial source regime `1 < T`, the frozen line-10 surrogate
gap is strictly positive for every processed count. -/
theorem surrogateGap_pos {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) (hhorizon : 1 < horizon) :
    0 < (ofProcessOne step horizon i).surrogateGap := by
  have hhorizonReal : (1 : Real) < (horizon : Real) := by
    exact_mod_cast hhorizon
  have hscale : 0 < 2 * Real.log (horizon : Real) := by
    have hlog := Real.log_pos hhorizonReal
    linarith
  change 0 < 8 * step.toPreEliminationSummary.empiricalWidthAt horizon i
  have hwidth :
      0 < step.toPreEliminationSummary.empiricalWidthAt horizon i := by
    exact sourceEmpiricalWidthScale_pos _ _ hscale
  positivity

/-- The first EAP phase target is nonnegative without hiding Lean's
totalized-division boundary. -/
theorem initialPhaseTarget_nonneg {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) :
    0 <= (ofProcessOne step horizon i).initialPhaseTarget := by
  change 0 <= 1280 /
    ((ofProcessOne step horizon i).initialProbability *
      (ofProcessOne step horizon i).surrogateGap ^ 2)
  apply div_nonneg (by norm_num)
  exact mul_nonneg (initialProbability_pos step horizon i).le (sq_nonneg _)

/-- Under the explicit positive-width condition used by the source analysis,
the first EAP phase target has a genuinely positive denominator and value. -/
theorem initialPhaseTarget_pos {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (i : Fin K) (hhorizon : 1 < horizon) :
    0 < (ofProcessOne step horizon i).initialPhaseTarget := by
  have hp := initialProbability_pos step horizon i
  have hgap := surrogateGap_pos step horizon i hhorizon
  change 0 < 1280 /
    ((ofProcessOne step horizon i).initialProbability *
      (ofProcessOne step horizon i).surrogateGap ^ 2)
  positivity

/-- Bundled deterministic producer for the next EAP leaf: a newly eliminated
arm receives a source-exact state with positive sampling probability,
surrogate gap, and first phase target in the nontrivial horizon regime. -/
theorem initializeNewlyEliminated_spec_of_mem {K : Nat}
    {state : DelayedSAPOStructuralRoundState K}
    (step : DelayedSAPONoSwitchProcessOne state)
    (horizon : Nat) (hhorizon : 1 < horizon)
    (prior : Fin K -> Option (DelayedSAPOEliminatedArmInitialization K))
    (i : Fin K)
    (hi : i ∈
      (step.toPreEliminationSummary.toConfidenceSnapshot horizon).eliminated) :
    initializeNewlyEliminated step horizon prior i =
        some (ofProcessOne step horizon i) ∧
      0 < (ofProcessOne step horizon i).initialProbability ∧
      0 < (ofProcessOne step horizon i).surrogateGap ∧
      0 < (ofProcessOne step horizon i).initialPhaseTarget := by
  exact ⟨initializeNewlyEliminated_of_mem step horizon prior i hi,
    initialProbability_pos step horizon i,
    surrogateGap_pos step horizon i hhorizon,
    initialPhaseTarget_pos step horizon i hhorizon⟩

end DelayedSAPOEliminatedArmInitialization

end DelayedFeedback

end BanditRLProof
