import BanditRLProof.TsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLaw

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-!
# Horizon-local history-adaptive expected corruption

This module packages only the predictable reward-shift data used through a
fixed finite horizon.  The source is extended by zero after that horizon and
then consumed by the existing all-time expected-corruption theorem route.
-/

/-- Predictable reward shifts and deterministic envelope witnesses needed only
for rounds `0, ..., horizon`.  Successor data are indexed by `Fin horizon`, so
no measurability or boundedness contract is requested after the final round. -/
structure FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource
    (K horizon : Nat) where
  initial : Fin K -> Real
  successor : forall n : Fin horizon,
    History.FinitePairHistory (Fin K) Real n.1 -> Fin K -> Real
  measurable_successor : forall n, Measurable
    (fun input : History.FinitePairHistory (Fin K) Real n.1 × Fin K =>
      successor n input.1 input.2)
  initialEnvelope : Fin K -> Real
  successorEnvelope : Fin horizon -> Fin K -> Real
  initialEnvelope_nonneg : forall arm, 0 <= initialEnvelope arm
  successorEnvelope_nonneg : forall n arm, 0 <= successorEnvelope n arm
  initial_abs_le : forall arm, |initial arm| <= initialEnvelope arm
  successor_abs_le : forall n history arm,
    |successor n history arm| <= successorEnvelope n arm

/-- Successor shift obtained by extending a horizon-local source by zero. -/
noncomputable def finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (arm : Fin K) : Real := by
  classical
  exact if h : n < horizon then source.successor ⟨n, h⟩ history arm else 0

/-- Deterministic envelope obtained by extending a horizon-local envelope by
zero after its final successor round. -/
noncomputable def finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (t : Nat) (arm : Fin K) : Real := by
  classical
  cases t with
  | zero => exact source.initialEnvelope arm
  | succ n =>
      exact if h : n < horizon then source.successorEnvelope ⟨n, h⟩ arm else 0

@[simp]
theorem finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor_of_lt
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (hn : n < horizon)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor
        source n history arm =
      source.successor ⟨n, hn⟩ history arm := by
  simp [finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor, hn]

@[simp]
theorem finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor_of_le
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (hn : horizon <= n)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor
        source n history arm = 0 := by
  simp [finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor,
    Nat.not_lt_of_ge hn]

@[simp]
theorem finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_zero
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (arm : Fin K) :
    finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope source 0 arm =
      source.initialEnvelope arm := by
  simp [finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope]

@[simp]
theorem finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_succ_of_lt
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (hn : n < horizon) (arm : Fin K) :
    finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope
        source (Nat.succ n) arm =
      source.successorEnvelope ⟨n, hn⟩ arm := by
  change (if h : n < horizon then
      source.successorEnvelope ⟨n, h⟩ arm else 0) = _
  simp [hn]

@[simp]
theorem finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_succ_of_le
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (hn : horizon <= n) (arm : Fin K) :
    finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope
        source (Nat.succ n) arm = 0 := by
  change (if h : n < horizon then
      source.successorEnvelope ⟨n, h⟩ arm else 0) = 0
  simp [Nat.not_lt_of_ge hn]

/-- Zero extension of a horizon-local source to the all-time source interface.
The supplied simp lemmas show that the extension is unchanged on every round
used by the target horizon; it introduces no post-horizon regularity
obligation. -/
noncomputable def FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource.toAllTime
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon) :
    FiniteArmIIDHistoryAdaptiveRewardShiftSource K where
  initial := source.initial
  successor := finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor source
  measurable_successor n := by
    classical
    by_cases hn : n < horizon
    · simpa [finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor, hn] using
        source.measurable_successor ⟨n, hn⟩
    · simp [finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor, hn]
  envelope := finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope source
  envelope_nonneg t arm := by
    cases t with
    | zero => exact source.initialEnvelope_nonneg arm
    | succ n =>
        by_cases hn : n < horizon
        · rw [finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_succ_of_lt
            source n hn arm]
          exact source.successorEnvelope_nonneg ⟨n, hn⟩ arm
        · rw [finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_succ_of_le
            source n (Nat.le_of_not_gt hn) arm]
  initial_abs_le arm := by
    simpa [finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope] using
      source.initial_abs_le arm
  successor_abs_le n history arm := by
    by_cases hn : n < horizon
    · calc
        |finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor
            source n history arm| =
            |source.successor ⟨n, hn⟩ history arm| := by
          rw [finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor_of_lt
            source n hn history arm]
        _ <= source.successorEnvelope ⟨n, hn⟩ arm :=
          source.successor_abs_le ⟨n, hn⟩ history arm
        _ = finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope
            source (n + 1) arm := by
          simpa only [Nat.succ_eq_add_one] using
            (finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_succ_of_lt
              source n hn arm).symm
    · rw [finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor_of_le
          source n (Nat.le_of_not_gt hn) history arm]
      rw [finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_succ_of_le
          source n (Nat.le_of_not_gt hn) arm]
      simpa only [abs_zero] using le_refl (0 : Real)

@[simp]
theorem FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource.toAllTime_initial
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (arm : Fin K) : source.toAllTime.initial arm = source.initial arm := by
  rfl

@[simp]
theorem FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource.toAllTime_successor_of_lt
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (hn : n < horizon)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    source.toAllTime.successor n history arm =
      source.successor ⟨n, hn⟩ history arm := by
  exact finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor_of_lt
    source n hn history arm

@[simp]
theorem FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource.toAllTime_successor_of_le
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (hn : horizon <= n)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    source.toAllTime.successor n history arm = 0 := by
  exact finiteArmIIDHorizonHistoryAdaptiveRewardShiftSuccessor_of_le
    source n hn history arm

@[simp]
theorem FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource.toAllTime_envelope_zero
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (arm : Fin K) :
    source.toAllTime.envelope 0 arm = source.initialEnvelope arm := by
  exact finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_zero source arm

@[simp]
theorem FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource.toAllTime_envelope_succ_of_lt
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (hn : n < horizon) (arm : Fin K) :
    source.toAllTime.envelope (Nat.succ n) arm =
      source.successorEnvelope ⟨n, hn⟩ arm := by
  exact finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_succ_of_lt
    source n hn arm

@[simp]
theorem FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource.toAllTime_envelope_succ_of_le
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (n : Nat) (hn : horizon <= n) (arm : Fin K) :
    source.toAllTime.envelope (Nat.succ n) arm = 0 := by
  exact finiteArmIIDHorizonHistoryAdaptiveRewardShiftEnvelope_succ_of_le
    source n hn arm

/-- Predictable clipped loss attached to the zero extension of a horizon-local
reward-shift source. -/
noncomputable def finiteArmIIDHorizonHistoryAdaptiveCorruptedRewardLoss
    {K horizon : Nat}
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon) :=
  finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source.toAllTime

/-- Exact generated-policy expected-corruption budget of a horizon-local
source.  Only rounds through `horizon` occur in the finite sum. -/
noncomputable def finiteArmIIDHorizonHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw
    {K horizon : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon) :
    Real :=
  finiteArmIIDHistoryAdaptiveExpectedRewardCorruptionBudgetForLaw
    model armLaw source.toAllTime horizon

/-- All-regimes expected-corruption envelope for a horizon-local source. -/
noncomputable def finiteArmIIDHorizonHistoryAdaptiveExpectedCorruptionAllRegimeBound
    {K horizon : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon) :
    Real :=
  finiteArmIIDHistoryAdaptiveExpectedCorruptionAllRegimeBound
    model armLaw source.toAllTime horizon

/-- Scheduled half-Tsallis regret under a finite-arm IID reward law and a
history-adaptive reward-shift source whose regularity contract stops at the
target horizon.  The conclusion uses the exact generated-policy expected
corruption and internally selects the refined or logarithmic branch. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDHorizonHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_allRegimes
    {K horizon : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (source : FiniteArmIIDHorizonHistoryAdaptiveRewardShiftSource K horizon)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIIDRewardVectorLaw armLaw
    let loss := finiteArmIIDHorizonHistoryAdaptiveCorruptedRewardLoss source
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      finiteArmIIDHorizonHistoryAdaptiveExpectedCorruptionAllRegimeBound
        model armLaw source := by
  simpa only [finiteArmIIDHorizonHistoryAdaptiveCorruptedRewardLoss,
    finiteArmIIDHorizonHistoryAdaptiveExpectedCorruptionAllRegimeBound] using
    integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLawRegret_le_allRegimes
      model armLaw hprob hbound hmean source.toAllTime hgapPos hgapLeOne horizon

end Tsallis
end BanditRLProof
