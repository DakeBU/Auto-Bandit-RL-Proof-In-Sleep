import BanditRLProof.Exp3RealizedRegret

/-!
# Shared finite best-arm transport for EXP3

This module packages the comparator-independent order step used by finite-arm
best-in-hindsight regret wrappers. It contains no probability bound: downstream
routes identify the best-arm event with a finite union of fixed-comparator
events and supply their own confidence schedules.
-/

namespace BanditRLProof.Exp3

universe u v

/-- Cumulative predictable loss of the best supported arm in hindsight. -/
noncomputable def sampledPredictableBestArmCumulativeLoss
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) : Real :=
  arms.inf' harms fun comparator =>
    (Finset.range horizon).sum fun t =>
      predictableLossAt loss t sample comparator

/-- The best-arm regret event is exactly the finite existential union of the
fixed-comparator regret events. -/
theorem threshold_le_sampledPredictableRealizedLoss_sub_bestArmCumulativeLoss_iff
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) (threshold : Real) :
    threshold <=
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          sampledPredictableBestArmCumulativeLoss
            arms harms loss horizon sample ↔
      ∃ comparator ∈ arms,
        threshold <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) := by
  let realizedLoss :=
    (Finset.range horizon).sum fun t =>
      sampledTrajectoryRealizedLossAt t sample
  let comparatorLoss := fun comparator =>
    (Finset.range horizon).sum fun t =>
      predictableLossAt loss t sample comparator
  change threshold <= realizedLoss - arms.inf' harms comparatorLoss ↔
    ∃ comparator ∈ arms, threshold <= realizedLoss - comparatorLoss comparator
  constructor
  · intro hbest
    have hinf :
        arms.inf' harms comparatorLoss <= realizedLoss - threshold := by
      linarith
    rcases (Finset.inf'_le_iff harms).1 hinf with
      ⟨comparator, hcomparator, hcomparatorLoss⟩
    exact ⟨comparator, hcomparator, by linarith⟩
  · rintro ⟨comparator, hcomparator, hregret⟩
    have hinf :
        arms.inf' harms comparatorLoss <= comparatorLoss comparator :=
      Finset.inf'_le _ hcomparator
    linarith

end BanditRLProof.Exp3
