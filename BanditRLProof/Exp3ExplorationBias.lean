import BanditRLProof.Exp3PredictableHedge

/-!
# Exploration bias for concrete sampled EXP3

This module compares the pure exponential-weights distribution `q_t` used by
the Hedge potential with the exploration-mixed sampling distribution
`p_t = (1 - gamma) q_t + gamma / |arms|`.

The final finite-horizon theorem gives both inequalities needed before the
almost-sure Hedge bound can be integrated: actual predictable loss is at most
pure-distribution predictable loss plus `gamma` per round, and the pure
estimator square is controlled by the actual probability-mixed estimator
square with factor `1 / (1 - gamma)`.
-/

namespace BanditRLProof
namespace Exp3

universe u v

/-- A pure Hedge coordinate is at most the corresponding explored probability
divided by `1 - gamma`. -/
theorem distribution_le_sampledTrajectoryProbabilityAt_div_one_sub_gamma
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_lt_one : gamma < 1) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) (action : Action) :
    distribution arms eta
        (sampledTrajectoryObservedLoss arms eta gamma sample) t action <=
      sampledTrajectoryProbabilityAt arms eta gamma t sample action /
        (1 - gamma) := by
  have hmix := sampledTrajectoryProbabilityAt_eq_mix_distribution
    arms eta gamma t sample action
  have hfloor_nonneg : 0 <= gamma / (arms.card : Real) :=
    div_nonneg hgamma_nonneg (Nat.cast_nonneg _)
  have hscaled :
      (1 - gamma) *
          distribution arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t action <=
        sampledTrajectoryProbabilityAt arms eta gamma t sample action := by
    rw [hmix]
    exact le_add_of_nonneg_right hfloor_nonneg
  apply (le_div_iff₀ (sub_pos.mpr hgamma_lt_one)).2
  simpa [mul_comm] using hscaled

/-- The pure-Hedge estimator square is bounded by the explored-probability
mixed square with the standard `1 / (1 - gamma)` factor. -/
theorem mixedSquaredLoss_sampledTrajectoryObservedLoss_le_inv_one_sub_gamma
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_lt_one : gamma < 1) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    mixedSquaredLoss arms eta
        (sampledTrajectoryObservedLoss arms eta gamma sample) t <=
      (1 / (1 - gamma)) *
        observedMixedSquaredImportanceWeightedLossAt
          arms eta gamma t sample := by
  unfold mixedSquaredLoss
  calc
    arms.sum (fun action =>
        distribution arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
          (sampledTrajectoryObservedLoss arms eta gamma sample t action) ^ 2) <=
      arms.sum (fun action =>
        (sampledTrajectoryProbabilityAt arms eta gamma t sample action /
            (1 - gamma)) *
          (sampledTrajectoryObservedLoss arms eta gamma sample t action) ^ 2) := by
        apply Finset.sum_le_sum
        intro action _haction
        exact mul_le_mul_of_nonneg_right
          (distribution_le_sampledTrajectoryProbabilityAt_div_one_sub_gamma
            arms eta gamma hgamma_nonneg hgamma_lt_one t sample action)
          (sq_nonneg _)
    _ = (1 / (1 - gamma)) *
        observedMixedSquaredImportanceWeightedLossAt
          arms eta gamma t sample := by
      unfold observedMixedSquaredImportanceWeightedLossAt
        mixedSquaredImportanceWeightedLoss sampledTrajectoryObservedLoss
        observedImportanceWeightedLossAt
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro action _haction
      ring

/-- Exploration changes one predictable `[0,1]` mixed loss by at most
`gamma` relative to the pure Hedge distribution. -/
theorem sampledTrajectoryPredictableMixedLoss_le_pure_add_gamma
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    arms.sum (fun action =>
        sampledTrajectoryProbabilityAt arms eta gamma t sample action *
          predictableLossAt loss t sample action) <=
      arms.sum (fun action =>
        distribution arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
          predictableLossAt loss t sample action) + gamma := by
  have hloss (action : Action) :
      0 <= predictableLossAt loss t sample action ∧
        predictableLossAt loss t sample action <= 1 := by
    cases t with
    | zero =>
        exact loss.initial_mem_unitInterval sample.1 action
    | succ n =>
        exact loss.successor_mem_unitInterval n sample.1
          (Preorder.frestrictLe n sample.2) action
  calc
    arms.sum (fun action =>
        sampledTrajectoryProbabilityAt arms eta gamma t sample action *
          predictableLossAt loss t sample action) =
      arms.sum (fun action =>
        ((1 - gamma) *
            distribution arms eta
              (sampledTrajectoryObservedLoss arms eta gamma sample) t action +
          gamma / (arms.card : Real)) *
            predictableLossAt loss t sample action) := by
        apply Finset.sum_congr rfl
        intro action _haction
        rw [sampledTrajectoryProbabilityAt_eq_mix_distribution]
    _ <= arms.sum (fun action =>
        distribution arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
          predictableLossAt loss t sample action +
        gamma / (arms.card : Real)) := by
      apply Finset.sum_le_sum
      intro action _haction
      have hq_nonneg := distribution_nonneg arms harms eta
        (sampledTrajectoryObservedLoss arms eta gamma sample) t action
      have hq_loss_nonneg := mul_nonneg hq_nonneg (hloss action).1
      have hgamma_q_loss_nonneg := mul_nonneg hgamma_nonneg hq_loss_nonneg
      have hfirst :
          (1 - gamma) *
              (distribution arms eta
                (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
                predictableLossAt loss t sample action) <=
            distribution arms eta
                (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
              predictableLossAt loss t sample action := by
        nlinarith
      have huniform_nonneg : 0 <= gamma / (arms.card : Real) :=
        div_nonneg hgamma_nonneg (Nat.cast_nonneg _)
      have hsecond :
          gamma / (arms.card : Real) * predictableLossAt loss t sample action <=
            gamma / (arms.card : Real) := by
        exact mul_le_of_le_one_right huniform_nonneg (hloss action).2
      calc
        ((1 - gamma) *
              distribution arms eta
                (sampledTrajectoryObservedLoss arms eta gamma sample) t action +
            gamma / (arms.card : Real)) *
            predictableLossAt loss t sample action =
          (1 - gamma) *
              (distribution arms eta
                (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
                predictableLossAt loss t sample action) +
            gamma / (arms.card : Real) *
              predictableLossAt loss t sample action := by ring
        _ <= distribution arms eta
              (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
              predictableLossAt loss t sample action +
            gamma / (arms.card : Real) := add_le_add hfirst hsecond
    _ = arms.sum (fun action =>
          distribution arms eta
              (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
            predictableLossAt loss t sample action) + gamma := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard_pos : 0 < (arms.card : Real) := by
        exact_mod_cast harms.card_pos
      field_simp [ne_of_gt hcard_pos]

/-- Finite-horizon exploration bias and second-moment comparison on one
concrete sampled trajectory. -/
theorem sampledTrajectory_finiteHorizon_explorationBias_secondMoment
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    ((Finset.range horizon).sum (fun t =>
        arms.sum (fun action =>
          sampledTrajectoryProbabilityAt arms eta gamma t sample action *
            predictableLossAt loss t sample action)) <=
      (Finset.range horizon).sum (fun t =>
        arms.sum (fun action =>
          distribution arms eta
              (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
            predictableLossAt loss t sample action)) +
        gamma * (horizon : Real)) ∧
    ((Finset.range horizon).sum (fun t =>
        mixedSquaredLoss arms eta
          (sampledTrajectoryObservedLoss arms eta gamma sample) t) <=
      (1 / (1 - gamma)) * (Finset.range horizon).sum (fun t =>
        observedMixedSquaredImportanceWeightedLossAt
          arms eta gamma t sample)) := by
  constructor
  · calc
      (Finset.range horizon).sum (fun t =>
          arms.sum (fun action =>
            sampledTrajectoryProbabilityAt arms eta gamma t sample action *
              predictableLossAt loss t sample action)) <=
        (Finset.range horizon).sum (fun t =>
          (arms.sum (fun action =>
            distribution arms eta
                (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
              predictableLossAt loss t sample action) + gamma)) := by
          apply Finset.sum_le_sum
          intro t _ht
          exact sampledTrajectoryPredictableMixedLoss_le_pure_add_gamma
            arms harms eta gamma hgamma_nonneg loss t sample
      _ = (Finset.range horizon).sum (fun t =>
            arms.sum (fun action =>
              distribution arms eta
                  (sampledTrajectoryObservedLoss arms eta gamma sample) t action *
                predictableLossAt loss t sample action)) +
          gamma * (horizon : Real) := by
        rw [Finset.sum_add_distrib]
        simp [mul_comm]
  · calc
      (Finset.range horizon).sum (fun t =>
          mixedSquaredLoss arms eta
            (sampledTrajectoryObservedLoss arms eta gamma sample) t) <=
        (Finset.range horizon).sum (fun t =>
          (1 / (1 - gamma)) *
            observedMixedSquaredImportanceWeightedLossAt
              arms eta gamma t sample) := by
          apply Finset.sum_le_sum
          intro t _ht
          exact
            mixedSquaredLoss_sampledTrajectoryObservedLoss_le_inv_one_sub_gamma
              arms eta gamma hgamma_nonneg hgamma_lt_one t sample
      _ = (1 / (1 - gamma)) * (Finset.range horizon).sum (fun t =>
          observedMixedSquaredImportanceWeightedLossAt
            arms eta gamma t sample) := by
        rw [Finset.mul_sum]

end Exp3
end BanditRLProof
