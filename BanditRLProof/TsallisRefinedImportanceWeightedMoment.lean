import BanditRLProof.TsallisFTRLGeneratedRegularity
import BanditRLProof.TsallisImportanceWeightedMoment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Refined half-Tsallis importance-weighted moments

This module isolates the finite-sum calculation behind the ordinary
importance-weighted part of the refined half-Tsallis stability route.  The
baseline is the sampled raw loss.  The quadratic moment contracts to
`sum_a sqrt (p a) * (1 - p a)`, while the positive cubic remainder is at
most one.

No potential, Hessian-comparison, conditional-expectation, or trajectory-law
statement is proved here.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- Inverse-half-Tsallis-Hessian quadratic moment after subtracting a baseline. -/
noncomputable def shiftedHalfPowerImportanceWeightedMoment
    {Action : Type u}
    (arms : Finset Action) (prob loss : Action -> Real)
    (chosen : Action) : Real :=
  arms.sum (fun action =>
    Real.sqrt (prob action) * prob action *
      (Exp3.importanceWeightedLoss prob loss chosen action - loss chosen) ^ 2)

/-- Positive cubic remainder used by the refined Taylor bound. -/
noncomputable def shiftedPositiveCubicImportanceWeightedMoment
    {Action : Type u}
    (arms : Finset Action) (prob loss : Action -> Real)
    (chosen : Action) : Real :=
  arms.sum (fun action =>
    (prob action) ^ 2 *
      (max (loss chosen -
        Exp3.importanceWeightedLoss prob loss chosen action) 0) ^ 3)

/-- Reindex a weighted sum over complements using simplex normalization. -/
theorem sum_mul_sum_erase_eq_sum_mul_one_sub
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob weight : Action -> Real)
    (hsum : arms.sum prob = 1) :
    arms.sum (fun chosen =>
        prob chosen * (arms.erase chosen).sum weight) =
      arms.sum (fun action => weight action * (1 - prob action)) := by
  calc
    arms.sum (fun chosen =>
        prob chosen * (arms.erase chosen).sum weight) =
        arms.sum (fun chosen =>
          prob chosen * (arms.sum weight - weight chosen)) := by
      apply Finset.sum_congr rfl
      intro chosen hchosen
      rw [show (arms.erase chosen).sum weight =
        arms.sum weight - weight chosen by
          rw [← Finset.sum_erase_add _ _ hchosen]
          ring]
    _ = arms.sum (fun chosen =>
        prob chosen * arms.sum weight - prob chosen * weight chosen) := by
      apply Finset.sum_congr rfl
      intro chosen _hchosen
      ring
    _ = arms.sum prob * arms.sum weight -
        arms.sum (fun action => prob action * weight action) := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = arms.sum weight -
        arms.sum (fun action => weight action * prob action) := by
      rw [hsum]
      simp only [one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro action _haction
      ring
    _ = arms.sum (fun action =>
        weight action - weight action * prob action) := by
      rw [Finset.sum_sub_distrib]
    _ = arms.sum (fun action => weight action * (1 - prob action)) := by
      apply Finset.sum_congr rfl
      intro action _haction
      ring

/-- Exact sampled-action expansion of the shifted quadratic moment. -/
theorem prob_mul_shiftedHalfPowerImportanceWeightedMoment_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    {chosen : Action} (hchosen : chosen ∈ arms)
    (hprob : 0 < prob chosen) :
    prob chosen *
        shiftedHalfPowerImportanceWeightedMoment arms prob loss chosen =
      (loss chosen) ^ 2 *
        (Real.sqrt (prob chosen) * (1 - prob chosen) ^ 2 +
          prob chosen * (arms.erase chosen).sum (fun action =>
            Real.sqrt (prob action) * prob action)) := by
  unfold shiftedHalfPowerImportanceWeightedMoment
  rw [Finset.mul_sum]
  rw [← Finset.sum_erase_add _ _ hchosen]
  have hchosenTerm :
      prob chosen *
          (Real.sqrt (prob chosen) * prob chosen *
            (Exp3.importanceWeightedLoss prob loss chosen chosen -
              loss chosen) ^ 2) =
        (loss chosen) ^ 2 *
          (Real.sqrt (prob chosen) * (1 - prob chosen) ^ 2) := by
    simp only [Exp3.importanceWeightedLoss, if_true]
    field_simp [ne_of_gt hprob]
  rw [hchosenTerm]
  have herase :
      (arms.erase chosen).sum (fun action =>
          prob chosen *
            (Real.sqrt (prob action) * prob action *
              (Exp3.importanceWeightedLoss prob loss chosen action -
                loss chosen) ^ 2)) =
        (loss chosen) ^ 2 *
          (prob chosen * (arms.erase chosen).sum (fun action =>
            Real.sqrt (prob action) * prob action)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro action haction
    have hne : chosen ≠ action :=
      Ne.symm (Finset.ne_of_mem_erase haction)
    simp [Exp3.importanceWeightedLoss, hne]
    ring
  rw [herase]
  ring

/--
The sampled shifted quadratic IW moment is bounded by the refined all-arm
half-power mass.
-/
theorem sum_prob_mul_shiftedHalfPowerImportanceWeightedMoment_le
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hprobability : FTRL.finiteSimplex arms prob)
    (hprob : forall action, action ∈ arms -> 0 < prob action)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    arms.sum (fun chosen =>
        prob chosen *
          shiftedHalfPowerImportanceWeightedMoment arms prob loss chosen) <=
      arms.sum (fun action =>
        Real.sqrt (prob action) * (1 - prob action)) := by
  rw [Finset.sum_congr rfl (fun chosen hchosen =>
    prob_mul_shiftedHalfPowerImportanceWeightedMoment_eq
      arms prob loss hchosen (hprob chosen hchosen))]
  calc
    arms.sum (fun chosen =>
        (loss chosen) ^ 2 *
          (Real.sqrt (prob chosen) * (1 - prob chosen) ^ 2 +
            prob chosen * (arms.erase chosen).sum (fun action =>
              Real.sqrt (prob action) * prob action))) <=
        arms.sum (fun chosen =>
          Real.sqrt (prob chosen) * (1 - prob chosen) ^ 2 +
            prob chosen * (arms.erase chosen).sum (fun action =>
              Real.sqrt (prob action) * prob action)) := by
      apply Finset.sum_le_sum
      intro chosen hchosen
      have hl := hloss chosen hchosen
      have hpNonneg := hprobability.1 chosen hchosen
      have hpLeOne :=
        finiteSimplex_apply_le_one hprobability hchosen
      have heraseNonneg :
          0 <= (arms.erase chosen).sum (fun action =>
            Real.sqrt (prob action) * prob action) := by
        apply Finset.sum_nonneg
        intro action haction
        exact mul_nonneg (Real.sqrt_nonneg _)
          (hprobability.1 action (Finset.mem_of_mem_erase haction))
      have hinnerNonneg :
          0 <= Real.sqrt (prob chosen) * (1 - prob chosen) ^ 2 +
            prob chosen * (arms.erase chosen).sum (fun action =>
              Real.sqrt (prob action) * prob action) := by
        exact add_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
          (mul_nonneg hpNonneg heraseNonneg)
      nlinarith [sq_nonneg (loss chosen),
        mul_self_le_mul_self hl.1 hl.2]
    _ = arms.sum (fun action =>
        Real.sqrt (prob action) * (1 - prob action)) := by
      rw [Finset.sum_add_distrib]
      rw [sum_mul_sum_erase_eq_sum_mul_one_sub
        arms prob (fun action => Real.sqrt (prob action) * prob action)
        hprobability.2]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro action _haction
      ring

/-- Exact sampled-action expansion of the positive cubic remainder. -/
theorem prob_mul_shiftedPositiveCubicImportanceWeightedMoment_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    {chosen : Action} (hchosen : chosen ∈ arms)
    (hprob : 0 < prob chosen) (hprobLeOne : prob chosen <= 1)
    (hlossNonneg : 0 <= loss chosen) :
    prob chosen *
        shiftedPositiveCubicImportanceWeightedMoment arms prob loss chosen =
      prob chosen * (loss chosen) ^ 3 *
        (arms.erase chosen).sum (fun action => (prob action) ^ 2) := by
  unfold shiftedPositiveCubicImportanceWeightedMoment
  rw [Finset.mul_sum]
  rw [← Finset.sum_erase_add _ _ hchosen]
  have hselected :
      max (loss chosen -
        Exp3.importanceWeightedLoss prob loss chosen chosen) 0 = 0 := by
    simp only [Exp3.importanceWeightedLoss, if_true]
    rw [max_eq_right]
    apply sub_nonpos.2
    apply (le_div_iff₀ hprob).2
    nlinarith
  simp only [hselected, zero_pow (by norm_num : 3 ≠ 0), mul_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro action haction
  have hne : chosen ≠ action :=
    Ne.symm (Finset.ne_of_mem_erase haction)
  simp [Exp3.importanceWeightedLoss, hne, hlossNonneg]
  ring

/-- The sampled positive cubic IW remainder is at most one. -/
theorem sum_prob_mul_shiftedPositiveCubicImportanceWeightedMoment_le_one
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action -> Real)
    (hprobability : FTRL.finiteSimplex arms prob)
    (hprob : forall action, action ∈ arms -> 0 < prob action)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    arms.sum (fun chosen =>
        prob chosen *
          shiftedPositiveCubicImportanceWeightedMoment
            arms prob loss chosen) <= 1 := by
  rw [Finset.sum_congr rfl (fun chosen hchosen =>
    prob_mul_shiftedPositiveCubicImportanceWeightedMoment_eq
      arms prob loss hchosen (hprob chosen hchosen)
      (finiteSimplex_apply_le_one hprobability hchosen)
      (hloss chosen hchosen).1)]
  calc
    arms.sum (fun chosen =>
        prob chosen * (loss chosen) ^ 3 *
          (arms.erase chosen).sum (fun action => (prob action) ^ 2)) <=
        arms.sum (fun chosen =>
          prob chosen *
            (arms.erase chosen).sum (fun action => (prob action) ^ 2)) := by
      apply Finset.sum_le_sum
      intro chosen hchosen
      have hp := hprobability.1 chosen hchosen
      have hl := hloss chosen hchosen
      have heraseNonneg :
          0 <= (arms.erase chosen).sum (fun action => (prob action) ^ 2) := by
        positivity
      have hlcube : (loss chosen) ^ 3 <= 1 := by
        nlinarith [sq_nonneg (loss chosen),
          mul_self_le_mul_self hl.1 hl.2]
      calc
        prob chosen * (loss chosen) ^ 3 *
            (arms.erase chosen).sum (fun action => (prob action) ^ 2) =
            (prob chosen *
              (arms.erase chosen).sum (fun action => (prob action) ^ 2)) *
                (loss chosen) ^ 3 := by ring
        _ <= (prob chosen *
              (arms.erase chosen).sum (fun action => (prob action) ^ 2)) *
                1 :=
          mul_le_mul_of_nonneg_left hlcube
            (mul_nonneg hp heraseNonneg)
        _ = prob chosen *
            (arms.erase chosen).sum (fun action => (prob action) ^ 2) := by
          ring
    _ = arms.sum (fun action =>
        (prob action) ^ 2 * (1 - prob action)) := by
      exact sum_mul_sum_erase_eq_sum_mul_one_sub
        arms prob (fun action => (prob action) ^ 2) hprobability.2
    _ <= arms.sum (fun action => (prob action) ^ 2) := by
      apply Finset.sum_le_sum
      intro action haction
      have hp := hprobability.1 action haction
      have hpLeOne :=
        finiteSimplex_apply_le_one hprobability haction
      nlinarith [sq_nonneg (prob action)]
    _ <= arms.sum prob := by
      apply Finset.sum_le_sum
      intro action haction
      have hp := hprobability.1 action haction
      have hpLeOne :=
        finiteSimplex_apply_le_one hprobability haction
      nlinarith [sq_nonneg (prob action)]
    _ = 1 := hprobability.2

/--
Paper-shaped finite-sum consumer for a shifted Taylor/Hessian stability bound.

The remaining hypothesis is deliberately pointwise: a producer must compare
its instantaneous stability quantity with the shifted quadratic and positive
cubic moments.  This theorem performs all sampled-action averaging.
-/
theorem sum_prob_mul_stability_le_refinedHalfPower_add_square
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (prob loss stability : Action -> Real)
    (heta : 0 <= eta)
    (hprobability : FTRL.finiteSimplex arms prob)
    (hprob : forall action, action ∈ arms -> 0 < prob action)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1)
    (hpointwise : forall chosen, chosen ∈ arms ->
      stability chosen <=
        eta / 2 *
            shiftedHalfPowerImportanceWeightedMoment
              arms prob loss chosen +
          eta ^ 2 / 2 *
            shiftedPositiveCubicImportanceWeightedMoment
              arms prob loss chosen) :
    arms.sum (fun chosen => prob chosen * stability chosen) <=
      eta / 2 * arms.sum (fun action =>
        Real.sqrt (prob action) * (1 - prob action)) +
        eta ^ 2 / 2 := by
  have hquadratic :=
    sum_prob_mul_shiftedHalfPowerImportanceWeightedMoment_le
      arms prob loss hprobability hprob hloss
  have hcubic :=
    sum_prob_mul_shiftedPositiveCubicImportanceWeightedMoment_le_one
      arms prob loss hprobability hprob hloss
  calc
    arms.sum (fun chosen => prob chosen * stability chosen) <=
        arms.sum (fun chosen =>
          prob chosen *
            (eta / 2 *
                shiftedHalfPowerImportanceWeightedMoment
                  arms prob loss chosen +
              eta ^ 2 / 2 *
                shiftedPositiveCubicImportanceWeightedMoment
                  arms prob loss chosen)) := by
      apply Finset.sum_le_sum
      intro chosen hchosen
      exact mul_le_mul_of_nonneg_left (hpointwise chosen hchosen)
        (hprobability.1 chosen hchosen)
    _ = eta / 2 *
          arms.sum (fun chosen =>
            prob chosen *
              shiftedHalfPowerImportanceWeightedMoment
                arms prob loss chosen) +
        eta ^ 2 / 2 *
          arms.sum (fun chosen =>
            prob chosen *
              shiftedPositiveCubicImportanceWeightedMoment
                arms prob loss chosen) := by
      calc
        arms.sum (fun chosen =>
            prob chosen *
              (eta / 2 *
                  shiftedHalfPowerImportanceWeightedMoment
                    arms prob loss chosen +
                eta ^ 2 / 2 *
                  shiftedPositiveCubicImportanceWeightedMoment
                    arms prob loss chosen)) =
            arms.sum (fun chosen =>
              eta / 2 *
                  (prob chosen *
                    shiftedHalfPowerImportanceWeightedMoment
                      arms prob loss chosen) +
                eta ^ 2 / 2 *
                  (prob chosen *
                    shiftedPositiveCubicImportanceWeightedMoment
                      arms prob loss chosen)) := by
          apply Finset.sum_congr rfl
          intro chosen _hchosen
          ring
        _ = eta / 2 *
              arms.sum (fun chosen =>
                prob chosen *
                  shiftedHalfPowerImportanceWeightedMoment
                    arms prob loss chosen) +
            eta ^ 2 / 2 *
              arms.sum (fun chosen =>
                prob chosen *
                  shiftedPositiveCubicImportanceWeightedMoment
                    arms prob loss chosen) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ <= eta / 2 * arms.sum (fun action =>
          Real.sqrt (prob action) * (1 - prob action)) +
        eta ^ 2 / 2 * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hquadratic (div_nonneg heta (by norm_num)))
        (mul_le_mul_of_nonneg_left hcubic (div_nonneg (sq_nonneg eta) (by norm_num)))
    _ = eta / 2 * arms.sum (fun action =>
          Real.sqrt (prob action) * (1 - prob action)) +
        eta ^ 2 / 2 := by ring

/--
Exact current-FTRL-expression wrapper around the shifted-moment consumer.

The sole unresolved premise is the deterministic shifted Taylor/Hessian
comparison for each sampled-action update.
-/
theorem sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_refined_of_shiftedTaylor
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (prob loss : Action -> Real) (next : Action -> Action -> Real)
    (heta : 0 <= eta)
    (hprobability : FTRL.finiteSimplex arms prob)
    (hprob : forall action, action ∈ arms -> 0 < prob action)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1)
    (hshiftedTaylor : forall chosen, chosen ∈ arms ->
      FTRL.linearLoss arms prob
            (Exp3.importanceWeightedLoss prob loss chosen) -
          FTRL.linearLoss arms (next chosen)
            (Exp3.importanceWeightedLoss prob loss chosen) <=
        eta / 2 *
            shiftedHalfPowerImportanceWeightedMoment
              arms prob loss chosen +
          eta ^ 2 / 2 *
            shiftedPositiveCubicImportanceWeightedMoment
              arms prob loss chosen) :
    arms.sum (fun chosen =>
        prob chosen *
          (FTRL.linearLoss arms prob
              (Exp3.importanceWeightedLoss prob loss chosen) -
            FTRL.linearLoss arms (next chosen)
              (Exp3.importanceWeightedLoss prob loss chosen))) <=
      eta / 2 * arms.sum (fun action =>
        Real.sqrt (prob action) * (1 - prob action)) +
        eta ^ 2 / 2 := by
  exact sum_prob_mul_stability_le_refinedHalfPower_add_square
    arms eta prob loss
    (fun chosen =>
      FTRL.linearLoss arms prob
          (Exp3.importanceWeightedLoss prob loss chosen) -
        FTRL.linearLoss arms (next chosen)
          (Exp3.importanceWeightedLoss prob loss chosen))
    heta hprobability hprob hloss hshiftedTaylor

end Tsallis
end BanditRLProof
