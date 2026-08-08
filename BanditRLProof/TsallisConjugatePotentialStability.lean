import BanditRLProof.TsallisRefinedImportanceWeightedMoment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Half-Tsallis conjugate-potential stability

This module formalizes the deterministic potential quantity used in the
paper-faithful refined Tsallis-INF stability route.  The local learning-rate
normalization is half the paper normalization, so the translated Lemma 19
coefficients are `eta` for the quadratic term and `2 * eta^2` for the positive
cubic remainder.

The constrained potential is represented by the negative regularized
objective value at a certified simplex minimizer, plus `1 / eta`.  That final
constant matches the paper normalization under `eta_paper = 2 * eta_local`; it
cancels in every fixed-eta step here but must be present for future cross-eta
telescoping.  The explicit coordinate increment is the unconstrained
half-Tsallis conjugate upper bound.  Their connection is proved below from
interior stationarity and simplex normalization; no measure, kernel, or
trajectory premise is involved.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/--
The paper-normalized negative regularized-objective value.  When `probability`
is a certified minimizer and `eta > 0`, this is the constrained half-Tsallis
potential under the local-to-paper learning-rate translation.
-/
noncomputable def halfTsallisPotentialValue
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score probability : Action -> Real) : Real :=
  -FTRL.regularizedObjective arms eta
      (negEntropyRegularizer arms (1 / 2 : Real)) score probability / eta +
    1 / eta

/--
The one-step candidate-potential expression before taking a sampling average.
The low-level feasible-next bridge treats `next` only as a candidate point;
the algorithm-facing theorems require both current and next minimizer
certificates.
-/
noncomputable def halfTsallisPotentialStability
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score probability estimate next : Action -> Real) : Real :=
  FTRL.linearLoss arms probability estimate +
    halfTsallisPotentialValue arms eta
      (fun action => score action + estimate action) next -
    halfTsallisPotentialValue arms eta score probability

/--
The coordinate increment obtained from the explicit unconstrained conjugate.
The shift is `estimate action - baseline`.
-/
noncomputable def halfTsallisConjugateCoordinateIncrement
    (eta probability shift : Real) : Real :=
  probability * shift +
    Real.sqrt probability /
      (eta * (1 + eta * shift * Real.sqrt probability)) -
    Real.sqrt probability / eta

/-- Finite sum of explicit conjugate coordinate increments. -/
noncomputable def halfTsallisConjugatePotentialUpper
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (probability estimate : Action -> Real) (baseline : Real) : Real :=
  arms.sum (fun action =>
    halfTsallisConjugateCoordinateIncrement eta (probability action)
      (estimate action - baseline))

theorem one_add_eta_mul_shift_mul_sqrt_pos
    {eta probability shift : Real}
    (_heta : 0 < eta) (hprobability : 0 < probability)
    (hdomain : -1 <= 2 * eta * shift * Real.sqrt probability) :
    0 < 1 + eta * shift * Real.sqrt probability := by
  have hsqrt : 0 < Real.sqrt probability := Real.sqrt_pos.2 hprobability
  nlinarith

/-- Exact rational form of the explicit conjugate coordinate increment. -/
theorem halfTsallisConjugateCoordinateIncrement_eq
    {eta probability shift : Real}
    (heta : 0 < eta) (hprobability : 0 < probability)
    (hdomain : -1 <= 2 * eta * shift * Real.sqrt probability) :
    halfTsallisConjugateCoordinateIncrement eta probability shift =
      eta * Real.sqrt probability * probability * shift ^ 2 /
        (1 + eta * shift * Real.sqrt probability) := by
  let s := Real.sqrt probability
  let denominator := 1 + eta * shift * s
  have hsqrt : 0 < s := by simpa [s] using Real.sqrt_pos.2 hprobability
  have hsqrt_sq : s ^ 2 = probability := by
    simpa [s] using Real.sq_sqrt hprobability.le
  have hden : 0 < denominator := by
    simpa [denominator, s] using
      one_add_eta_mul_shift_mul_sqrt_pos heta hprobability hdomain
  have hetaNe : eta ≠ 0 := ne_of_gt heta
  have hdenNe : denominator ≠ 0 := ne_of_gt hden
  unfold halfTsallisConjugateCoordinateIncrement
  change probability * shift + s / (eta * denominator) - s / eta =
    eta * s * probability * shift ^ 2 / denominator
  apply (eq_div_iff hdenNe).2
  have hcancel : s / (eta * denominator) * denominator = s / eta := by
    field_simp [hetaNe, hdenNe]
  calc
    (probability * shift + s / (eta * denominator) - s / eta) *
        denominator =
      probability * shift * denominator +
        (s / (eta * denominator) * denominator) -
        (s / eta) * denominator := by ring
    _ = probability * shift * denominator + s / eta -
        (s / eta) * denominator := by rw [hcancel]
    _ = eta * s * probability * shift ^ 2 := by
      field_simp [hetaNe]
      linear_combination -eta * shift * hsqrt_sq

/--
Scalar translated Lemma 19 bound.  The positive cubic term is active only
when the shifted estimate is negative.
-/
theorem halfTsallisConjugateCoordinateIncrement_le
    {eta probability shift : Real}
    (heta : 0 < eta) (hprobability : 0 < probability)
    (hdomain : -1 <= 2 * eta * shift * Real.sqrt probability) :
    halfTsallisConjugateCoordinateIncrement eta probability shift <=
      eta * Real.sqrt probability * probability * shift ^ 2 +
        2 * eta ^ 2 * probability ^ 2 * (max (-shift) 0) ^ 3 := by
  rw [halfTsallisConjugateCoordinateIncrement_eq
    heta hprobability hdomain]
  have hsqrt : 0 < Real.sqrt probability := Real.sqrt_pos.2 hprobability
  have hsqrt_sq : (Real.sqrt probability) ^ 2 = probability :=
    Real.sq_sqrt hprobability.le
  have hden := one_add_eta_mul_shift_mul_sqrt_pos
    heta hprobability hdomain
  by_cases hshift : 0 <= shift
  · rw [max_eq_right]
    · simp only [zero_pow (by norm_num : (3 : Nat) ≠ 0), mul_zero, add_zero]
      apply (div_le_iff₀ hden).2
      have hmain :
          0 <= eta * Real.sqrt probability * probability * shift ^ 2 := by
        positivity
      have hdenOne : 1 <= 1 + eta * shift * Real.sqrt probability := by
        have : 0 <= eta * shift * Real.sqrt probability := by positivity
        linarith
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hdenOne hmain)
    · linarith
  · have hshiftNeg : shift < 0 := lt_of_not_ge hshift
    rw [max_eq_left (by linarith : 0 <= -shift)]
    apply (div_le_iff₀ hden).2
    have hbase :
        0 <= eta * Real.sqrt probability * probability * shift ^ 2 := by
      positivity
    have hremainder :
        0 <= 2 * eta ^ 2 * probability ^ 2 * (-shift) ^ 3 := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (by positivity))
        (pow_nonneg (by linarith) 3)
    have hfactor :
        (eta * Real.sqrt probability * probability * shift ^ 2 +
              2 * eta ^ 2 * probability ^ 2 * (-shift) ^ 3) *
            (1 + eta * shift * Real.sqrt probability) -
          eta * Real.sqrt probability * probability * shift ^ 2 =
        eta ^ 2 * probability ^ 2 * (-shift) ^ 3 *
          (1 + 2 * eta * shift * Real.sqrt probability) := by
      linear_combination
        eta ^ 2 * probability * shift ^ 3 * hsqrt_sq
    have hfactorNonneg :
        0 <= eta ^ 2 * probability ^ 2 * (-shift) ^ 3 *
          (1 + 2 * eta * shift * Real.sqrt probability) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg eta) (sq_nonneg probability))
          (pow_nonneg (by linarith) 3))
        (by linarith)
    linarith

/-- Coordinatewise Fenchel upper bound for a nonnegative competitor weight. -/
theorem halfTsallis_fenchelCoordinate_le
    {eta probability competitor shift : Real}
    (heta : 0 < eta) (hprobability : 0 < probability)
    (hcompetitor : 0 <= competitor)
    (hdomain : -1 <= 2 * eta * shift * Real.sqrt probability) :
    -competitor / (eta * Real.sqrt probability) - competitor * shift +
        2 * Real.sqrt competitor / eta <=
      Real.sqrt probability /
        (eta * (1 + eta * shift * Real.sqrt probability)) := by
  let s := Real.sqrt probability
  let r := Real.sqrt competitor
  let denominator := 1 + eta * shift * s
  have hs : 0 < s := by simpa [s] using Real.sqrt_pos.2 hprobability
  have hrSq : r ^ 2 = competitor := by
    simpa [r] using Real.sq_sqrt hcompetitor
  have hden : 0 < denominator := by
    simpa [denominator, s] using
      one_add_eta_mul_shift_mul_sqrt_pos heta hprobability hdomain
  have hetaS : 0 < eta * s := mul_pos heta hs
  have hetaDen : 0 < eta * denominator := mul_pos heta hden
  have hleft :
      -competitor / (eta * s) - competitor * shift + 2 * r / eta =
        (-competitor * denominator + 2 * s * r) / (eta * s) := by
    field_simp [ne_of_gt heta, ne_of_gt hs]
    ring
  have hcore :
      (-competitor * denominator + 2 * s * r) * denominator <= s ^ 2 := by
    rw [← hrSq]
    nlinarith [sq_nonneg (r * denominator - s)]
  rw [hleft]
  apply (div_le_div_iff₀ hetaS hetaDen).2
  calc
    (-competitor * denominator + 2 * s * r) *
        (eta * denominator) =
      eta * ((-competitor * denominator + 2 * s * r) * denominator) := by
        ring
    _ <= eta * s ^ 2 := mul_le_mul_of_nonneg_left hcore heta.le
    _ = s * (eta * s) := by ring

/-- The explicit conjugate finite sum is bounded by shifted quadratic/cubic moments. -/
theorem halfTsallisConjugatePotentialUpper_le_shiftedMoments
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (probability estimate : Action -> Real) (baseline : Real)
    (heta : 0 < eta)
    (hprobability : forall action, action ∈ arms -> 0 < probability action)
    (hdomain : forall action, action ∈ arms ->
      -1 <= 2 * eta * (estimate action - baseline) *
        Real.sqrt (probability action)) :
    halfTsallisConjugatePotentialUpper
        arms eta probability estimate baseline <=
      eta * arms.sum (fun action =>
        Real.sqrt (probability action) * probability action *
          (estimate action - baseline) ^ 2) +
      2 * eta ^ 2 * arms.sum (fun action =>
        probability action ^ 2 *
          (max (baseline - estimate action) 0) ^ 3) := by
  unfold halfTsallisConjugatePotentialUpper
  calc
    arms.sum (fun action =>
        halfTsallisConjugateCoordinateIncrement eta (probability action)
          (estimate action - baseline)) <=
      arms.sum (fun action =>
        eta * Real.sqrt (probability action) * probability action *
            (estimate action - baseline) ^ 2 +
          2 * eta ^ 2 * probability action ^ 2 *
            (max (-(estimate action - baseline)) 0) ^ 3) := by
      apply Finset.sum_le_sum
      intro action haction
      exact halfTsallisConjugateCoordinateIncrement_le heta
        (hprobability action haction) (hdomain action haction)
    _ = eta * arms.sum (fun action =>
          Real.sqrt (probability action) * probability action *
            (estimate action - baseline) ^ 2) +
        2 * eta ^ 2 * arms.sum (fun action =>
          probability action ^ 2 *
            (max (baseline - estimate action) 0) ^ 3) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro action _haction
        ring
      · apply Finset.sum_congr rfl
        intro action _haction
        have hshift :
            -(estimate action - baseline) = baseline - estimate action := by
          ring
        rw [hshift]
        ring

/-- Ordinary importance-weighted estimates satisfy the translated conjugate domain. -/
theorem importanceWeightedLoss_sub_selectedLoss_conjugate_domain
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (probability loss : Action -> Real)
    (heta : 0 < eta) (heta_le : eta <= 1 / 2)
    (hprobability : FTRL.finiteSimplex arms probability)
    (hprobabilityPos : forall action, action ∈ arms -> 0 < probability action)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1)
    {chosen action : Action} (hchosen : chosen ∈ arms) (haction : action ∈ arms) :
    -1 <= 2 * eta *
      (Exp3.importanceWeightedLoss probability loss chosen action - loss chosen) *
        Real.sqrt (probability action) := by
  by_cases hsame : chosen = action
  · subst action
    have hp := hprobabilityPos chosen hchosen
    have hpLe := finiteSimplex_apply_le_one hprobability hchosen
    have hl := hloss chosen hchosen
    have hlDiv : loss chosen <= loss chosen / probability chosen := by
      apply (le_div_iff₀ hp).2
      calc
        loss chosen * probability chosen <= loss chosen * 1 :=
          mul_le_mul_of_nonneg_left hpLe hl.1
        _ = loss chosen := by ring
    have hshift :
        0 <= loss chosen / probability chosen - loss chosen := sub_nonneg.2 hlDiv
    simp only [Exp3.importanceWeightedLoss, if_true]
    have : 0 <= 2 * eta *
        (loss chosen / probability chosen - loss chosen) *
          Real.sqrt (probability chosen) := by positivity
    linarith
  · have hpNonneg := hprobability.1 action haction
    have hpLe := finiteSimplex_apply_le_one hprobability haction
    have hsqrtLe : Real.sqrt (probability action) <= 1 :=
      Real.sqrt_le_one.2 hpLe
    have hl := hloss chosen hchosen
    have htwoEtaNonneg : 0 <= 2 * eta := by positivity
    have htwoEtaLe : 2 * eta <= 1 := by nlinarith
    have hscaledLoss : 2 * eta * loss chosen <= 1 := by
      calc
        2 * eta * loss chosen <= 2 * eta * 1 :=
          mul_le_mul_of_nonneg_left hl.2 htwoEtaNonneg
        _ <= 1 := by simpa using htwoEtaLe
    have hproduct :
        2 * eta * loss chosen * Real.sqrt (probability action) <= 1 := by
      calc
        2 * eta * loss chosen * Real.sqrt (probability action) <=
            2 * eta * loss chosen * 1 :=
          mul_le_mul_of_nonneg_left hsqrtLe
            (mul_nonneg htwoEtaNonneg hl.1)
        _ <= 1 := by simpa using hscaledLoss
    simp [Exp3.importanceWeightedLoss, hsame]
    nlinarith

theorem linearLoss_sub_linearLoss_eq_sum_sub_mul
    {Action : Type u}
    (arms : Finset Action) (p q score : Action -> Real) :
    FTRL.linearLoss arms p score - FTRL.linearLoss arms q score =
      arms.sum (fun action => (p action - q action) * score action) := by
  unfold FTRL.linearLoss
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro action _haction
  ring

theorem sum_sub_mul_sub_baseline_eq_sum_sub_mul
    {Action : Type u}
    (arms : Finset Action) (p q value : Action -> Real) (baseline : Real)
    (hp : arms.sum p = 1) (hq : arms.sum q = 1) :
    arms.sum (fun action =>
        (p action - q action) * (value action - baseline)) =
      arms.sum (fun action => (p action - q action) * value action) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hbaseline :
      arms.sum (fun action => (p action - q action) * baseline) = 0 := by
    calc
      arms.sum (fun action => (p action - q action) * baseline) =
          (arms.sum p - arms.sum q) * baseline := by
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
      _ = 0 := by rw [hp, hq]; ring
  rw [hbaseline, sub_zero]

/-- Stationarity removes the score and its common simplex multiplier. -/
theorem linearLoss_sub_linearLoss_score_eq_sum_div_sqrt_of_stationary
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score p q : Action -> Real) (multiplier : Real)
    (heta : 0 < eta)
    (hp : FTRL.finiteSimplex arms p)
    (hq : FTRL.finiteSimplex arms q)
    (hpPos : forall action, action ∈ arms -> 0 < p action)
    (hstationary : HalfTsallisInteriorStationary
      arms eta score p multiplier) :
    FTRL.linearLoss arms p score - FTRL.linearLoss arms q score =
      arms.sum (fun action =>
        (p action - q action) / (eta * Real.sqrt (p action))) := by
  rw [linearLoss_sub_linearLoss_eq_sum_sub_mul]
  have hscore : forall action, action ∈ arms ->
      score action = multiplier / eta +
        1 / (eta * Real.sqrt (p action)) := by
    intro action haction
    have hpAction := hpPos action haction
    have hrpow :
        (p action) ^ (-(1 / 2 : Real)) =
          1 / Real.sqrt (p action) := by
      rw [Real.rpow_neg hpAction.le, ← Real.sqrt_eq_rpow]
      simp [one_div]
    have hstat := hstationary action haction
    rw [hrpow] at hstat
    calc
      score action = (multiplier + 1 / Real.sqrt (p action)) / eta := by
        apply (eq_div_iff (ne_of_gt heta)).2
        linarith
      _ = multiplier / eta +
          1 / (eta * Real.sqrt (p action)) := by
        field_simp [ne_of_gt heta, ne_of_gt (Real.sqrt_pos.2 hpAction)]
  rw [Finset.sum_congr rfl (fun action haction => by
    rw [hscore action haction])]
  have hsumDiff : arms.sum (fun action => p action - q action) = 0 := by
    rw [Finset.sum_sub_distrib, hp.2, hq.2]
    ring
  calc
    arms.sum (fun action =>
        (p action - q action) *
          (multiplier / eta + 1 / (eta * Real.sqrt (p action)))) =
      multiplier / eta * arms.sum (fun action => p action - q action) +
        arms.sum (fun action =>
          (p action - q action) / (eta * Real.sqrt (p action))) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro action _haction
        ring
      · apply Finset.sum_congr rfl
        intro action _haction
        ring
    _ = arms.sum (fun action =>
          (p action - q action) / (eta * Real.sqrt (p action))) := by
      rw [hsumDiff]
      ring

/--
The feasible-next candidate-potential expression is bounded by the explicit
unconstrained conjugate sum.  Only the current point needs stationarity.  This
is an algebraic bridge, not an actual constrained-potential theorem unless the
caller separately certifies that `next` minimizes the updated objective.
-/
theorem halfTsallisPotentialStability_le_conjugatePotentialUpper_of_feasible
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score probability estimate next : Action -> Real)
    (baseline multiplier : Real)
    (heta : 0 < eta)
    (hprobability : FTRL.finiteSimplex arms probability)
    (hnext : FTRL.finiteSimplex arms next)
    (hprobabilityPos : forall action, action ∈ arms -> 0 < probability action)
    (hstationary : HalfTsallisInteriorStationary
      arms eta score probability multiplier)
    (hdomain : forall action, action ∈ arms ->
      -1 <= 2 * eta * (estimate action - baseline) *
        Real.sqrt (probability action)) :
    halfTsallisPotentialStability
        arms eta score probability estimate next <=
      halfTsallisConjugatePotentialUpper
        arms eta probability estimate baseline := by
  have hetaNe : eta ≠ 0 := ne_of_gt heta
  have hlinearAdd :
      FTRL.linearLoss arms next (fun action => score action + estimate action) =
        FTRL.linearLoss arms next score +
          FTRL.linearLoss arms next estimate := by
    unfold FTRL.linearLoss
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
  have hstability :
      halfTsallisPotentialStability arms eta score probability estimate next =
        (FTRL.linearLoss arms probability estimate -
            FTRL.linearLoss arms next estimate) +
          (FTRL.linearLoss arms probability score -
            FTRL.linearLoss arms next score) +
          2 / eta *
            (arms.sum (fun action => Real.sqrt (next action)) -
              arms.sum (fun action => Real.sqrt (probability action))) := by
    unfold halfTsallisPotentialStability halfTsallisPotentialValue
    rw [regularizedObjective_half_eq, regularizedObjective_half_eq, hlinearAdd]
    field_simp [hetaNe]
    ring
  have hscore :=
    linearLoss_sub_linearLoss_score_eq_sum_div_sqrt_of_stationary
      arms eta score probability next multiplier heta hprobability hnext
      hprobabilityPos hstationary
  have hestimate :
      FTRL.linearLoss arms probability estimate -
          FTRL.linearLoss arms next estimate =
        arms.sum (fun action =>
          (probability action - next action) *
            (estimate action - baseline)) := by
    rw [linearLoss_sub_linearLoss_eq_sum_sub_mul]
    symm
    exact sum_sub_mul_sub_baseline_eq_sum_sub_mul
      arms probability next estimate baseline hprobability.2 hnext.2
  have hsqrt :
      2 / eta *
          (arms.sum (fun action => Real.sqrt (next action)) -
            arms.sum (fun action => Real.sqrt (probability action))) =
        arms.sum (fun action =>
          2 / eta *
            (Real.sqrt (next action) - Real.sqrt (probability action))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro action _haction
    ring
  rw [hstability, hscore, hestimate, hsqrt]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  unfold halfTsallisConjugatePotentialUpper
  apply Finset.sum_le_sum
  intro action haction
  have hfenchel := halfTsallis_fenchelCoordinate_le
    heta (hprobabilityPos action haction) (hnext.1 action haction)
    (hdomain action haction)
  have hpAction := hprobabilityPos action haction
  have hsqrtSq : (Real.sqrt (probability action)) ^ 2 =
      probability action := Real.sq_sqrt hpAction.le
  have hprobDiv :
      probability action /
          (eta * Real.sqrt (probability action)) =
        Real.sqrt (probability action) / eta := by
    field_simp [hetaNe, ne_of_gt (Real.sqrt_pos.2 hpAction)]
    linear_combination -hsqrtSq
  calc
    (probability action - next action) * (estimate action - baseline) +
          (probability action - next action) /
            (eta * Real.sqrt (probability action)) +
        2 / eta *
          (Real.sqrt (next action) - Real.sqrt (probability action)) =
      probability action * (estimate action - baseline) -
          Real.sqrt (probability action) / eta +
        (-next action / (eta * Real.sqrt (probability action)) -
            next action * (estimate action - baseline) +
          2 * Real.sqrt (next action) / eta) := by
      rw [sub_div, hprobDiv]
      ring
    _ <= probability action * (estimate action - baseline) -
          Real.sqrt (probability action) / eta +
        Real.sqrt (probability action) /
          (eta * (1 + eta * (estimate action - baseline) *
            Real.sqrt (probability action))) := by
      simpa [add_assoc, add_comm, add_left_comm] using
        (add_le_add_left hfenchel
          (probability action * (estimate action - baseline) -
            Real.sqrt (probability action) / eta))
    _ = halfTsallisConjugateCoordinateIncrement eta
          (probability action) (estimate action - baseline) := by
      unfold halfTsallisConjugateCoordinateIncrement
      ring

/--
Paper-faithful one-step conjugate-potential stability for an ordinary
importance-weighted sampled update.
-/
theorem halfTsallisPotentialStability_importanceWeightedLoss_le_shiftedMoments_of_minimizers
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score probability loss next : Action -> Real) (chosen : Action)
    (hchosen : chosen ∈ arms)
    (heta : 0 < eta) (heta_le : eta <= 1 / 2)
    (hprobabilityMin : FTRL.IsRegularizedMinimizer
      (FTRL.finiteSimplex arms) arms eta
      (negEntropyRegularizer arms (1 / 2 : Real)) score probability)
    (hnextMin : FTRL.IsRegularizedMinimizer
      (FTRL.finiteSimplex arms) arms eta
      (negEntropyRegularizer arms (1 / 2 : Real))
      (fun action => score action +
        Exp3.importanceWeightedLoss probability loss chosen action) next)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    halfTsallisPotentialStability arms eta score probability
        (Exp3.importanceWeightedLoss probability loss chosen) next <=
      eta * shiftedHalfPowerImportanceWeightedMoment
          arms probability loss chosen +
        2 * eta ^ 2 * shiftedPositiveCubicImportanceWeightedMoment
          arms probability loss chosen := by
  have hprobabilityPos :=
    isRegularizedMinimizer_pos arms eta score probability hprobabilityMin
  obtain ⟨multiplier, hstationary⟩ :=
    exists_halfTsallisInteriorStationary_of_isRegularizedMinimizer_auto
      arms eta score probability hprobabilityMin
  have hdomain : forall action, action ∈ arms ->
      -1 <= 2 * eta *
        (Exp3.importanceWeightedLoss probability loss chosen action -
          loss chosen) * Real.sqrt (probability action) := by
    intro action haction
    exact importanceWeightedLoss_sub_selectedLoss_conjugate_domain
      arms eta probability loss heta heta_le hprobabilityMin.1
      hprobabilityPos hloss hchosen haction
  have hbridge :=
    halfTsallisPotentialStability_le_conjugatePotentialUpper_of_feasible
      arms eta score probability
      (Exp3.importanceWeightedLoss probability loss chosen) next
      (loss chosen) multiplier heta hprobabilityMin.1 hnextMin.1
      hprobabilityPos hstationary hdomain
  have hupper :=
    halfTsallisConjugatePotentialUpper_le_shiftedMoments
      arms eta probability
      (Exp3.importanceWeightedLoss probability loss chosen) (loss chosen)
      heta hprobabilityPos hdomain
  calc
    halfTsallisPotentialStability arms eta score probability
        (Exp3.importanceWeightedLoss probability loss chosen) next <=
      halfTsallisConjugatePotentialUpper arms eta probability
        (Exp3.importanceWeightedLoss probability loss chosen) (loss chosen) :=
      hbridge
    _ <= eta * shiftedHalfPowerImportanceWeightedMoment
          arms probability loss chosen +
        2 * eta ^ 2 * shiftedPositiveCubicImportanceWeightedMoment
          arms probability loss chosen := by
      simpa [shiftedHalfPowerImportanceWeightedMoment,
        shiftedPositiveCubicImportanceWeightedMoment] using hupper

/--
Sampled-action averaged ordinary-IW conjugate-potential stability.  This is the
deterministic finite-action form of the refined coefficient used downstream by
the self-bounding route.
-/
theorem sum_prob_mul_halfTsallisPotentialStability_importanceWeightedLoss_le_refined_of_minimizers
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score probability loss : Action -> Real)
    (next : Action -> Action -> Real)
    (heta : 0 < eta) (heta_le : eta <= 1 / 2)
    (hprobabilityMin : FTRL.IsRegularizedMinimizer
      (FTRL.finiteSimplex arms) arms eta
      (negEntropyRegularizer arms (1 / 2 : Real)) score probability)
    (hnextMin : forall chosen, chosen ∈ arms ->
      FTRL.IsRegularizedMinimizer
        (FTRL.finiteSimplex arms) arms eta
        (negEntropyRegularizer arms (1 / 2 : Real))
        (fun action => score action +
          Exp3.importanceWeightedLoss probability loss chosen action)
        (next chosen))
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    arms.sum (fun chosen => probability chosen *
      halfTsallisPotentialStability arms eta score probability
        (Exp3.importanceWeightedLoss probability loss chosen) (next chosen)) <=
      eta * arms.sum (fun action =>
        Real.sqrt (probability action) * (1 - probability action)) +
        2 * eta ^ 2 := by
  have hprobabilityPos :=
    isRegularizedMinimizer_pos arms eta score probability hprobabilityMin
  have hquadratic :=
    sum_prob_mul_shiftedHalfPowerImportanceWeightedMoment_le
      arms probability loss hprobabilityMin.1 hprobabilityPos hloss
  have hcubic :=
    sum_prob_mul_shiftedPositiveCubicImportanceWeightedMoment_le_one
      arms probability loss hprobabilityMin.1 hprobabilityPos hloss
  calc
    arms.sum (fun chosen => probability chosen *
        halfTsallisPotentialStability arms eta score probability
          (Exp3.importanceWeightedLoss probability loss chosen)
          (next chosen)) <=
      arms.sum (fun chosen => probability chosen *
        (eta * shiftedHalfPowerImportanceWeightedMoment
            arms probability loss chosen +
          2 * eta ^ 2 * shiftedPositiveCubicImportanceWeightedMoment
            arms probability loss chosen)) := by
      apply Finset.sum_le_sum
      intro chosen hchosen
      exact mul_le_mul_of_nonneg_left
        (halfTsallisPotentialStability_importanceWeightedLoss_le_shiftedMoments_of_minimizers
          arms eta score probability loss (next chosen) chosen hchosen
          heta heta_le hprobabilityMin (hnextMin chosen hchosen) hloss)
        (hprobabilityMin.1.1 chosen hchosen)
    _ = eta * arms.sum (fun chosen => probability chosen *
          shiftedHalfPowerImportanceWeightedMoment
            arms probability loss chosen) +
        2 * eta ^ 2 * arms.sum (fun chosen => probability chosen *
          shiftedPositiveCubicImportanceWeightedMoment
            arms probability loss chosen) := by
      calc
        arms.sum (fun chosen => probability chosen *
            (eta * shiftedHalfPowerImportanceWeightedMoment
                arms probability loss chosen +
              2 * eta ^ 2 * shiftedPositiveCubicImportanceWeightedMoment
                arms probability loss chosen)) =
          arms.sum (fun chosen =>
              eta * (probability chosen *
                shiftedHalfPowerImportanceWeightedMoment
                  arms probability loss chosen) +
            2 * eta ^ 2 * (probability chosen *
              shiftedPositiveCubicImportanceWeightedMoment
                arms probability loss chosen)) := by
          apply Finset.sum_congr rfl
          intro chosen _hchosen
          ring
        _ = eta * arms.sum (fun chosen => probability chosen *
              shiftedHalfPowerImportanceWeightedMoment
                arms probability loss chosen) +
            2 * eta ^ 2 * arms.sum (fun chosen => probability chosen *
              shiftedPositiveCubicImportanceWeightedMoment
                arms probability loss chosen) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ <= eta * arms.sum (fun action =>
          Real.sqrt (probability action) * (1 - probability action)) +
        2 * eta ^ 2 * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hquadratic heta.le)
        (mul_le_mul_of_nonneg_left hcubic (by positivity))
    _ = eta * arms.sum (fun action =>
          Real.sqrt (probability action) * (1 - probability action)) +
        2 * eta ^ 2 := by ring

/-- Canonical-selector wrapper with all minimizer certificates discharged. -/
theorem sum_halfTsallisMinimizer_mul_potentialStability_le_refined
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score loss : Action -> Real)
    (heta : 0 < eta) (heta_le : eta <= 1 / 2)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    let probability := halfTsallisMinimizer arms harms eta score
    let next := fun chosen =>
      halfTsallisUpdatedMinimizer arms harms eta score loss chosen
    arms.sum (fun chosen => probability chosen *
      halfTsallisPotentialStability arms eta score probability
        (Exp3.importanceWeightedLoss probability loss chosen) (next chosen)) <=
      eta * arms.sum (fun action =>
        Real.sqrt (probability action) * (1 - probability action)) +
        2 * eta ^ 2 := by
  dsimp only
  exact
    sum_prob_mul_halfTsallisPotentialStability_importanceWeightedLoss_le_refined_of_minimizers
      arms eta score (halfTsallisMinimizer arms harms eta score) loss
      (fun chosen =>
        halfTsallisUpdatedMinimizer arms harms eta score loss chosen)
      heta heta_le
      (halfTsallisMinimizer_isRegularizedMinimizer arms harms eta score)
      (fun chosen _hchosen =>
        halfTsallisUpdatedMinimizer_isRegularizedMinimizer
          arms harms eta score loss chosen)
      hloss

end Tsallis
end BanditRLProof
