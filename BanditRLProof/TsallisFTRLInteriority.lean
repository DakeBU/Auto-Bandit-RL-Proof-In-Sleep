import BanditRLProof.TsallisFTRLStationarity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

/-!
# Interiority of half-Tsallis finite-simplex minimizers

The square-root regularizer has an infinite inward slope at a zero coordinate.
This module makes that boundary argument finite and algebraic: transfer a
sufficiently small positive mass from any positive donor coordinate to the
zero coordinate and contradict global minimality.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- A one-sided transfer from a positive donor to a zero coordinate stays in
the finite simplex. -/
theorem finiteSimplex_simplexPairShift_of_eq_zero_of_le
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : Action -> Real) (i j : Action) (t : Real)
    (hij : i ≠ j) (hp : FTRL.finiteSimplex arms p)
    (hi : i ∈ arms) (hj : j ∈ arms)
    (hpi : p i = 0) (ht : 0 <= t) (htj : t <= p j) :
    FTRL.finiteSimplex arms (simplexPairShift p i j t) := by
  constructor
  · intro a ha
    by_cases hai : a = i
    · subst a
      simp [simplexPairShift, pairDirection, hij, hpi, ht]
    · by_cases haj : a = j
      · subst a
        simp [simplexPairShift, pairDirection, hai, sub_eq_add_neg]
        linarith
      · simp [simplexPairShift, pairDirection, hai, haj, hp.1 a ha]
  · rw [sum_simplexPairShift arms p i j t hi hj, hp.2]

/-- Exact linear-loss change under a two-coordinate simplex transfer. -/
theorem linearLoss_simplexPairShift_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p score : Action -> Real) (i j : Action) (t : Real)
    (hi : i ∈ arms) (hj : j ∈ arms) :
    FTRL.linearLoss arms (simplexPairShift p i j t) score =
      FTRL.linearLoss arms p score + t * (score i - score j) := by
  unfold FTRL.linearLoss simplexPairShift
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,
    sum_pairDirection_mul arms i j score hi hj]

/-- Exact square-root-sum change when mass enters a zero coordinate. -/
theorem sum_sqrt_simplexPairShift_eq_of_eq_zero
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : Action -> Real) (i j : Action) (t : Real)
    (hij : i ≠ j) (hi : i ∈ arms) (hj : j ∈ arms) (hpi : p i = 0) :
    arms.sum (fun a => Real.sqrt (simplexPairShift p i j t a)) =
      arms.sum (fun a => Real.sqrt (p a)) + Real.sqrt t +
        Real.sqrt (p j - t) - Real.sqrt (p j) := by
  have hpoint : forall a, a ∈ arms ->
      Real.sqrt (simplexPairShift p i j t a) =
        Real.sqrt (p a) +
          (if a = i then Real.sqrt t - Real.sqrt (p i) else 0) +
          (if a = j then Real.sqrt (p j - t) - Real.sqrt (p j) else 0) := by
    intro a ha
    by_cases hai : a = i
    · subst a
      simp [simplexPairShift, pairDirection, hij, hpi]
    · by_cases haj : a = j
      · subst a
        simp [simplexPairShift, pairDirection, hai, sub_eq_add_neg]
      · simp [simplexPairShift, pairDirection, hai, haj]
  calc
    arms.sum (fun a => Real.sqrt (simplexPairShift p i j t a)) =
        arms.sum (fun a =>
          Real.sqrt (p a) +
            (if a = i then Real.sqrt t - Real.sqrt (p i) else 0) +
            (if a = j then Real.sqrt (p j - t) - Real.sqrt (p j) else 0)) :=
      Finset.sum_congr rfl hpoint
    _ = arms.sum (fun a => Real.sqrt (p a)) + Real.sqrt t +
          Real.sqrt (p j - t) - Real.sqrt (p j) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp [hi, hj, hpi]
      ring

/-- Removing mass `t` from a positive coordinate loses at most
`t / sqrt r` of square-root mass. -/
theorem sqrt_sub_sqrt_sub_le_div_sqrt
    {r t : Real} (hr : 0 < r) (ht : 0 <= t) (htr : t <= r) :
    Real.sqrt r - Real.sqrt (r - t) <= t / Real.sqrt r := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hrt : 0 <= r - t := sub_nonneg.2 htr
  have hsle : Real.sqrt (r - t) <= Real.sqrt r :=
    Real.sqrt_le_sqrt (by linarith)
  have hsrSq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr.le
  have hsubSq : (Real.sqrt (r - t)) ^ 2 = r - t := Real.sq_sqrt hrt
  apply (le_div_iff₀ hsr).2
  nlinarith [mul_nonneg (sub_nonneg.2 hsle) (Real.sqrt_nonneg (r - t))]

/-- At a zero coordinate, the square-root gain dominates any fixed linear
slope for a sufficiently small positive transfer from a positive donor. -/
theorem exists_transfer_strictly_improves_half_objective
    (r d : Real) (hr : 0 < r) :
    exists t, 0 < t ∧ t < r ∧
      d * t < 2 * (Real.sqrt t + Real.sqrt (r - t) - Real.sqrt r) := by
  let C : Real := |d| + 2 / Real.sqrt r
  let s : Real := min (Real.sqrt r / 2) (1 / (C + 1))
  let t : Real := s ^ 2
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hs : 0 < s := by
    dsimp [s]
    exact lt_min (by positivity) (by positivity)
  have hsR : s <= Real.sqrt r / 2 := by
    dsimp [s]
    exact min_le_left _ _
  have hsC : s <= 1 / (C + 1) := by
    dsimp [s]
    exact min_le_right _ _
  have htr : t < r := by
    have hsLt : s < Real.sqrt r := by linarith
    have hsrSq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr.le
    dsimp [t]
    nlinarith [sq_nonneg (Real.sqrt r - s)]
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hsqrtT : Real.sqrt t = s := by
    dsimp [t]
    simpa using Real.sqrt_sq hs.le
  have hdonor : Real.sqrt r - Real.sqrt (r - t) <= t / Real.sqrt r :=
    sqrt_sub_sqrt_sub_le_div_sqrt hr ht.le htr.le
  have hd : d * t <= |d| * t :=
    mul_le_mul_of_nonneg_right (le_abs_self d) ht.le
  have hratio : C / (C + 1) < 1 := by
    apply (div_lt_one (by linarith)).2
    linarith
  have hCs : C * s < 1 := by
    calc
      C * s <= C * (1 / (C + 1)) :=
        mul_le_mul_of_nonneg_left hsC hC.le
      _ = C / (C + 1) := by ring
      _ < 1 := hratio
  have hCss : C * s * s < s := by
    have := mul_lt_mul_of_pos_right hCs hs
    simpa [mul_assoc] using this
  refine ⟨t, ht, htr, ?_⟩
  have hbound :
      d * t - 2 * (Real.sqrt t + Real.sqrt (r - t) - Real.sqrt r) <=
        |d| * t - 2 * Real.sqrt t + 2 * (t / Real.sqrt r) := by
    linarith
  have heq :
      |d| * t - 2 * Real.sqrt t + 2 * (t / Real.sqrt r) =
        C * s * s - 2 * s := by
    rw [hsqrtT]
    dsimp [C, t]
    ring
  rw [heq] at hbound
  linarith

/-- Every supported coordinate of a half-Tsallis finite-simplex minimizer is
strictly positive.  No sign condition on `eta` or boundedness condition on the
finite score is needed. -/
theorem isRegularizedMinimizer_pos
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) (score p : Action -> Real)
    (hpMin : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p) :
    forall action, action ∈ arms -> 0 < p action := by
  intro i hi
  have hpiNonneg : 0 <= p i := hpMin.1.1 i hi
  by_contra hnot
  have hpi : p i = 0 := le_antisymm (not_lt.mp hnot) hpiNonneg
  have hsumPos : 0 < arms.sum p := by
    rw [hpMin.1.2]
    norm_num
  rcases (Finset.sum_pos_iff_of_nonneg hpMin.1.1).mp hsumPos with
    ⟨j, hj, hpj⟩
  have hij : i ≠ j := by
    intro heq
    subst j
    linarith
  let d : Real := eta * (score i - score j)
  rcases exists_transfer_strictly_improves_half_objective (p j) d hpj with
    ⟨t, ht, htj, himprove⟩
  have hshiftSimplex :
      FTRL.finiteSimplex arms (simplexPairShift p i j t) :=
    finiteSimplex_simplexPairShift_of_eq_zero_of_le
      arms p i j t hij hpMin.1 hi hj hpi ht.le htj.le
  have hlinear := linearLoss_simplexPairShift_eq
    arms p score i j t hi hj
  have hsqrt := sum_sqrt_simplexPairShift_eq_of_eq_zero
    arms p i j t hij hi hj hpi
  have hdecrease :
      FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real)) score
          (simplexPairShift p i j t) <
        FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real)) score p := by
    rw [regularizedObjective_half_eq, regularizedObjective_half_eq,
      hlinear, hsqrt]
    dsimp [d] at himprove
    nlinarith
  exact (not_lt_of_ge (hpMin.2 _ hshiftSimplex)) hdecrease

/-- A half-Tsallis simplex minimizer automatically supplies the interior
stationarity certificate used by the one-step stability route. -/
theorem exists_halfTsallisInteriorStationary_of_isRegularizedMinimizer_auto
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) (score p : Action -> Real)
    (hpMin : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p) :
    exists multiplier,
      HalfTsallisInteriorStationary arms eta score p multiplier :=
  exists_halfTsallisInteriorStationary_of_isRegularizedMinimizer
    arms eta score p hpMin (isRegularizedMinimizer_pos arms eta score p hpMin)

/--
Sampling-law half-Tsallis stability directly from current and chosen-update
minimizer certificates.  Strict positivity and common multipliers are derived
internally.
-/
theorem sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_powerSum_half_of_minimizers
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score prob loss : Action -> Real)
    (next : Action -> Action -> Real)
    (heta : 0 < eta)
    (hprobMin : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score prob)
    (hnextMin : forall chosen, chosen ∈ arms ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real))
        (fun action => score action +
          Exp3.importanceWeightedLoss prob loss chosen action)
        (next chosen))
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    arms.sum (fun chosen =>
        prob chosen *
          (FTRL.linearLoss arms prob
              (Exp3.importanceWeightedLoss prob loss chosen) -
            FTRL.linearLoss arms (next chosen)
              (Exp3.importanceWeightedLoss prob loss chosen))) <=
      2 * eta * powerSum arms (1 / 2 : Real) prob := by
  exact
    sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_powerSum_half_of_positive_minimizers
      arms eta score prob loss next heta hprobMin
      (isRegularizedMinimizer_pos arms eta score prob hprobMin)
      hnextMin
      (fun chosen hchosen =>
        isRegularizedMinimizer_pos arms eta
          (fun action => score action +
            Exp3.importanceWeightedLoss prob loss chosen action)
          (next chosen) (hnextMin chosen hchosen))
      hloss

end Tsallis
end BanditRLProof
