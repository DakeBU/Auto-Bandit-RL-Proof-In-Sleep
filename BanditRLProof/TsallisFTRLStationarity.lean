import BanditRLProof.TsallisFTRLOneStepStability
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Half-Tsallis FTRL minimizer and stationarity transport

This module connects the finite-simplex minimizer certificate used by the
generic FTRL route to the explicit interior stationarity certificate consumed
by the half-Tsallis one-step stability theorem.  The proof perturbs two simplex
coordinates in opposite directions, differentiates the resulting scalar
objective at an interior minimizer, and uses the vanishing derivative to
identify a common multiplier.

Strict positivity is an explicit input.  This module does not prove existence
or interiority of a half-Tsallis minimizer and does not construct the stochastic
Tsallis-INF update.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- The zero-sum direction that transfers mass from `j` to `i`. -/
def pairDirection {Action : Type u} [DecidableEq Action]
    (i j : Action) (a : Action) : Real :=
  (if a = i then 1 else 0) - (if a = j then 1 else 0)

/-- Transfer scalar mass `t` from coordinate `j` to coordinate `i`. -/
def simplexPairShift {Action : Type u} [DecidableEq Action]
    (p : Action -> Real) (i j : Action) (t : Real) : Action -> Real :=
  fun a => p a + t * pairDirection i j a

@[simp]
theorem simplexPairShift_zero {Action : Type u} [DecidableEq Action]
    (p : Action -> Real) (i j : Action) :
    simplexPairShift p i j 0 = p := by
  funext a
  simp [simplexPairShift]

theorem sum_pairDirection_mul {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (i j : Action) (f : Action -> Real)
    (hi : i ∈ arms) (hj : j ∈ arms) :
    arms.sum (fun a => pairDirection i j a * f a) = f i - f j := by
  simp only [pairDirection, sub_mul, Finset.sum_sub_distrib]
  simp [hi, hj]

theorem sum_simplexPairShift {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : Action -> Real) (i j : Action) (t : Real)
    (hi : i ∈ arms) (hj : j ∈ arms) :
    arms.sum (simplexPairShift p i j t) = arms.sum p := by
  have hdir := sum_pairDirection_mul arms i j (fun _ => (1 : Real)) hi hj
  simp only [mul_one, sub_self] at hdir
  simp only [simplexPairShift, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hdir]
  ring

theorem finiteSimplex_simplexPairShift_of_abs_lt_min
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : Action -> Real) (i j : Action) (t : Real)
    (hij : i ≠ j) (hp : FTRL.finiteSimplex arms p)
    (hi : i ∈ arms) (hj : j ∈ arms)
    (ht : |t| < min (p i) (p j)) :
    FTRL.finiteSimplex arms (simplexPairShift p i j t) := by
  constructor
  · intro a ha
    rcases abs_lt.mp (ht.trans_le (min_le_left _ _)) with ⟨htLower, htUpper⟩
    rcases abs_lt.mp (ht.trans_le (min_le_right _ _)) with ⟨htLower', htUpper'⟩
    by_cases hai : a = i
    · subst a
      simp [simplexPairShift, pairDirection, hij]
      linarith
    · by_cases haj : a = j
      · subst a
        simp [simplexPairShift, pairDirection, hai]
        linarith
      · simp [simplexPairShift, pairDirection, hai, haj, hp.1 a ha]
  · rw [sum_simplexPairShift arms p i j t hi hj, hp.2]

/-- The half-Tsallis objective is a linear term minus twice the square-root sum. -/
theorem regularizedObjective_half_eq {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score p : Action -> Real) :
    FTRL.regularizedObjective arms eta
        (negEntropyRegularizer arms (1 / 2 : Real)) score p =
      eta * FTRL.linearLoss arms p score -
        2 * arms.sum (fun a => Real.sqrt (p a)) + 2 := by
  simp [FTRL.regularizedObjective, negEntropyRegularizer, entropy, powerSum,
    Real.sqrt_eq_rpow]
  ring

theorem hasDerivAt_simplexPairShift {Action : Type u} [DecidableEq Action]
    (p : Action -> Real) (i j a : Action) :
    HasDerivAt (fun t => simplexPairShift p i j t a)
      (pairDirection i j a) 0 := by
  convert
    (hasDerivAt_const (x := (0 : Real)) (p a)).add
      ((hasDerivAt_id (0 : Real)).mul_const (pairDirection i j a)) using 1
  ring

theorem hasDerivAt_linearLoss_simplexPairShift
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p score : Action -> Real) (i j : Action)
    (hi : i ∈ arms) (hj : j ∈ arms) :
    HasDerivAt
      (fun t => FTRL.linearLoss arms (simplexPairShift p i j t) score)
      (score i - score j) 0 := by
  have hsum :
      HasDerivAt
        (fun t => arms.sum (fun a => simplexPairShift p i j t a * score a))
        (arms.sum (fun a => pairDirection i j a * score a)) 0 :=
    HasDerivAt.fun_sum (fun a _ =>
      (hasDerivAt_simplexPairShift p i j a).mul_const (score a))
  rw [sum_pairDirection_mul arms i j score hi hj] at hsum
  simpa [FTRL.linearLoss] using hsum

theorem sum_pairDirection_div_two_sqrt
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : Action -> Real) (i j : Action)
    (hi : i ∈ arms) (hj : j ∈ arms) :
    arms.sum (fun a => pairDirection i j a / (2 * Real.sqrt (p a))) =
      1 / (2 * Real.sqrt (p i)) - 1 / (2 * Real.sqrt (p j)) := by
  simp only [pairDirection, sub_div, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp
    · intro a _ hai
      simp [hai]
    · exact fun hnot => (hnot hi).elim
  · rw [Finset.sum_eq_single j]
    · simp
    · intro a _ haj
      simp [haj]
    · exact fun hnot => (hnot hj).elim

theorem hasDerivAt_sum_sqrt_simplexPairShift
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : Action -> Real) (i j : Action)
    (hi : i ∈ arms) (hj : j ∈ arms)
    (hpPos : forall a, a ∈ arms -> 0 < p a) :
    HasDerivAt
      (fun t => arms.sum (fun a => Real.sqrt (simplexPairShift p i j t a)))
      (1 / (2 * Real.sqrt (p i)) - 1 / (2 * Real.sqrt (p j))) 0 := by
  have hsum :
      HasDerivAt
        (fun t => arms.sum (fun a => Real.sqrt (simplexPairShift p i j t a)))
        (arms.sum (fun a => pairDirection i j a / (2 * Real.sqrt (p a)))) 0 :=
    HasDerivAt.fun_sum (fun a ha => by
      simpa using (hasDerivAt_simplexPairShift p i j a).sqrt
        (ne_of_gt (by simpa [simplexPairShift] using hpPos a ha)))
  rw [sum_pairDirection_div_two_sqrt arms p i j hi hj] at hsum
  exact hsum

theorem hasDerivAt_regularizedObjective_half_simplexPairShift
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) (score p : Action -> Real)
    (i j : Action) (hi : i ∈ arms) (hj : j ∈ arms)
    (hpPos : forall a, a ∈ arms -> 0 < p a) :
    HasDerivAt
      (fun t => FTRL.regularizedObjective arms eta
        (negEntropyRegularizer arms (1 / 2 : Real)) score
        (simplexPairShift p i j t))
      (eta * (score i - score j) -
        (1 / Real.sqrt (p i) - 1 / Real.sqrt (p j))) 0 := by
  have hlinear :=
    (hasDerivAt_linearLoss_simplexPairShift arms p score i j hi hj).const_mul eta
  have hsqrt :=
    (hasDerivAt_sum_sqrt_simplexPairShift arms p i j hi hj hpPos).const_mul 2
  have htotal := (hlinear.sub hsqrt).const_add 2
  have hfun :
      (fun t => FTRL.regularizedObjective arms eta
        (negEntropyRegularizer arms (1 / 2 : Real)) score
        (simplexPairShift p i j t)) =
      (fun t => eta * FTRL.linearLoss arms (simplexPairShift p i j t) score -
        2 * arms.sum (fun a => Real.sqrt (simplexPairShift p i j t a)) + 2) := by
    funext t
    exact regularizedObjective_half_eq arms eta score
      (simplexPairShift p i j t)
  rw [hfun]
  convert htotal using 1
  · funext t
    simp only [Pi.sub_apply]
    ring
  · ring

theorem isLocalMin_regularizedObjective_half_simplexPairShift
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) (score p : Action -> Real)
    (i j : Action) (hij : i ≠ j)
    (hi : i ∈ arms) (hj : j ∈ arms)
    (hpMin : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p)
    (hpPos : forall a, a ∈ arms -> 0 < p a) :
    IsLocalMin
      (fun t => FTRL.regularizedObjective arms eta
        (negEntropyRegularizer arms (1 / 2 : Real)) score
        (simplexPairShift p i j t)) 0 := by
  have hdelta : 0 < min (p i) (p j) :=
    lt_min (hpPos i hi) (hpPos j hj)
  show ∀ᶠ t in nhds 0,
    FTRL.regularizedObjective arms eta
        (negEntropyRegularizer arms (1 / 2 : Real)) score
        (simplexPairShift p i j 0) <=
      FTRL.regularizedObjective arms eta
        (negEntropyRegularizer arms (1 / 2 : Real)) score
        (simplexPairShift p i j t)
  filter_upwards [Metric.ball_mem_nhds (0 : Real) hdelta] with t ht
  have htAbs : |t| < min (p i) (p j) := by
    simpa [Real.dist_eq] using ht
  have hshift := finiteSimplex_simplexPairShift_of_abs_lt_min
    arms p i j t hij hpMin.1 hi hj htAbs
  simpa [simplexPairShift] using hpMin.2 (simplexPairShift p i j t) hshift

theorem halfTsallis_pairwise_stationary_of_isRegularizedMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) (score p : Action -> Real)
    (hpMin : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p)
    (hpPos : forall a, a ∈ arms -> 0 < p a)
    {i j : Action} (hi : i ∈ arms) (hj : j ∈ arms) :
    eta * score i - (p i) ^ (-(1 / 2 : Real)) =
      eta * score j - (p j) ^ (-(1 / 2 : Real)) := by
  by_cases hij : i = j
  · subst j
    rfl
  have hlocal := isLocalMin_regularizedObjective_half_simplexPairShift
    arms eta score p i j hij hi hj hpMin hpPos
  have hderiv := hasDerivAt_regularizedObjective_half_simplexPairShift
    arms eta score p i j hi hj hpPos
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  have hrpowI :
      (p i) ^ (-(1 / 2 : Real)) = 1 / Real.sqrt (p i) := by
    rw [Real.rpow_neg (hpPos i hi).le, ← Real.sqrt_eq_rpow]
    simp [one_div]
  have hrpowJ :
      (p j) ^ (-(1 / 2 : Real)) = 1 / Real.sqrt (p j) := by
    rw [Real.rpow_neg (hpPos j hj).le, ← Real.sqrt_eq_rpow]
    simp [one_div]
  rw [hrpowI, hrpowJ]
  linarith

/--
An explicitly interior half-Tsallis simplex minimizer admits the stationarity
certificate consumed by the one-step stability theorem.
-/
theorem exists_halfTsallisInteriorStationary_of_isRegularizedMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) (score p : Action -> Real)
    (hpMin : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p)
    (hpPos : forall a, a ∈ arms -> 0 < p a) :
    exists multiplier,
      HalfTsallisInteriorStationary arms eta score p multiplier := by
  have harms : arms.Nonempty := by
    by_contra hnot
    have hempty : arms = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty] at hpMin
    simp [FTRL.IsRegularizedMinimizer, FTRL.finiteSimplex] at hpMin
  rcases harms with ⟨anchor, hanchor⟩
  refine ⟨eta * score anchor - (p anchor) ^ (-(1 / 2 : Real)), ?_⟩
  intro action haction
  exact halfTsallis_pairwise_stationary_of_isRegularizedMinimizer
    arms eta score p hpMin hpPos haction hanchor

/-- The supporting-line inequality for the square root at a positive point. -/
theorem two_mul_sqrt_sub_sqrt_le_sub_div_sqrt
    {p q : Real} (hp : 0 < p) (hq : 0 <= q) :
    2 * (Real.sqrt q - Real.sqrt p) <=
      (q - p) / Real.sqrt p := by
  have hsqrtP : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsqrtQ : 0 <= Real.sqrt q := Real.sqrt_nonneg q
  have hsqrtPSq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp.le
  have hsqrtQSq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  apply (le_div_iff₀ hsqrtP).2
  nlinarith [sq_nonneg (Real.sqrt q - Real.sqrt p)]

/--
A positive simplex point satisfying half-Tsallis stationarity globally minimizes
the corresponding regularized objective on the finite simplex.
-/
theorem isRegularizedMinimizer_of_halfTsallisInteriorStationary
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) (score p : Action -> Real)
    (multiplier : Real)
    (hp : FTRL.finiteSimplex arms p)
    (hpPos : forall a, a ∈ arms -> 0 < p a)
    (hstationary : HalfTsallisInteriorStationary
      arms eta score p multiplier) :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p := by
  refine ⟨hp, ?_⟩
  intro q hq
  have hcoord : forall a, a ∈ arms ->
      multiplier * (q a - p a) <=
        eta * (q a - p a) * score a -
          2 * (Real.sqrt (q a) - Real.sqrt (p a)) := by
    intro a ha
    have htangent := two_mul_sqrt_sub_sqrt_le_sub_div_sqrt
      (hpPos a ha) (hq.1 a ha)
    have hrpow :
        (p a) ^ (-(1 / 2 : Real)) = 1 / Real.sqrt (p a) := by
      rw [Real.rpow_neg (hpPos a ha).le, ← Real.sqrt_eq_rpow]
      simp [one_div]
    have hstat := hstationary a ha
    rw [hrpow] at hstat
    calc
      multiplier * (q a - p a) =
          eta * (q a - p a) * score a -
            (q a - p a) / Real.sqrt (p a) := by
        rw [← hstat]
        ring
      _ <= eta * (q a - p a) * score a -
            2 * (Real.sqrt (q a) - Real.sqrt (p a)) :=
        sub_le_sub_left htangent _
  have hsum := Finset.sum_le_sum hcoord
  have hleft :
      arms.sum (fun a => multiplier * (q a - p a)) = 0 := by
    rw [← Finset.mul_sum]
    simp only [Finset.sum_sub_distrib, hq.2, hp.2, sub_self, mul_zero]
  have hright :
      arms.sum (fun a =>
        eta * (q a - p a) * score a -
          2 * (Real.sqrt (q a) - Real.sqrt (p a))) =
        FTRL.regularizedObjective arms eta
            (negEntropyRegularizer arms (1 / 2 : Real)) score q -
          FTRL.regularizedObjective arms eta
            (negEntropyRegularizer arms (1 / 2 : Real)) score p := by
    rw [regularizedObjective_half_eq, regularizedObjective_half_eq]
    unfold FTRL.linearLoss
    simp only [Finset.sum_sub_distrib]
    have hlinear :
        arms.sum (fun a => eta * (q a - p a) * score a) =
          eta * arms.sum (fun a => q a * score a) -
            eta * arms.sum (fun a => p a * score a) := by
      simp_rw [show forall a,
          eta * (q a - p a) * score a =
            eta * (q a * score a - p a * score a) by
          intro a
          ring]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      ring
    have hsqrt :
        arms.sum (fun a =>
          2 * (Real.sqrt (q a) - Real.sqrt (p a))) =
          2 * arms.sum (fun a => Real.sqrt (q a)) -
            2 * arms.sum (fun a => Real.sqrt (p a)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hlinear, hsqrt]
    ring
  rw [hleft, hright] at hsum
  linarith

/-- Interior half-Tsallis stationarity is equivalent to simplex minimality. -/
theorem isRegularizedMinimizer_iff_exists_halfTsallisInteriorStationary
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) (score p : Action -> Real)
    (hp : FTRL.finiteSimplex arms p)
    (hpPos : forall a, a ∈ arms -> 0 < p a) :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p ↔
      exists multiplier,
        HalfTsallisInteriorStationary arms eta score p multiplier := by
  constructor
  · intro hpMin
    exact exists_halfTsallisInteriorStationary_of_isRegularizedMinimizer
      arms eta score p hpMin hpPos
  · rintro ⟨multiplier, hstationary⟩
    exact isRegularizedMinimizer_of_halfTsallisInteriorStationary
      arms eta score p multiplier hp hpPos hstationary

/--
Sampling-law half-Tsallis stability directly from concrete regularized-minimizer
certificates.  Common multipliers are constructed internally from interiority.
-/
theorem sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_powerSum_half_of_positive_minimizers
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score prob loss : Action -> Real)
    (next : Action -> Action -> Real)
    (heta : 0 < eta)
    (hprobMin : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score prob)
    (hprobPos : forall action, action ∈ arms -> 0 < prob action)
    (hnextMin : forall chosen, chosen ∈ arms ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real))
        (fun action => score action +
          Exp3.importanceWeightedLoss prob loss chosen action)
        (next chosen))
    (hnextPos : forall chosen, chosen ∈ arms ->
      forall action, action ∈ arms -> 0 < next chosen action)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    arms.sum (fun chosen =>
        prob chosen *
          (FTRL.linearLoss arms prob
              (Exp3.importanceWeightedLoss prob loss chosen) -
            FTRL.linearLoss arms (next chosen)
              (Exp3.importanceWeightedLoss prob loss chosen))) <=
      2 * eta * powerSum arms (1 / 2 : Real) prob := by
  classical
  rcases exists_halfTsallisInteriorStationary_of_isRegularizedMinimizer
    arms eta score prob hprobMin hprobPos with
    ⟨multiplier, hprobStationary⟩
  have hnextExists : forall chosen, chosen ∈ arms ->
      exists nextMultiplier,
        HalfTsallisInteriorStationary arms eta
          (fun action => score action +
            Exp3.importanceWeightedLoss prob loss chosen action)
          (next chosen) nextMultiplier := by
    intro chosen hchosen
    exact exists_halfTsallisInteriorStationary_of_isRegularizedMinimizer
      arms eta
      (fun action => score action +
        Exp3.importanceWeightedLoss prob loss chosen action)
      (next chosen) (hnextMin chosen hchosen) (hnextPos chosen hchosen)
  let nextMultiplier : Action -> Real := fun chosen =>
    if hchosen : chosen ∈ arms then
      Classical.choose (hnextExists chosen hchosen)
    else 0
  have hnextStationary : forall chosen, chosen ∈ arms ->
      HalfTsallisInteriorStationary arms eta
        (fun action => score action +
          Exp3.importanceWeightedLoss prob loss chosen action)
        (next chosen) (nextMultiplier chosen) := by
    intro chosen hchosen
    simp only [nextMultiplier, dif_pos hchosen]
    exact Classical.choose_spec (hnextExists chosen hchosen)
  exact sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_powerSum_half
    arms eta score prob loss next multiplier nextMultiplier heta
    hprobMin.1 hprobPos (fun chosen hchosen => (hnextMin chosen hchosen).1)
    hnextPos hloss hprobStationary hnextStationary

end Tsallis
end BanditRLProof
