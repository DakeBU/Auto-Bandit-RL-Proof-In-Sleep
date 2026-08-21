import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Stochastic-gradient-bandit source audit

This module formalizes the finite-action algebra in Algorithm 1 and Equations
(3)--(7) of Baudry--Johnson--Vary--Pike-Burke--Rebeschini (NeurIPS 2025).

The finite weighted sums below are the exact conditional-mean calculations
obtained after fixing a pre-action history.  They are not a construction of
the paper's recursive stochastic history, reward kernel, or learning-rate
regret theorems.  Those trajectory and rate endpoints remain separate open
obligations.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open scoped BigOperators

noncomputable section

variable {Action : Type*} [Fintype Action] [DecidableEq Action]

/-- The denominator in the source softmax rule, Equation (3). -/
def softmaxDenominator (theta : Action -> Real) : Real :=
  ∑ a, Real.exp (theta a)

/-- The source softmax sampling probability, Equation (3). -/
def softmaxProbability (theta : Action -> Real) (a : Action) : Real :=
  Real.exp (theta a) / softmaxDenominator theta

omit [DecidableEq Action] in
theorem softmaxDenominator_pos [Nonempty Action] (theta : Action -> Real) :
    0 < softmaxDenominator theta := by
  classical
  let a : Action := Classical.choice inferInstance
  exact Finset.sum_pos' (fun i _hi => (Real.exp_pos (theta i)).le)
    ⟨a, Finset.mem_univ a, Real.exp_pos (theta a)⟩

omit [DecidableEq Action] in
theorem softmaxProbability_pos [Nonempty Action] (theta : Action -> Real) (a : Action) :
    0 < softmaxProbability theta a := by
  exact div_pos (Real.exp_pos _) (softmaxDenominator_pos theta)

omit [DecidableEq Action] in
theorem softmaxProbability_nonneg [Nonempty Action] (theta : Action -> Real) (a : Action) :
    0 <= softmaxProbability theta a :=
  (softmaxProbability_pos theta a).le

omit [DecidableEq Action] in
/-- Equation (3) defines a normalized finite sampling law. -/
theorem softmaxProbability_sum [Nonempty Action] (theta : Action -> Real) :
    ∑ a, softmaxProbability theta a = 1 := by
  rw [show (∑ a, softmaxProbability theta a) =
      (∑ a, Real.exp (theta a)) / softmaxDenominator theta by
    simp only [softmaxProbability, Finset.sum_div]]
  exact div_self (ne_of_gt (softmaxDenominator_pos theta))

theorem softmaxProbability_le_one [Nonempty Action] (theta : Action -> Real) (a : Action) :
    softmaxProbability theta a <= 1 := by
  have hsum := softmaxProbability_sum theta
  have hrest : 0 <= ∑ b ∈ (Finset.univ : Finset Action).erase a,
      softmaxProbability theta b := by
    exact Finset.sum_nonneg fun b _hb => softmaxProbability_nonneg theta b
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset Action)
    (softmaxProbability theta) (Finset.mem_univ a)
  linarith

/-- Algorithm 1 / Equation (4), before multiplication by the learning rate. -/
def sourceIncrement (p : Action -> Real) (reward : Real)
    (selected k : Action) : Real :=
  if selected = k then (1 - p k) * reward else -(p k * reward)

omit [Fintype Action] in
theorem sourceIncrement_eq_indicator (p : Action -> Real) (reward : Real)
    (selected k : Action) :
    sourceIncrement p reward selected k =
      reward * ((if selected = k then 1 else 0) - p k) := by
  by_cases h : selected = k <;> simp [sourceIncrement, h] <;> ring

/-- Algorithm 1 preserves the zero sum of its parameter vector. -/
theorem sum_sourceIncrement (p : Action -> Real) (reward : Real)
    (selected : Action) (hp : ∑ k, p k = 1) :
    ∑ k, sourceIncrement p reward selected k = 0 := by
  classical
  simp_rw [sourceIncrement_eq_indicator]
  calc
    (∑ k, reward * ((if selected = k then 1 else 0) - p k)) =
        reward * ∑ k, ((if selected = k then 1 else 0) - p k) := by
          rw [Finset.mul_sum]
    _ = reward * ((∑ k, if selected = k then 1 else 0) - ∑ k, p k) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by simp [hp]

/-- The policy value at a fixed pre-action history. -/
def policyValue (p mean : Action -> Real) : Real :=
  ∑ a, p a * mean a

/-- The finite conditional-mean version of the source expected update. -/
def expectedSourceIncrement (p mean : Action -> Real) (k : Action) : Real :=
  ∑ selected, p selected * sourceIncrement p (mean selected) selected k

/-- Equation (5), in policy-gradient-coordinate form. -/
theorem expectedSourceIncrement_eq_gradientCoordinate
    (p mean : Action -> Real) (k : Action) :
    expectedSourceIncrement p mean k =
      p k * (mean k - policyValue p mean) := by
  classical
  simp_rw [expectedSourceIncrement, sourceIncrement_eq_indicator]
  calc
    (∑ selected,
        p selected *
          (mean selected * ((if selected = k then 1 else 0) - p k))) =
        (∑ selected,
          (p selected * mean selected) * (if selected = k then 1 else 0)) -
        ∑ selected, (p selected * mean selected) * p k := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro selected _hselected
          ring
    _ = p k * mean k - policyValue p mean * p k := by
          rw [← Finset.sum_mul]
          simp [policyValue]
    _ = p k * (mean k - policyValue p mean) := by ring

/-- The source instantaneous expected gap `E_t[Delta_{A_t}]`. -/
def instantaneousGap (p gap : Action -> Real) : Real :=
  ∑ a, p a * gap a

omit [DecidableEq Action] in
theorem instantaneousGap_eq_bestMean_sub_policyValue
    (p mean gap : Action -> Real) (bestMean : Real)
    (hp : ∑ a, p a = 1)
    (hgap : ∀ a, gap a = bestMean - mean a) :
    instantaneousGap p gap = bestMean - policyValue p mean := by
  unfold instantaneousGap
  calc
    (∑ a, p a * gap a) = ∑ a, p a * (bestMean - mean a) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [hgap a]
    _ = ∑ a, (bestMean * p a - p a * mean a) := by
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = (∑ a, bestMean * p a) - ∑ a, p a * mean a := by
      rw [Finset.sum_sub_distrib]
    _ = bestMean * (∑ a, p a) - ∑ a, p a * mean a := by
      rw [Finset.mul_sum]
    _ = bestMean - policyValue p mean := by rw [hp]; simp [policyValue]

/-- Equation (5), in instantaneous-gap-coordinate form. -/
theorem expectedSourceIncrement_eq_gapCoordinate
    (p mean gap : Action -> Real) (bestMean : Real) (k : Action)
    (hp : ∑ a, p a = 1)
    (hgap : ∀ a, gap a = bestMean - mean a) :
    expectedSourceIncrement p mean k =
      p k * (instantaneousGap p gap - gap k) := by
  rw [expectedSourceIncrement_eq_gradientCoordinate,
    instantaneousGap_eq_bestMean_sub_policyValue p mean gap bestMean hp hgap,
    hgap k]
  ring

/-- The gap-coordinate update isolated from Equation (5). -/
def gapExpectedIncrement (p gap : Action -> Real) (k : Action) : Real :=
  p k * (instantaneousGap p gap - gap k)

theorem expectedSourceIncrement_eq_gapExpectedIncrement
    (p mean gap : Action -> Real) (bestMean : Real) (k : Action)
    (hp : ∑ a, p a = 1)
    (hgap : ∀ a, gap a = bestMean - mean a) :
    expectedSourceIncrement p mean k = gapExpectedIncrement p gap k := by
  exact expectedSourceIncrement_eq_gapCoordinate p mean gap bestMean k hp hgap

theorem instantaneousGap_ge_minGap_mul_failureMass
    (p gap : Action -> Real) (best : Action) (Delta : Real)
    (hp : ∑ a, p a = 1)
    (hp_nonneg : ∀ a, 0 <= p a)
    (hgap_best : gap best = 0)
    (hgap_min : ∀ a, a ≠ best -> Delta <= gap a) :
    Delta * (1 - p best) <= instantaneousGap p gap := by
  classical
  have hprob_erase :
      ∑ a ∈ (Finset.univ : Finset Action).erase best, p a = 1 - p best := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset Action) p
      (Finset.mem_univ best)
    rw [hp] at hsplit
    linarith
  calc
    Delta * (1 - p best) =
        ∑ a ∈ (Finset.univ : Finset Action).erase best, p a * Delta := by
      rw [← hprob_erase]
      rw [← Finset.sum_mul]
      ring
    _ <= ∑ a ∈ (Finset.univ : Finset Action).erase best, p a * gap a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (hgap_min a (by simpa using ha)) (hp_nonneg a)
    _ = instantaneousGap p gap := by
      rw [instantaneousGap]
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset Action)
        (fun a => p a * gap a) (Finset.mem_univ best)
      calc
        (∑ a ∈ (Finset.univ : Finset Action).erase best, p a * gap a) =
            (∑ a ∈ (Finset.univ : Finset Action).erase best, p a * gap a) +
              p best * gap best := by rw [hgap_best]; ring
        _ = ∑ a, p a * gap a := hsplit

/-- Pointwise Equation (6): the best coordinate gains at least the positive
gap times its success/failure probability product. -/
theorem gapExpectedIncrement_best_ge
    (p gap : Action -> Real) (best : Action) (Delta : Real)
    (hp : ∑ a, p a = 1)
    (hp_nonneg : ∀ a, 0 <= p a)
    (hgap_best : gap best = 0)
    (hgap_min : ∀ a, a ≠ best -> Delta <= gap a) :
    Delta * (p best * (1 - p best)) <=
      gapExpectedIncrement p gap best := by
  rw [gapExpectedIncrement, hgap_best, sub_zero]
  have hinst := instantaneousGap_ge_minGap_mul_failureMass
    p gap best Delta hp hp_nonneg hgap_best hgap_min
  nlinarith [hp_nonneg best]

/-- The finite-horizon best-parameter expectation represented by Equation
(6), after conditioning at each round. -/
def bestParameterIncrementSum (eta : Real) (p : Nat -> Action -> Real)
    (gap : Action -> Real) (best : Action) (horizon : Nat) : Real :=
  eta * ∑ t ∈ Finset.range horizon, gapExpectedIncrement (p t) gap best

/-- Finite-horizon Equation (6). -/
theorem bestParameterIncrementSum_ge
    (eta Delta : Real) (p : Nat -> Action -> Real) (gap : Action -> Real)
    (best : Action) (horizon : Nat)
    (heta : 0 <= eta)
    (hp : ∀ t, ∑ a, p t a = 1)
    (hp_nonneg : ∀ t a, 0 <= p t a)
    (hgap_best : gap best = 0)
    (hgap_min : ∀ a, a ≠ best -> Delta <= gap a) :
    eta * Delta *
        (∑ t ∈ Finset.range horizon, p t best * (1 - p t best)) <=
      bestParameterIncrementSum eta p gap best horizon := by
  unfold bestParameterIncrementSum
  have hsum :
      Delta * (∑ t ∈ Finset.range horizon, p t best * (1 - p t best)) <=
        ∑ t ∈ Finset.range horizon, gapExpectedIncrement (p t) gap best := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _ht
    exact gapExpectedIncrement_best_ge (p t) gap best Delta
      (hp t) (hp_nonneg t) hgap_best hgap_min
  nlinarith

/-- The gap-weighted finite-horizon expected pseudo-regret from Equation (2). -/
def sourceExpectedPseudoRegret (p : Nat -> Action -> Real)
    (gap : Action -> Real) (horizon : Nat) : Real :=
  ∑ t ∈ Finset.range horizon, instantaneousGap (p t) gap

theorem instantaneousGap_le_maxGap_mul_failureMass
    (p gap : Action -> Real) (best : Action) (DeltaMax : Real)
    (hp : ∑ a, p a = 1)
    (hp_nonneg : ∀ a, 0 <= p a)
    (hgap_best : gap best = 0)
    (hgap_max : ∀ a, a ≠ best -> gap a <= DeltaMax) :
    instantaneousGap p gap <= DeltaMax * (1 - p best) := by
  classical
  have hprob_erase :
      ∑ a ∈ (Finset.univ : Finset Action).erase best, p a = 1 - p best := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset Action) p
      (Finset.mem_univ best)
    rw [hp] at hsplit
    linarith
  calc
    instantaneousGap p gap =
        ∑ a ∈ (Finset.univ : Finset Action).erase best, p a * gap a := by
      rw [instantaneousGap]
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset Action)
        (fun a => p a * gap a) (Finset.mem_univ best)
      calc
        (∑ a, p a * gap a) =
            (∑ a ∈ (Finset.univ : Finset Action).erase best, p a * gap a) +
              p best * gap best := hsplit.symm
        _ = ∑ a ∈ (Finset.univ : Finset Action).erase best, p a * gap a := by
          rw [hgap_best]
          ring
    _ <= ∑ a ∈ (Finset.univ : Finset Action).erase best, p a * DeltaMax := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (hgap_max a (by simpa using ha)) (hp_nonneg a)
    _ = DeltaMax * (1 - p best) := by
      rw [← Finset.sum_mul, hprob_erase]
      ring

theorem failureMass_eq_successFailure_add_sq (x : Real) :
    1 - x = x * (1 - x) + (1 - x) ^ 2 := by ring

/-- Equation (7), with its positive learning-rate/minimum-gap denominator and
maximum-gap envelope exposed explicitly. -/
theorem sourceRegretDecomposition_le
    (eta Delta DeltaMax : Real) (p : Nat -> Action -> Real)
    (gap : Action -> Real) (best : Action) (horizon : Nat)
    (heta : 0 < eta) (hDelta : 0 < Delta) (hDeltaMax : 0 <= DeltaMax)
    (hp : ∀ t, ∑ a, p t a = 1)
    (hp_nonneg : ∀ t a, 0 <= p t a)
    (hgap_best : gap best = 0)
    (hgap_min : ∀ a, a ≠ best -> Delta <= gap a)
    (hgap_max : ∀ a, a ≠ best -> gap a <= DeltaMax) :
    sourceExpectedPseudoRegret p gap horizon <=
      (DeltaMax / (eta * Delta)) *
          bestParameterIncrementSum eta p gap best horizon +
        DeltaMax *
          (∑ t ∈ Finset.range horizon, (1 - p t best) ^ 2) := by
  have hregret :
      sourceExpectedPseudoRegret p gap horizon <=
        DeltaMax * (∑ t ∈ Finset.range horizon, (1 - p t best)) := by
    unfold sourceExpectedPseudoRegret
    calc
      (∑ t ∈ Finset.range horizon, instantaneousGap (p t) gap) <=
          ∑ t ∈ Finset.range horizon, DeltaMax * (1 - p t best) := by
        apply Finset.sum_le_sum
        intro t _ht
        exact instantaneousGap_le_maxGap_mul_failureMass
          (p t) gap best DeltaMax (hp t) (hp_nonneg t) hgap_best hgap_max
      _ = DeltaMax * (∑ t ∈ Finset.range horizon, (1 - p t best)) := by
        rw [Finset.mul_sum]
  have hparameter := bestParameterIncrementSum_ge
    eta Delta p gap best horizon heta.le hp hp_nonneg hgap_best hgap_min
  have hproduct : 0 < eta * Delta := mul_pos heta hDelta
  have hsuccessFailure :
      (∑ t ∈ Finset.range horizon, p t best * (1 - p t best)) <=
        bestParameterIncrementSum eta p gap best horizon / (eta * Delta) := by
    rw [le_div_iff₀ hproduct]
    nlinarith
  have hsplit :
      (∑ t ∈ Finset.range horizon, (1 - p t best)) =
        (∑ t ∈ Finset.range horizon, p t best * (1 - p t best)) +
          ∑ t ∈ Finset.range horizon, (1 - p t best) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    exact failureMass_eq_successFailure_add_sq (p t best)
  rw [hsplit] at hregret
  calc
    sourceExpectedPseudoRegret p gap horizon <=
        DeltaMax *
          ((∑ t ∈ Finset.range horizon, p t best * (1 - p t best)) +
            ∑ t ∈ Finset.range horizon, (1 - p t best) ^ 2) := hregret
    _ <= DeltaMax *
          (bestParameterIncrementSum eta p gap best horizon / (eta * Delta) +
            ∑ t ∈ Finset.range horizon, (1 - p t best) ^ 2) := by
      gcongr
    _ = (DeltaMax / (eta * Delta)) *
          bestParameterIncrementSum eta p gap best horizon +
        DeltaMax *
          (∑ t ∈ Finset.range horizon, (1 - p t best) ^ 2) := by
      field_simp

end

end StochasticGradientBandit
end BanditRLProof
