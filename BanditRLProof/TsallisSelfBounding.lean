import BanditRLProof.TsallisFTRLEstimatedEnvironmentRegret
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Self-bounding interfaces for the half-Tsallis route

This module records the paper-facing `(Delta, C, T)` self-bounding condition,
identifies it on the generated predictable trajectory under an exact gap law,
and proves the finite completion-of-squares conversion used after a refined
suboptimal-arm stability bound is available.

The currently compiled half-power stability endpoint contains the optimal-arm
term.  The final counterexample below records why that endpoint cannot be fed
directly into the gap conversion.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Unit mass at one action, used as the fixed optimal-arm comparator. -/
def pointMass {Action : Type u} [DecidableEq Action]
    (best : Action) : Action -> Real :=
  fun action => if action = best then 1 else 0

theorem finiteSimplex_pointMass
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms) :
    FTRL.finiteSimplex arms (pointMass best) := by
  constructor
  · intro action _haction
    by_cases h : action = best <;> simp [pointMass, h]
  · simp [pointMass, hbest]

theorem linearLoss_pointMass
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms)
    (loss : Action -> Real) :
    FTRL.linearLoss arms (pointMass best) loss = loss best := by
  unfold FTRL.linearLoss pointMass
  simp [hbest]

/-- One-round regret against a point mass is the probability-weighted gap. -/
theorem linearLoss_sub_pointMass_eq_gapMass
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms)
    (prob loss gap : Action -> Real)
    (hprob : FTRL.finiteSimplex arms prob)
    (hgap : ∀ action ∈ arms, loss action - loss best = gap action) :
    FTRL.linearLoss arms prob loss -
        FTRL.linearLoss arms (pointMass best) loss =
      arms.sum (fun action => prob action * gap action) := by
  rw [linearLoss_pointMass arms hbest loss]
  have hconstant :
      arms.sum (fun action => prob action * loss best) = loss best := by
    rw [← Finset.sum_mul, hprob.2, one_mul]
  calc
    FTRL.linearLoss arms prob loss - loss best =
        arms.sum (fun action => prob action * loss action) -
          arms.sum (fun action => prob action * loss best) := by
      rw [hconstant]
      rfl
    _ = arms.sum (fun action =>
        prob action * loss action - prob action * loss best) := by
      rw [Finset.sum_sub_distrib]
    _ = arms.sum (fun action => prob action * gap action) := by
      apply Finset.sum_congr rfl
      intro action haction
      rw [← hgap action haction]
      ring

/-- Gap mass accumulated by the generated actual-time sampling laws. -/
noncomputable def sampledHalfTsallisPredictableGapMass
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (gap : Action -> Real) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    arms.sum (fun action =>
      sampledHalfTsallisProbabilityAtTime
        arms harms eta t sample action * gap action))

/-- Paper-facing scalar form of a `(Delta, C, T)` self-bounding constraint. -/
def HasSelfBoundingRegret
    (expectedGapMass regret corruption : Real) : Prop :=
  expectedGapMass - corruption ≤ regret

/-- A predictable fixed-gap law identifies environment regret pathwise. -/
theorem sampledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_gapMass
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (gap : Action -> Real)
    (horizon : Nat)
    (hgap : ∀ t sample action, action ∈ arms ->
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best = gap action)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon sample =
      sampledHalfTsallisPredictableGapMass
        arms harms eta gap horizon sample := by
  unfold sampledHalfTsallisPredictableEnvironmentRegret
    sampledHalfTsallisPredictableGapMass
  apply Finset.sum_congr rfl
  intro t _ht
  exact linearLoss_sub_pointMass_eq_gapMass
    arms hbest
    (sampledHalfTsallisProbabilityAtTime arms harms eta t sample)
    (Exp3.predictableLossAt loss t sample) gap
    (finiteSimplex_sampledHalfTsallisProbabilityAtTime
      arms harms eta t sample)
    (hgap t sample)

/-- The fixed-gap predictable environment satisfies the integrated
self-bounding condition, with any nonnegative corruption allowance. -/
theorem integral_sampledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (gap : Action -> Real)
    (horizon : Nat)
    (hgap : ∀ t sample action, action ∈ arms ->
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best = gap action)
    (corruption : Real) (hcorruption : 0 ≤ corruption) :
    let selector := canonicalHalfTsallisFiniteHistorySelectorMeasurability
      arms harms eta
    let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector loss.environment
    HasSelfBoundingRegret
      (integral mu (sampledHalfTsallisPredictableGapMass
        arms harms eta gap horizon))
      (integral mu (sampledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon))
      corruption := by
  dsimp only
  unfold HasSelfBoundingRegret
  have heq :
      integral
          (prior ⊗ₘ sampledHalfTsallisTrajectoryKernel arms harms eta
            (canonicalHalfTsallisFiniteHistorySelectorMeasurability
              arms harms eta) loss.environment)
          (sampledHalfTsallisPredictableGapMass
            arms harms eta gap horizon) =
        integral
          (prior ⊗ₘ sampledHalfTsallisTrajectoryKernel arms harms eta
            (canonicalHalfTsallisFiniteHistorySelectorMeasurability
              arms harms eta) loss.environment)
          (sampledHalfTsallisPredictableEnvironmentRegret
            arms harms eta loss (pointMass best) horizon) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun sample =>
      (sampledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_gapMass
        arms harms eta loss hbest gap horizon hgap sample).symm)
  linarith

/-- Actual generated environment-regret upper bound specialized to the
optimal-arm point-mass comparator. -/
theorem integral_sampledHalfTsallisPredictableEnvironmentRegret_pointMass_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (heta : 0 < eta)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat) :
    let selector := canonicalHalfTsallisFiniteHistorySelectorMeasurability
      arms harms eta
    let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector loss.environment
    integral mu (sampledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) <=
      2 * eta * powerSum arms (1 / 2 : Real)
          (initialHalfTsallisDistribution arms harms eta) +
        integral mu (fun sample => (Finset.range horizon).sum (fun n =>
          sampledHalfTsallisHalfPowerBoundAt (Env := Env)
            arms harms eta n (sampledHalfTsallisHistoryAt n sample))) +
        ((powerSum arms (1 / 2 : Real)
              (initialHalfTsallisDistribution arms harms eta) -
            powerSum arms (1 / 2 : Real) (pointMass best)) /
          (1 - (1 / 2 : Real))) / eta := by
  exact integral_sampledHalfTsallisPredictableEnvironmentRegret_le
    prior arms harms eta heta loss (pointMass best)
      (finiteSimplex_pointMass arms hbest) horizon

/-- Coordinate completion of squares used by the self-bounding conversion. -/
theorem two_mul_coeff_mul_sqrt_sub_gap_mul_le_sq_div_gap
    (coeff probability gap : Real) (hprobability : 0 ≤ probability)
    (hgap : 0 < gap) :
    2 * coeff * Real.sqrt probability - gap * probability ≤
      coeff ^ 2 / gap := by
  apply (le_div_iff₀ hgap).2
  have hsqrtSq := Real.sq_sqrt hprobability
  have hsq := sq_nonneg (coeff - gap * Real.sqrt probability)
  calc
    (2 * coeff * Real.sqrt probability - gap * probability) * gap =
        2 * coeff * Real.sqrt probability * gap - gap ^ 2 * probability := by
      ring
    _ = 2 * coeff * Real.sqrt probability * gap -
        gap ^ 2 * (Real.sqrt probability) ^ 2 := by
      rw [hsqrtSq]
    _ = coeff ^ 2 - (coeff - gap * Real.sqrt probability) ^ 2 := by
      ring
    _ <= coeff ^ 2 := sub_le_self _ hsq

/-- Finite `(Delta, C, T)` self-bounding conversion after a refined upper
bound has removed every zero-gap coordinate. -/
theorem regret_le_two_mul_base_add_sum_sq_div_gap_add_corruption
    {Index : Type u} (indices : Finset Index)
    (probability coeff gap : Index -> Real)
    (regret base corruption : Real)
    (hprobability : ∀ index ∈ indices, 0 ≤ probability index)
    (hgap : ∀ index ∈ indices, 0 < gap index)
    (hselfBounding :
      indices.sum (fun index => gap index * probability index) -
          corruption ≤ regret)
    (hupper :
      regret ≤ base + indices.sum (fun index =>
        coeff index * Real.sqrt (probability index))) :
    regret ≤
      2 * base + indices.sum (fun index => coeff index ^ 2 / gap index) +
        corruption := by
  have hcombine :
      regret ≤
        2 * (base + indices.sum (fun index =>
          coeff index * Real.sqrt (probability index))) -
        indices.sum (fun index => gap index * probability index) +
        corruption := by
    linarith
  have hcoordinates :
      indices.sum (fun index =>
          2 * coeff index * Real.sqrt (probability index) -
            gap index * probability index) ≤
        indices.sum (fun index => coeff index ^ 2 / gap index) := by
    apply Finset.sum_le_sum
    intro index hindex
    exact two_mul_coeff_mul_sqrt_sub_gap_mul_le_sq_div_gap
      (coeff index) (probability index) (gap index)
      (hprobability index hindex) (hgap index hindex)
  have hrewrite :
      2 * (base + indices.sum (fun index =>
          coeff index * Real.sqrt (probability index))) -
          indices.sum (fun index => gap index * probability index) +
          corruption =
        2 * base + indices.sum (fun index =>
          2 * coeff index * Real.sqrt (probability index) -
            gap index * probability index) + corruption := by
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  rw [hrewrite] at hcombine
  linarith

theorem powerSum_pointMass_half
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms) :
    powerSum arms (1 / 2 : Real) (pointMass best) = 1 := by
  unfold powerSum pointMass
  simp [hbest]

theorem sum_erase_sqrt_pointMass
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (best : Action) :
    (arms.erase best).sum (fun action =>
      Real.sqrt (pointMass best action)) = 0 := by
  apply Finset.sum_eq_zero
  intro action haction
  have hne : action ≠ best := (Finset.mem_erase.mp haction).1
  simp [pointMass, hne]

/-- The existing total half-power budget cannot uniformly be replaced by a
suboptimal-arm square-root budget.  A refined `(1-p)` factor is genuinely
needed before the self-bounding conversion can consume the trajectory bound. -/
theorem not_forall_powerSum_half_le_sum_erase_sqrt
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms) :
    ¬ ∀ p : Action -> Real, FTRL.finiteSimplex arms p ->
      powerSum arms (1 / 2 : Real) p ≤
        (arms.erase best).sum (fun action => Real.sqrt (p action)) := by
  intro h
  have hbad := h (pointMass best) (finiteSimplex_pointMass arms hbest)
  rw [powerSum_pointMass_half arms hbest,
    sum_erase_sqrt_pointMass arms best] at hbad
  norm_num at hbad

end Tsallis
end BanditRLProof
