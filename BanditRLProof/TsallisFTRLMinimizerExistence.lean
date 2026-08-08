import BanditRLProof.TsallisFTRLInteriority
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact

/-!
# Existence of half-Tsallis finite-simplex minimizers

The project simplex only constrains coordinates in an explicit `Finset`, so it
is not compact as a subset of the full function space when the ambient action
type is infinite.  We minimize instead on Mathlib's compact standard simplex
over the finite subtype `↥arms`, then extend the minimizer by zero.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- Extend finite-subtype weights by zero outside the explicit arm set. -/
def extendFiniteWeights {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : ↥arms -> Real) : Action -> Real :=
  fun action => if haction : action ∈ arms then p ⟨action, haction⟩ else 0

@[simp]
theorem extendFiniteWeights_apply_of_mem
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : ↥arms -> Real)
    {action : Action} (haction : action ∈ arms) :
    extendFiniteWeights arms p action = p ⟨action, haction⟩ := by
  simp [extendFiniteWeights, haction]

@[simp]
theorem extendFiniteWeights_apply_of_not_mem
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : ↥arms -> Real)
    {action : Action} (haction : action ∉ arms) :
    extendFiniteWeights arms p action = 0 := by
  simp [extendFiniteWeights, haction]

theorem sum_extendFiniteWeights
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : ↥arms -> Real) :
    arms.sum (extendFiniteWeights arms p) = ∑ action : ↥arms, p action := by
  rw [← arms.sum_attach]
  simp [extendFiniteWeights]

theorem finiteSimplex_extendFiniteWeights
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {p : ↥arms -> Real}
    (hp : p ∈ stdSimplex Real ↥arms) :
    FTRL.finiteSimplex arms (extendFiniteWeights arms p) := by
  constructor
  · intro action haction
    rw [extendFiniteWeights_apply_of_mem arms p haction]
    exact hp.1 ⟨action, haction⟩
  · rw [sum_extendFiniteWeights arms p, hp.2]

theorem restrict_mem_stdSimplex_of_finiteSimplex
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {p : Action -> Real}
    (hp : FTRL.finiteSimplex arms p) :
    Finset.restrict arms p ∈ stdSimplex Real ↥arms := by
  constructor
  · intro action
    exact hp.1 action action.2
  · change (∑ action : ↥arms, p action) = 1
    rw [← Finset.attach_eq_univ, Finset.sum_attach]
    exact hp.2

theorem linearLoss_extendFiniteWeights_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : ↥arms -> Real) (score : Action -> Real) :
    FTRL.linearLoss arms (extendFiniteWeights arms p) score =
      FTRL.linearLoss Finset.univ p (fun action => score action) := by
  unfold FTRL.linearLoss
  rw [← arms.sum_attach]
  simp [extendFiniteWeights]

theorem linearLoss_restrict_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p score : Action -> Real) :
    FTRL.linearLoss Finset.univ (Finset.restrict arms p)
        (fun action => score action) =
      FTRL.linearLoss arms p score := by
  unfold FTRL.linearLoss
  rw [← arms.sum_attach]
  simp [Finset.restrict]

theorem sum_sqrt_extendFiniteWeights_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : ↥arms -> Real) :
    arms.sum (fun action => Real.sqrt (extendFiniteWeights arms p action)) =
      ∑ action : ↥arms, Real.sqrt (p action) := by
  rw [← arms.sum_attach]
  simp [extendFiniteWeights]

theorem sum_sqrt_restrict_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (p : Action -> Real) :
    (Finset.univ : Finset ↥arms).sum
        (fun action => Real.sqrt (Finset.restrict arms p action)) =
      arms.sum (fun action => Real.sqrt (p action)) := by
  rw [← arms.sum_attach]
  simp [Finset.restrict]

theorem regularizedObjective_half_extendFiniteWeights_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score : Action -> Real) (p : ↥arms -> Real) :
    FTRL.regularizedObjective arms eta
        (negEntropyRegularizer arms (1 / 2 : Real)) score
        (extendFiniteWeights arms p) =
      FTRL.regularizedObjective arms.attach eta
        (negEntropyRegularizer arms.attach (1 / 2 : Real))
        (fun action : ↥arms => score action) p := by
  rw [Finset.attach_eq_univ]
  rw [regularizedObjective_half_eq, regularizedObjective_half_eq,
    linearLoss_extendFiniteWeights_eq, sum_sqrt_extendFiniteWeights_eq]

theorem regularizedObjective_half_restrict_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score p : Action -> Real) :
    FTRL.regularizedObjective arms.attach eta
        (negEntropyRegularizer arms.attach (1 / 2 : Real))
        (fun action : ↥arms => score action) (Finset.restrict arms p) =
      FTRL.regularizedObjective arms eta
        (negEntropyRegularizer arms (1 / 2 : Real)) score p := by
  rw [Finset.attach_eq_univ]
  rw [regularizedObjective_half_eq, regularizedObjective_half_eq,
    linearLoss_restrict_eq, sum_sqrt_restrict_eq]

/-- The half-Tsallis objective is continuous on the finite subtype function
space. -/
theorem continuous_regularizedObjective_half_univ
    {Action : Type u} [Fintype Action]
    (eta : Real) (score : Action -> Real) :
    Continuous (fun p : Action -> Real =>
      FTRL.regularizedObjective Finset.univ eta
        (negEntropyRegularizer Finset.univ (1 / 2 : Real)) score p) := by
  simp_rw [regularizedObjective_half_eq, FTRL.linearLoss]
  fun_prop

/-- Every nonempty explicit finite arm set admits a half-Tsallis regularized
minimizer.  The learning rate and finite score coordinates may be arbitrary
real numbers. -/
theorem exists_isRegularizedMinimizer_half
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score : Action -> Real) :
    exists p,
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p := by
  let restrictedScore : ↥arms -> Real := fun action => score action
  let objective : (↥arms -> Real) -> Real := fun p =>
    FTRL.regularizedObjective arms.attach eta
      (negEntropyRegularizer arms.attach (1 / 2 : Real))
      restrictedScore p
  have hsimplexNonempty : (stdSimplex Real ↥arms).Nonempty := by
    let anchor : ↥arms := ⟨harms.choose, harms.choose_spec⟩
    exact ⟨Pi.single anchor 1, single_mem_stdSimplex Real anchor⟩
  have hcontinuous : Continuous objective := by
    dsimp [objective, restrictedScore]
    exact continuous_regularizedObjective_half_univ eta
      (fun action : ↥arms => score action)
  obtain ⟨p, hpSimplex, hpMin⟩ :=
    (isCompact_stdSimplex Real ↥arms).exists_isMinOn
      hsimplexNonempty hcontinuous.continuousOn
  refine ⟨extendFiniteWeights arms p,
    finiteSimplex_extendFiniteWeights arms hpSimplex, ?_⟩
  intro q hq
  have hqSimplex : Finset.restrict arms q ∈ stdSimplex Real ↥arms :=
    restrict_mem_stdSimplex_of_finiteSimplex arms hq
  have hmin := hpMin hqSimplex
  dsimp [objective, restrictedScore] at hmin
  rw [← regularizedObjective_half_extendFiniteWeights_eq arms eta score p,
    regularizedObjective_half_restrict_eq arms eta score q] at hmin
  exact hmin

/-- A fixed choice of half-Tsallis minimizer on a nonempty explicit arm set. -/
noncomputable def halfTsallisMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score : Action -> Real) : Action -> Real :=
  Classical.choose (exists_isRegularizedMinimizer_half arms harms eta score)

theorem halfTsallisMinimizer_isRegularizedMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score : Action -> Real) :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score
      (halfTsallisMinimizer arms harms eta score) :=
  Classical.choose_spec (exists_isRegularizedMinimizer_half arms harms eta score)

/-- Canonical half-Tsallis update after observing one importance-weighted loss. -/
noncomputable def halfTsallisUpdatedMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score loss : Action -> Real) (chosen : Action) :
    Action -> Real :=
  let prob := halfTsallisMinimizer arms harms eta score
  halfTsallisMinimizer arms harms eta (fun action =>
    score action + Exp3.importanceWeightedLoss prob loss chosen action)

theorem halfTsallisUpdatedMinimizer_isRegularizedMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score loss : Action -> Real) (chosen : Action) :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real))
      (fun action => score action +
        Exp3.importanceWeightedLoss
          (halfTsallisMinimizer arms harms eta score) loss chosen action)
      (halfTsallisUpdatedMinimizer arms harms eta score loss chosen) := by
  exact halfTsallisMinimizer_isRegularizedMinimizer arms harms eta
    (fun action => score action +
      Exp3.importanceWeightedLoss
        (halfTsallisMinimizer arms harms eta score) loss chosen action)

/-- The sampling-law one-step stability endpoint with both current and updated
minimizers selected internally. -/
theorem sum_halfTsallisMinimizer_mul_linearLoss_sub_updated_le_powerSum_half
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score loss : Action -> Real)
    (heta : 0 < eta)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    let prob := halfTsallisMinimizer arms harms eta score
    let next := fun chosen =>
      halfTsallisUpdatedMinimizer arms harms eta score loss chosen
    arms.sum (fun chosen =>
        prob chosen *
          (FTRL.linearLoss arms prob
              (Exp3.importanceWeightedLoss prob loss chosen) -
            FTRL.linearLoss arms (next chosen)
              (Exp3.importanceWeightedLoss prob loss chosen))) <=
      2 * eta * powerSum arms (1 / 2 : Real) prob := by
  dsimp only
  exact
    sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_powerSum_half_of_minimizers
      arms eta score (halfTsallisMinimizer arms harms eta score) loss
      (fun chosen =>
        halfTsallisUpdatedMinimizer arms harms eta score loss chosen)
      heta
      (halfTsallisMinimizer_isRegularizedMinimizer arms harms eta score)
      (fun chosen _ =>
        halfTsallisUpdatedMinimizer_isRegularizedMinimizer
          arms harms eta score loss chosen)
      hloss

/-- A nonempty finite arm set admits a strictly positive half-Tsallis
minimizer together with its common stationarity multiplier. -/
theorem exists_halfTsallisInteriorStationary_minimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score : Action -> Real) :
    exists p multiplier,
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
          arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p ∧
        (forall action, action ∈ arms -> 0 < p action) ∧
        HalfTsallisInteriorStationary arms eta score p multiplier := by
  obtain ⟨p, hpMin⟩ := exists_isRegularizedMinimizer_half arms harms eta score
  obtain ⟨multiplier, hstationary⟩ :=
    exists_halfTsallisInteriorStationary_of_isRegularizedMinimizer_auto
      arms eta score p hpMin
  exact ⟨p, multiplier, hpMin,
    isRegularizedMinimizer_pos arms eta score p hpMin, hstationary⟩

end Tsallis
end BanditRLProof
