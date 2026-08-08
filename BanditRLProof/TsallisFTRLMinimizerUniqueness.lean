import BanditRLProof.TsallisFTRLMinimizerExistence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Uniqueness of half-Tsallis finite-simplex minimizers

The square-root sum is strictly concave on a nonempty standard simplex, so the
half-Tsallis regularized objective is strictly convex there.  The project-level
finite simplex leaves coordinates outside `arms` unconstrained; accordingly,
the public uniqueness theorem identifies exactly the supported coordinates.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- The finite sum of square roots is strictly concave on every nonempty
standard simplex. -/
theorem strictConcaveOn_sum_sqrt_stdSimplex
    {Action : Type u} [Fintype Action] [Nonempty Action] :
    StrictConcaveOn Real (stdSimplex Real Action)
      (fun p : Action -> Real =>
        (Finset.univ : Finset Action).sum (fun action => Real.sqrt (p action))) := by
  classical
  refine ⟨convex_stdSimplex Real Action, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  have hne : exists action, p action ≠ q action := by
    by_contra hnot
    push Not at hnot
    exact hpq (funext hnot)
  obtain ⟨different, hdifferent⟩ := hne
  have hcoordLe : forall action,
      a • Real.sqrt (p action) + b • Real.sqrt (q action) <=
        Real.sqrt ((a • p + b • q) action) := by
    intro action
    simpa only [Pi.add_apply, Pi.smul_apply] using
      Real.strictConcaveOn_sqrt.concaveOn.2
        (hp.1 action) (hq.1 action) ha.le hb.le hab
  have hcoordLt :
      a • Real.sqrt (p different) + b • Real.sqrt (q different) <
        Real.sqrt ((a • p + b • q) different) := by
    simpa only [Pi.add_apply, Pi.smul_apply] using
      Real.strictConcaveOn_sqrt.2
        (hp.1 different) (hq.1 different) hdifferent ha hb hab
  have hsum := Finset.sum_lt_sum
    (fun action _haction => hcoordLe action)
    ⟨different, Finset.mem_univ different, hcoordLt⟩
  simpa only [Finset.sum_add_distrib, Finset.smul_sum] using hsum

/-- On a nonempty finite standard simplex, the half-Tsallis regularized
objective is strictly convex in the probability vector. -/
theorem strictConvexOn_regularizedObjective_half_stdSimplex
    {Action : Type u} [Fintype Action] [Nonempty Action]
    (eta : Real) (score : Action -> Real) :
    StrictConvexOn Real (stdSimplex Real Action)
      (fun p => FTRL.regularizedObjective Finset.univ eta
        (negEntropyRegularizer Finset.univ (1 / 2 : Real)) score p) := by
  classical
  refine ⟨convex_stdSimplex Real Action, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  have hsqrt :=
    (strictConcaveOn_sum_sqrt_stdSimplex (Action := Action)).2
      hp hq hpq ha hb hab
  simp only [smul_eq_mul] at hsqrt
  have hlinear :
      FTRL.linearLoss Finset.univ (a • p + b • q) score =
        a * FTRL.linearLoss Finset.univ p score +
          b * FTRL.linearLoss Finset.univ q score := by
    unfold FTRL.linearLoss
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
    rw [Finset.sum_add_distrib]
    calc
      (∑ action, a * p action * score action) +
          ∑ action, b * q action * score action =
        (∑ action, a * (p action * score action)) +
          ∑ action, b * (q action * score action) := by
            congr 1 <;> apply Finset.sum_congr rfl <;> intro action _ <;> ring
      _ = a * (∑ action, p action * score action) +
          b * ∑ action, q action * score action := by
            rw [Finset.mul_sum, Finset.mul_sum]
  change
    FTRL.regularizedObjective Finset.univ eta
        (negEntropyRegularizer Finset.univ (1 / 2 : Real)) score
        (a • p + b • q) <
      a • FTRL.regularizedObjective Finset.univ eta
          (negEntropyRegularizer Finset.univ (1 / 2 : Real)) score p +
        b • FTRL.regularizedObjective Finset.univ eta
          (negEntropyRegularizer Finset.univ (1 / 2 : Real)) score q
  simp only [regularizedObjective_half_eq, hlinear, smul_eq_mul]
  nlinarith

/-- Two half-Tsallis minimizers have identical coordinates on the explicit arm
set.  Coordinates outside `arms` are intentionally not constrained by the
project finite-simplex predicate or objective. -/
theorem isRegularizedMinimizer_half_eq_on_arms
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score p q : Action -> Real)
    (hp : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p)
    (hq : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score q) :
    forall action, action ∈ arms -> p action = q action := by
  letI : Nonempty ↥arms := ⟨⟨harms.choose, harms.choose_spec⟩⟩
  let objective : (↥arms -> Real) -> Real := fun weights =>
    FTRL.regularizedObjective arms.attach eta
      (negEntropyRegularizer arms.attach (1 / 2 : Real))
      (fun action : ↥arms => score action) weights
  have hpMem : Finset.restrict arms p ∈ stdSimplex Real ↥arms :=
    restrict_mem_stdSimplex_of_finiteSimplex arms hp.1
  have hqMem : Finset.restrict arms q ∈ stdSimplex Real ↥arms :=
    restrict_mem_stdSimplex_of_finiteSimplex arms hq.1
  have hpMin : IsMinOn objective (stdSimplex Real ↥arms)
      (Finset.restrict arms p) := by
    intro weights hweights
    have hcandidate : FTRL.finiteSimplex arms
        (extendFiniteWeights arms weights) :=
      finiteSimplex_extendFiniteWeights arms hweights
    have h := hp.2 (extendFiniteWeights arms weights) hcandidate
    rw [← regularizedObjective_half_restrict_eq arms eta score p,
      regularizedObjective_half_extendFiniteWeights_eq arms eta score weights] at h
    exact h
  have hqMin : IsMinOn objective (stdSimplex Real ↥arms)
      (Finset.restrict arms q) := by
    intro weights hweights
    have hcandidate : FTRL.finiteSimplex arms
        (extendFiniteWeights arms weights) :=
      finiteSimplex_extendFiniteWeights arms hweights
    have h := hq.2 (extendFiniteWeights arms weights) hcandidate
    rw [← regularizedObjective_half_restrict_eq arms eta score q,
      regularizedObjective_half_extendFiniteWeights_eq arms eta score weights] at h
    exact h
  have hstrict : StrictConvexOn Real (stdSimplex Real ↥arms) objective := by
    dsimp [objective]
    rw [Finset.attach_eq_univ]
    exact strictConvexOn_regularizedObjective_half_stdSimplex
      (Action := ↥arms) eta (fun action : ↥arms => score action)
  have heq : Finset.restrict arms p = Finset.restrict arms q :=
    hstrict.eq_of_isMinOn hpMin hqMin hpMem hqMem
  intro action haction
  exact congrFun heq ⟨action, haction⟩

/-- The canonical selected minimizer agrees on every supported coordinate with
any other half-Tsallis minimizer certificate. -/
theorem halfTsallisMinimizer_eq_on_arms
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score p : Action -> Real)
    (hp : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p) :
    forall action, action ∈ arms ->
      halfTsallisMinimizer arms harms eta score action = p action := by
  exact isRegularizedMinimizer_half_eq_on_arms arms harms eta score
    (halfTsallisMinimizer arms harms eta score) p
    (halfTsallisMinimizer_isRegularizedMinimizer arms harms eta score) hp

end Tsallis
end BanditRLProof
