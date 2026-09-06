import BanditRLProof.TsallisFTRLMinimizerUniqueness
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Ultrafilter

/-!
# Measurability of the canonical half-Tsallis minimizer

The project minimizer is chosen noncomputably on the ambient action space, but
the objective only sees the explicit finite arm set.  We restrict the selected
minimizer to that finite subtype and prove continuity in the restricted score
vector.  Compactness supplies cluster points and strict convexity identifies
every cluster point with the unique minimizer.
-/

namespace BanditRLProof
namespace Tsallis

open Filter

universe u

/-- The canonical project minimizer, restricted to the explicit finite arm
subtype and parameterized by a score vector on that subtype. -/
noncomputable def restrictedHalfTsallisMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score : ↥arms -> Real) : ↥arms -> Real :=
  Finset.restrict arms
    (halfTsallisMinimizer arms harms eta (extendFiniteWeights arms score))

theorem restrictedHalfTsallisMinimizer_mem_stdSimplex
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score : ↥arms -> Real) :
    restrictedHalfTsallisMinimizer arms harms eta score ∈
      stdSimplex Real ↥arms := by
  exact restrict_mem_stdSimplex_of_finiteSimplex arms
    (halfTsallisMinimizer_isRegularizedMinimizer arms harms eta
      (extendFiniteWeights arms score)).1

theorem restrictedHalfTsallisMinimizer_isMinOn
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (score : ↥arms -> Real) :
    IsMinOn
      (fun weights : ↥arms -> Real =>
        FTRL.regularizedObjective arms.attach eta
          (negEntropyRegularizer arms.attach (1 / 2 : Real)) score weights)
      (stdSimplex Real ↥arms)
      (restrictedHalfTsallisMinimizer arms harms eta score) := by
  intro weights hweights
  have hcandidate : FTRL.finiteSimplex arms
      (extendFiniteWeights arms weights) :=
    finiteSimplex_extendFiniteWeights arms hweights
  have h := (halfTsallisMinimizer_isRegularizedMinimizer arms harms eta
    (extendFiniteWeights arms score)).2
      (extendFiniteWeights arms weights) hcandidate
  rw [← regularizedObjective_half_restrict_eq arms eta
      (extendFiniteWeights arms score)
      (halfTsallisMinimizer arms harms eta (extendFiniteWeights arms score)),
    regularizedObjective_half_extendFiniteWeights_eq arms eta
      (extendFiniteWeights arms score) weights] at h
  simpa [restrictedHalfTsallisMinimizer, extendFiniteWeights] using h

/-- The restricted half-Tsallis objective is jointly continuous in the finite
score vector and simplex vector. -/
theorem continuous_regularizedObjective_half_restricted_joint
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real) :
    Continuous (fun pair : (↥arms -> Real) × (↥arms -> Real) =>
      FTRL.regularizedObjective arms.attach eta
        (negEntropyRegularizer arms.attach (1 / 2 : Real)) pair.1 pair.2) := by
  rw [Finset.attach_eq_univ]
  simp_rw [regularizedObjective_half_eq, FTRL.linearLoss]
  fun_prop

set_option maxHeartbeats 1000000 in
/-- The finite-coordinate canonical half-Tsallis minimizer is continuous in
the finite score vector. -/
theorem continuous_restrictedHalfTsallisMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real) :
    Continuous (restrictedHalfTsallisMinimizer arms harms eta) := by
  letI : Nonempty ↥arms := ⟨⟨harms.choose, harms.choose_spec⟩⟩
  rw [continuous_iff_continuousAt]
  intro score
  let objective : (↥arms -> Real) -> (↥arms -> Real) -> Real :=
    fun parameter weights =>
      FTRL.regularizedObjective arms.attach eta
        (negEntropyRegularizer arms.attach (1 / 2 : Real)) parameter weights
  apply (isCompact_stdSimplex Real ↥arms).tendsto_nhds_of_unique_mapClusterPt
  · exact Filter.Eventually.of_forall fun parameter =>
      restrictedHalfTsallisMinimizer_mem_stdSimplex
        arms harms eta parameter
  · intro weights hweights hcluster
    have hweightsMin : IsMinOn (objective score)
        (stdSimplex Real ↥arms) weights := by
      rw [mapClusterPt_iff_ultrafilter] at hcluster
      obtain ⟨ultra, hultraScore, hultraWeights⟩ := hcluster
      have hscore : Tendsto id (↑ultra) (nhds score) := by
        simpa only [Filter.map_id] using hultraScore
      have hpair : Tendsto
          (fun parameter =>
            (parameter,
              restrictedHalfTsallisMinimizer arms harms eta parameter))
          (↑ultra)
          (nhds (score, weights)) :=
        hscore.prodMk_nhds hultraWeights
      intro candidate hcandidate
      have hleft : Tendsto
          (fun parameter => objective parameter
            (restrictedHalfTsallisMinimizer arms harms eta parameter))
          (↑ultra) (nhds (objective score weights)) := by
        exact (continuous_regularizedObjective_half_restricted_joint
          arms eta).continuousAt.tendsto.comp hpair
      have hright : Tendsto
          (fun parameter => objective parameter candidate)
          (↑ultra) (nhds (objective score candidate)) := by
        have hcontinuous : Continuous
            (fun parameter => objective parameter candidate) := by
          exact (continuous_regularizedObjective_half_restricted_joint
            arms eta).comp (continuous_id.prodMk continuous_const)
        exact hcontinuous.continuousAt.tendsto.comp hscore
      exact le_of_tendsto_of_tendsto' hleft hright fun parameter =>
        restrictedHalfTsallisMinimizer_isMinOn
          arms harms eta parameter hcandidate
    have hstrict : StrictConvexOn Real (stdSimplex Real ↥arms)
        (objective score) := by
      dsimp [objective]
      rw [Finset.attach_eq_univ]
      exact strictConvexOn_regularizedObjective_half_stdSimplex
        (Action := ↥arms) eta score
    exact hstrict.eq_of_isMinOn hweightsMin
      (restrictedHalfTsallisMinimizer_isMinOn arms harms eta score)
      hweights
      (restrictedHalfTsallisMinimizer_mem_stdSimplex arms harms eta score)

/-- Changing score coordinates outside the explicit arm set does not change
the canonical half-Tsallis minimizer on supported coordinates. -/
theorem halfTsallisMinimizer_eq_on_arms_of_score_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (score₁ score₂ : Action -> Real)
    (hscore : forall action, action ∈ arms ->
      score₁ action = score₂ action) :
    forall action, action ∈ arms ->
      halfTsallisMinimizer arms harms eta score₁ action =
        halfTsallisMinimizer arms harms eta score₂ action := by
  have hobjective : forall weights : Action -> Real,
      FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real)) score₁ weights =
        FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real)) score₂ weights := by
    intro weights
    unfold FTRL.regularizedObjective FTRL.linearLoss
    congr 2
    apply Finset.sum_congr rfl
    intro action haction
    rw [hscore action haction]
  have hsecond : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score₁
      (halfTsallisMinimizer arms harms eta score₂) := by
    refine ⟨(halfTsallisMinimizer_isRegularizedMinimizer
      arms harms eta score₂).1, ?_⟩
    intro weights hweights
    rw [hobjective, hobjective]
    exact (halfTsallisMinimizer_isRegularizedMinimizer
      arms harms eta score₂).2 weights hweights
  exact isRegularizedMinimizer_half_eq_on_arms arms harms eta score₁
    (halfTsallisMinimizer arms harms eta score₁)
    (halfTsallisMinimizer arms harms eta score₂)
    (halfTsallisMinimizer_isRegularizedMinimizer arms harms eta score₁)
    hsecond

theorem restrictedHalfTsallisMinimizer_restrict_score_apply
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (score : Action -> Real) (action : ↥arms) :
    restrictedHalfTsallisMinimizer arms harms eta
        (Finset.restrict arms score) action =
      halfTsallisMinimizer arms harms eta score action := by
  unfold restrictedHalfTsallisMinimizer
  exact halfTsallisMinimizer_eq_on_arms_of_score_eq
    arms harms eta (extendFiniteWeights arms (Finset.restrict arms score)) score
    (fun candidate hcandidate => by
      simp [extendFiniteWeights, Finset.restrict, hcandidate])
    action action.2

/-- Coordinatewise measurability of supported scores implies coordinatewise
measurability of the existing canonical project minimizer. -/
theorem measurable_halfTsallisMinimizer_comp
    {Omega : Type*} {Action : Type u}
    [MeasurableSpace Omega] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (score : Omega -> Action -> Real)
    (hscore : forall action, action ∈ arms ->
      Measurable (fun omega => score omega action))
    (action : Action) (haction : action ∈ arms) :
    Measurable (fun omega =>
      halfTsallisMinimizer arms harms eta (score omega) action) := by
  let restrictedScore : Omega -> ↥arms -> Real := fun omega candidate =>
    score omega candidate
  have hrestrictedScore : Measurable restrictedScore :=
    measurable_pi_lambda _ fun candidate => hscore candidate candidate.2
  have hrestrictedSelector : Measurable (fun omega =>
      restrictedHalfTsallisMinimizer arms harms eta
        (restrictedScore omega)) :=
    (continuous_restrictedHalfTsallisMinimizer arms harms eta).measurable.comp
      hrestrictedScore
  have hcoordinate : Measurable (fun omega =>
      restrictedHalfTsallisMinimizer arms harms eta
        (restrictedScore omega) ⟨action, haction⟩) :=
    (measurable_pi_apply
      (X := fun _candidate : ↥arms => Real) ⟨action, haction⟩).comp
        hrestrictedSelector
  rw [← show (fun omega =>
      restrictedHalfTsallisMinimizer arms harms eta
        (restrictedScore omega) ⟨action, haction⟩) =
      (fun omega =>
        halfTsallisMinimizer arms harms eta (score omega) action) by
    funext omega
    exact restrictedHalfTsallisMinimizer_restrict_score_apply
      arms harms eta (score omega) ⟨action, haction⟩]
  exact hcoordinate

end Tsallis
end BanditRLProof
