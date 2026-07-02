import Mathlib.Probability.Kernel.Basic

/-!
# Posterior kernel surface

This module records the narrow `POSTERIOR-KERNEL` leaf: a posterior over
environments, indexed by the observed history, is represented as a Mathlib
Markov kernel from histories to environments.  It deliberately does not prove a
Bayes formula, a regular-conditional-distribution existence theorem, Thompson
probability matching, or Bayesian regret.
-/

open MeasureTheory

universe u v

namespace BanditRLProof
namespace PosteriorKernel

/--
A posterior distribution over environments indexed by observed histories.

The underlying object is Mathlib's `ProbabilityTheory.Kernel`; the local
wrapper gives Thompson-sampling and Bayesian-regret leaves a stable project
name for the regularity contract.
-/
structure MarkovPosteriorKernel
    (History : Type u) (Env : Type v)
    [MeasurableSpace History] [MeasurableSpace Env] where
  kernel : ProbabilityTheory.Kernel History Env
  isMarkovKernel : ProbabilityTheory.IsMarkovKernel kernel

variable {History : Type u} {Env : Type v}
    [MeasurableSpace History] [MeasurableSpace Env]

instance instIsMarkovKernel
    (posterior : MarkovPosteriorKernel History Env) :
    ProbabilityTheory.IsMarkovKernel posterior.kernel :=
  posterior.isMarkovKernel

/-- Build the local posterior-kernel contract from an existing Mathlib kernel. -/
def ofKernel
    (kernel : ProbabilityTheory.Kernel History Env)
    (hkernel : ProbabilityTheory.IsMarkovKernel kernel) :
    MarkovPosteriorKernel History Env where
  kernel := kernel
  isMarkovKernel := hkernel

/-- Build a posterior kernel from a measurable posterior-measure selector. -/
def ofMeasureSelector
    (posterior : History -> Measure Env)
    (hposterior : Measurable posterior)
    (hprob : forall history, IsProbabilityMeasure (posterior history)) :
    MarkovPosteriorKernel History Env where
  kernel := ProbabilityTheory.Kernel.mk posterior hposterior
  isMarkovKernel := ⟨hprob⟩

@[simp]
theorem ofMeasureSelector_apply
    (posterior : History -> Measure Env)
    (hposterior : Measurable posterior)
    (hprob : forall history, IsProbabilityMeasure (posterior history))
    (history : History) :
    (ofMeasureSelector posterior hposterior hprob).kernel history =
      posterior history := rfl

/--
Build a posterior kernel on a countable/discrete history space.

Finite histories in the bandit development are typically countable/discrete,
so Mathlib's `Kernel.ofFunOfCountable` can turn any probability-valued
posterior selector into a Markov kernel without a separate measurability proof.
-/
def ofCountableHistorySelector
    [Countable History] [MeasurableSingletonClass History]
    (posterior : History -> Measure Env)
    (hprob : forall history, IsProbabilityMeasure (posterior history)) :
    MarkovPosteriorKernel History Env where
  kernel := ProbabilityTheory.Kernel.ofFunOfCountable posterior
  isMarkovKernel := ⟨hprob⟩

@[simp]
theorem ofCountableHistorySelector_apply
    [Countable History] [MeasurableSingletonClass History]
    (posterior : History -> Measure Env)
    (hprob : forall history, IsProbabilityMeasure (posterior history))
    (history : History) :
    (ofCountableHistorySelector posterior hprob).kernel history =
      posterior history := rfl

/-- The posterior kernel is measurable as a map from histories to measures. -/
theorem measurable_kernel
    (posterior : MarkovPosteriorKernel History Env) :
    Measurable posterior.kernel :=
  posterior.kernel.measurable

/-- A measurable random history selects a measurable random posterior measure. -/
theorem measurable_apply_of_measurable_history
    {Omega : Type u} [MeasurableSpace Omega]
    (posterior : MarkovPosteriorKernel History Env)
    (history : Omega -> History)
    (hhistory : Measurable history) :
    Measurable (fun omega : Omega => posterior.kernel (history omega)) :=
  posterior.kernel.measurable.comp hhistory

/--
For every measurable environment event, the posterior event probability is a
measurable scalar function of a measurable random history.
-/
theorem measurable_eventProbability_of_measurable_history
    {Omega : Type u} [MeasurableSpace Omega]
    (posterior : MarkovPosteriorKernel History Env)
    (history : Omega -> History)
    (hhistory : Measurable history)
    {event : Set Env}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega => posterior.kernel (history omega) event) :=
  (ProbabilityTheory.Kernel.measurable_coe posterior.kernel hevent).comp
    hhistory

/-- Every measure selected by a posterior kernel is a probability measure. -/
theorem isProbabilityMeasure_apply
    (posterior : MarkovPosteriorKernel History Env)
    (history : History) :
    IsProbabilityMeasure (posterior.kernel history) := by
  haveI : ProbabilityTheory.IsMarkovKernel posterior.kernel :=
    posterior.isMarkovKernel
  infer_instance

@[simp]
theorem apply_univ
    (posterior : MarkovPosteriorKernel History Env)
    (history : History) :
    posterior.kernel history Set.univ = 1 := by
  haveI : IsProbabilityMeasure (posterior.kernel history) :=
    isProbabilityMeasure_apply posterior history
  simp

/--
Minimal prior/likelihood/posterior package.

This records the Bayesian objects that future Thompson-sampling leaves need to
name.  It does not assert that `posterior` satisfies Bayes' rule for `prior`
and `likelihood`.
-/
structure BayesianPosteriorSurface
    (Env : Type u) (History : Type v)
    [MeasurableSpace Env] [MeasurableSpace History] where
  prior : Measure Env
  likelihood : ProbabilityTheory.Kernel Env History
  posterior : MarkovPosteriorKernel History Env
  prior_isProbability : IsProbabilityMeasure prior
  likelihood_isMarkovKernel : ProbabilityTheory.IsMarkovKernel likelihood

namespace BayesianPosteriorSurface

variable {Env' : Type u} {History' : Type v}
    [MeasurableSpace Env'] [MeasurableSpace History']

instance instPriorIsProbability
    (surface : BayesianPosteriorSurface Env' History') :
    IsProbabilityMeasure surface.prior :=
  surface.prior_isProbability

instance instLikelihoodIsMarkovKernel
    (surface : BayesianPosteriorSurface Env' History') :
    ProbabilityTheory.IsMarkovKernel surface.likelihood :=
  surface.likelihood_isMarkovKernel

theorem posterior_isProbabilityMeasure_apply
    (surface : BayesianPosteriorSurface Env' History')
    (history : History') :
    IsProbabilityMeasure (surface.posterior.kernel history) :=
  isProbabilityMeasure_apply surface.posterior history

end BayesianPosteriorSurface

end PosteriorKernel
end BanditRLProof
