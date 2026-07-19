import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Posterior

/-!
# Posterior kernel surface

This module records the narrow `POSTERIOR-KERNEL` leaf: a posterior over
environments, indexed by the observed history, is represented as a Mathlib
Markov kernel from histories to environments.  It deliberately does not prove a
Bayes formula, a regular-conditional-distribution existence theorem, Thompson
probability matching, or Bayesian regret.
-/

open MeasureTheory
open scoped ProbabilityTheory

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

/-!
## Canonical Bayesian posterior

Mathlib's `ProbabilityTheory.posterior likelihood prior` is the posterior
kernel characterized by the swapped joint-law identity.  The declarations
below expose that object through the local posterior contract and identify it
with `condDistrib` on any source whose environment/history pair law is the
Bayesian composition product.
-/

/-- The Mathlib posterior of a likelihood kernel under a prior measure. -/
noncomputable def canonicalPosterior
    [StandardBorelSpace Env] [Nonempty Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood] :
    MarkovPosteriorKernel History Env :=
  ofKernel (ProbabilityTheory.posterior likelihood prior) inferInstance

@[simp]
theorem canonicalPosterior_kernel
    [StandardBorelSpace Env] [Nonempty Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood] :
    (canonicalPosterior prior likelihood).kernel =
      ProbabilityTheory.posterior likelihood prior := rfl

/-- The canonical joint law generated by a prior followed by a likelihood. -/
noncomputable def canonicalJointMeasure
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood] :
    Measure (Env × History) :=
  prior ⊗ₘ likelihood

instance instCanonicalJointMeasureIsProbabilityMeasure
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood] :
    IsProbabilityMeasure (canonicalJointMeasure prior likelihood) := by
  rw [canonicalJointMeasure]
  infer_instance

/--
Identify the canonical posterior on any source with the prescribed Bayesian
environment/history pair law.

The proof uses the defining composition-product identity for Mathlib's
`posterior`.  Thus the posterior conditional-law equality is produced from a
joint-law transport, rather than assumed as a separate Bayes-law field.
-/
theorem canonicalPosterior_kernel_ae_eq_condDistrib_of_pair_map_eq
    {Omega : Type*} [MeasurableSpace Omega]
    [StandardBorelSpace Env] [Nonempty Env]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (henv : Measurable env) (hhistory : Measurable history)
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (hpair :
      mu.map (fun omega => (env omega, history omega)) =
        canonicalJointMeasure prior likelihood) :
    (canonicalPosterior prior likelihood).kernel =ᵐ[mu.map history]
      ProbabilityTheory.condDistrib env history mu := by
  have hpairMeas : Measurable (fun omega => (env omega, history omega)) :=
    henv.prodMk hhistory
  have hhistoryLaw :
      mu.map history = likelihood ∘ₘ prior := by
    calc
      mu.map history =
          (mu.map (fun omega => (env omega, history omega))).map Prod.snd := by
            rw [Measure.map_map measurable_snd hpairMeas]
            rfl
      _ = (canonicalJointMeasure prior likelihood).map Prod.snd :=
        congrArg (fun nu : Measure (Env × History) => nu.map Prod.snd) hpair
      _ = likelihood ∘ₘ prior := by
        change (prior ⊗ₘ likelihood).snd = likelihood ∘ₘ prior
        rw [Measure.snd_compProd]
  have hswappedJoint :
      mu.map (fun omega => (history omega, env omega)) =
        mu.map history ⊗ₘ (canonicalPosterior prior likelihood).kernel := by
    calc
      mu.map (fun omega => (history omega, env omega)) =
          (mu.map (fun omega => (env omega, history omega))).map Prod.swap := by
            rw [Measure.map_map measurable_swap hpairMeas]
            rfl
      _ = (canonicalJointMeasure prior likelihood).map Prod.swap :=
        congrArg (fun nu : Measure (Env × History) => nu.map Prod.swap) hpair
      _ = (likelihood ∘ₘ prior) ⊗ₘ
          (canonicalPosterior prior likelihood).kernel := by
        exact ProbabilityTheory.compProd_posterior_eq_map_swap.symm
      _ = mu.map history ⊗ₘ
          (canonicalPosterior prior likelihood).kernel := by
        rw [hhistoryLaw]
  exact ((ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
    (μ := mu) history henv.aemeasurable
    (canonicalPosterior prior likelihood).kernel).2 hswappedJoint).symm

/--
On the canonical Bayesian product space itself, the Mathlib posterior is the
conditional distribution of the environment coordinate given the history
coordinate.
-/
theorem canonicalPosterior_kernel_ae_eq_condDistrib_fst_snd
    [StandardBorelSpace Env] [Nonempty Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood] :
    (canonicalPosterior prior likelihood).kernel =ᵐ[
        (canonicalJointMeasure prior likelihood).map Prod.snd]
      ProbabilityTheory.condDistrib Prod.fst Prod.snd
        (canonicalJointMeasure prior likelihood) := by
  apply canonicalPosterior_kernel_ae_eq_condDistrib_of_pair_map_eq
    (canonicalJointMeasure prior likelihood) Prod.fst Prod.snd
    measurable_fst measurable_snd prior likelihood
  simp [canonicalJointMeasure]

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
