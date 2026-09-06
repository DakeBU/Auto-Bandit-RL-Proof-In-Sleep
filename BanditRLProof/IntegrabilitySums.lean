import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Finite sums of integrable terms

Thin Mathlib-backed wrappers for the reusable integrability fact needed by
finite regret decompositions: a finite sum of integrable terms is integrable.
This module does not state Bochner expectation linearity; that is a separate
leaf.
-/

namespace BanditRLProof
namespace IntegrabilitySums

open MeasureTheory

universe u v w

/--
Finite sums of integrable terms are integrable.

This is the `INT-FINITE-SUM` import wrapper.  It is polymorphic in the
codomain, following Mathlib's `integrable_finset_sum'`; in bandit applications
the codomain is usually `Real`.
-/
theorem integrable_finset_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v}
    {E : Type w} [TopologicalSpace E] [ESeminormedAddCommMonoid E]
    [ContinuousAdd E]
    (mu : Measure Omega)
    (s : Finset Idx)
    (f : Idx -> Omega -> E)
    (hf : forall i, i ∈ s -> Integrable (f i) mu) :
    Integrable (fun omega : Omega => s.sum (fun i => f i omega)) mu := by
  simpa only [Finset.sum_apply] using
    (MeasureTheory.integrable_finset_sum
      (μ := mu)
      (s := s)
      (f := f)
      hf)

/--
Finite-type specialization of `integrable_finset_sum`.

This version exposes the common finite-arm shape with `(Finset.univ :
Finset Idx)`.
-/
theorem integrable_univ_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    {E : Type w} [TopologicalSpace E] [ESeminormedAddCommMonoid E]
    [ContinuousAdd E]
    (mu : Measure Omega)
    (f : Idx -> Omega -> E)
    (hf : forall i : Idx, Integrable (f i) mu) :
    Integrable
      (fun omega : Omega =>
        (Finset.univ : Finset Idx).sum (fun i => f i omega))
      mu := by
  exact
    integrable_finset_sum
      (mu := mu)
      (s := (Finset.univ : Finset Idx))
      (f := f)
      (hf := fun i _hi => hf i)

end IntegrabilitySums
end BanditRLProof
