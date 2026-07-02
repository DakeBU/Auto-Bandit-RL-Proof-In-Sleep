import Mathlib.MeasureTheory.Integral.Bochner.Basic
import BanditRLProof.IntegrabilitySums

/-!
# Bochner expectation over finite sums

Thin Mathlib-backed wrappers for finite-sum linearity of the Bochner integral.
These are the expectation-level companion to `IntegrabilitySums`: each summand
must be integrable, and then the integral of the finite sum is the finite sum
of the integrals.
-/

namespace BanditRLProof
namespace ExpectationBochnerSums

open MeasureTheory

universe u v w

/--
The Bochner integral distributes over a finite sum of integrable terms.

This is the `EXP-FINITE-SUM` import wrapper.  It is polymorphic in the
Bochner codomain; bandit expected-regret applications typically instantiate
`E := Real`.
-/
theorem integral_finset_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v}
    {E : Type w} [NormedAddCommGroup E] [NormedSpace Real E]
    (mu : Measure Omega)
    (s : Finset Idx)
    (f : Idx -> Omega -> E)
    (hf : forall i, i ∈ s -> Integrable (f i) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega => s.sum (fun i => f i omega)) =
    s.sum (fun i => MeasureTheory.integral mu (f i)) := by
  simpa only [Finset.sum_apply] using
    (MeasureTheory.integral_finset_sum
      (μ := mu)
      (s := s)
      (f := f)
      hf)

/--
Finite-type specialization of `integral_finset_sum`.

The statement exposes the common finite-arm `(Finset.univ : Finset Idx)`
shape used by regret decompositions.
-/
theorem integral_univ_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace Real E]
    (mu : Measure Omega)
    (f : Idx -> Omega -> E)
    (hf : forall i : Idx, Integrable (f i) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (Finset.univ : Finset Idx).sum (fun i => f i omega)) =
    (Finset.univ : Finset Idx).sum
      (fun i => MeasureTheory.integral mu (f i)) := by
  exact
    integral_finset_sum
      (mu := mu)
      (s := (Finset.univ : Finset Idx))
      (f := f)
      (hf := fun i _hi => hf i)

end ExpectationBochnerSums
end BanditRLProof
