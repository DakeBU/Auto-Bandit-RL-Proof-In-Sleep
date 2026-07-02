import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Finite union probability bounds

Thin Mathlib-backed finite-union wrappers.  These are outer-measure bounds:
no event measurability or probability-measure assumption is required.
-/

namespace BanditRLProof
namespace ProbabilityUnionBound

open MeasureTheory

universe u v

/--
The measure of a finite union of events is bounded by the finite sum of their
measures.

This is an outer-measure wrapper around
`MeasureTheory.measure_biUnion_finset_le`, so it does not require the events to
be measurable and does not require `mu` to be a probability measure.
-/
theorem measure_biUnion_finset_le
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v}
    (mu : Measure Omega)
    (s : Finset Idx)
    (E : Idx -> Set Omega) :
    mu (⋃ i ∈ s, E i) <=
      s.sum (fun i => mu (E i)) := by
  simpa using
    (MeasureTheory.measure_biUnion_finset_le
      (μ := mu)
      (I := s)
      (s := E))

/--
Fintype specialization of the finite-union probability bound.

The index set is `(Finset.univ : Finset Idx)`, matching the finite-arm style
used by the bandit proofs.
-/
theorem measure_iUnion_fintype_le_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    (mu : Measure Omega)
    (E : Idx -> Set Omega) :
    mu (⋃ i, E i) <=
      (Finset.univ : Finset Idx).sum (fun i => mu (E i)) := by
  simpa using
    (MeasureTheory.measure_iUnion_fintype_le
      (μ := mu)
      (s := E))

end ProbabilityUnionBound
end BanditRLProof
