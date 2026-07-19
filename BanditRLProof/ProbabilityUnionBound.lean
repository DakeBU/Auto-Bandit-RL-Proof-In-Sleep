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
Equal-share finite-union bound.

Every event receives confidence budget `delta / s.card`; nonemptiness of the
index set lets the finite sum normalize back to `delta`.  As with
`measure_biUnion_finset_le`, no event measurability or probability-measure
assumption is required.
-/
theorem measure_biUnion_finset_le_of_uniform
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v} [DecidableEq Idx]
    (mu : Measure Omega)
    (s : Finset Idx) (hs : s.Nonempty)
    (delta : Real)
    (E : Idx -> Set Omega)
    (hE : forall i, i ∈ s ->
      mu (E i) <= ENNReal.ofReal (delta / (s.card : Real))) :
    mu (⋃ i ∈ s, E i) <= ENNReal.ofReal delta := by
  have hcardNat : 0 < s.card := Finset.card_pos.mpr hs
  have hcardReal : 0 < (s.card : Real) := Nat.cast_pos.mpr hcardNat
  have hcardENN_ne_zero : (s.card : ENNReal) ≠ 0 := by
    simp [Finset.card_ne_zero.mpr hs]
  have hcardENN_ne_top : (s.card : ENNReal) ≠ ⊤ := by simp
  calc
    mu (⋃ i ∈ s, E i) <= s.sum (fun i => mu (E i)) :=
      measure_biUnion_finset_le mu s E
    _ <= s.sum (fun _i =>
        ENNReal.ofReal (delta / (s.card : Real))) := by
      exact Finset.sum_le_sum fun i hi => hE i hi
    _ = (s.card : ENNReal) *
        ENNReal.ofReal (delta / (s.card : Real)) := by
      simp [nsmul_eq_mul]
    _ = ENNReal.ofReal delta := by
      rw [ENNReal.ofReal_div_of_pos hcardReal]
      simp only [ENNReal.ofReal_natCast]
      exact ENNReal.mul_div_cancel hcardENN_ne_zero hcardENN_ne_top

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
