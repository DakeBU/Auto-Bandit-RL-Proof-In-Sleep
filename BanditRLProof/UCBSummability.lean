import BanditRLProof.ProbabilityUnionBound

/-!
# Finite-horizon UCB tail summability wrappers

This file records the finite-union/summation layer used by UCB-style bad
events: once each arm-time event has a tail bound, the bad-event union over
finite arms and a finite horizon is bounded by the corresponding double sum.
-/

namespace BanditRLProof
namespace UCBSummability

open MeasureTheory

universe u v

/-- The union of arm-time bad events over all finite arms and times `< T`. -/
def finiteHorizonBadEvent
    {Omega : Type u} {Arm : Type v}
    (bad : Arm -> Nat -> Set Omega) (T : Nat) : Set Omega :=
  ⋃ a, ⋃ t ∈ Finset.range T, bad a t

/--
Finite-horizon union bound for a UCB-style arm-time bad-event family.

No event measurability is required: this is an outer-measure bound inherited
from Mathlib's finite-union measure inequality.
-/
theorem measure_finiteHorizonBadEvent_le_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Arm : Type v} [Fintype Arm]
    (mu : Measure Omega)
    (bad : Arm -> Nat -> Set Omega)
    (T : Nat) :
    mu (finiteHorizonBadEvent bad T) <=
      (Finset.univ : Finset Arm).sum
        (fun a => (Finset.range T).sum (fun t => mu (bad a t))) := by
  unfold finiteHorizonBadEvent
  calc
    mu (⋃ a, ⋃ t ∈ Finset.range T, bad a t)
        <= (Finset.univ : Finset Arm).sum
            (fun a => mu (⋃ t ∈ Finset.range T, bad a t)) := by
          exact ProbabilityUnionBound.measure_iUnion_fintype_le_sum
            mu (fun a => ⋃ t ∈ Finset.range T, bad a t)
    _ <= (Finset.univ : Finset Arm).sum
          (fun a => (Finset.range T).sum (fun t => mu (bad a t))) := by
          exact Finset.sum_le_sum (fun a _ha =>
            ProbabilityUnionBound.measure_biUnion_finset_le
              mu (Finset.range T) (bad a))

/--
Tail-bound consumer for finite-horizon UCB bad events.

The hypothesis `htail` is the per-arm/per-time concentration result; this
wrapper only assembles those local bounds into the finite bad-event sum.
-/
theorem measure_finiteHorizonBadEvent_le_tail_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Arm : Type v} [Fintype Arm]
    (mu : Measure Omega)
    (bad : Arm -> Nat -> Set Omega)
    (tail : Arm -> Nat -> ENNReal)
    (T : Nat)
    (htail : forall a t, t < T -> mu (bad a t) <= tail a t) :
    mu (finiteHorizonBadEvent bad T) <=
      (Finset.univ : Finset Arm).sum
        (fun a => (Finset.range T).sum (fun t => tail a t)) := by
  exact (measure_finiteHorizonBadEvent_le_sum mu bad T).trans
    (Finset.sum_le_sum (fun a _ha =>
      Finset.sum_le_sum (fun t ht =>
        htail a t (Finset.mem_range.mp ht))))

end UCBSummability
end BanditRLProof
