import BanditRLProof.ConcentrationConfidenceSchedule
import BanditRLProof.ProbabilityUnionBound

/-!
# Finite-index geometric all-time confidence

This module composes two already-compiled outer-measure adapters: a finite
equal-share union at each time and a countable geometric schedule over time.
It is deliberately only a confidence-budget composition theorem. It does not
produce the per-index tails and is not a Ville/Doob, mixture, optional-stopping,
self-normalized, or general Freedman inequality.
-/

namespace BanditRLProof.Concentration

open MeasureTheory
open scoped ENNReal

universe u v

/-- A countable family of finite-index bad events is controlled by the sum of
its per-time budgets when every index receives an equal share. No event
measurability or probability-measure assumption is required. -/
theorem measure_iUnion_iUnion_fintype_le_tsum_of_uniform
    {Omega : Type u} {Idx : Type v}
    [MeasurableSpace Omega] [Fintype Idx] [Nonempty Idx]
    (mu : Measure Omega)
    (bad : Nat -> Idx -> Set Omega)
    (deltaAt : Nat -> Real)
    (hbad : forall n i,
      mu (bad n i) <=
        ENNReal.ofReal (deltaAt n / (Fintype.card Idx : Real))) :
    mu (⋃ n, ⋃ i, bad n i) <=
      ∑' n, ENNReal.ofReal (deltaAt n) := by
  classical
  calc
    mu (⋃ n, ⋃ i, bad n i) <= ∑' n, mu (⋃ i, bad n i) :=
      MeasureTheory.measure_iUnion_le _
    _ <= ∑' n, ENNReal.ofReal (deltaAt n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa using
        (ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
          mu (Finset.univ : Finset Idx) Finset.univ_nonempty
            (deltaAt n) (bad n) (fun i _hi => hbad n i))

/-- Equal sharing across a nonempty finite index type at every time, followed
by the geometric schedule over time, gives one all-time outer confidence
budget. No event measurability or probability-measure assumption is required. -/
theorem measure_iUnion_iUnion_fintype_le_delta_of_geometricConfidenceShare
    {Omega : Type u} {Idx : Type v}
    [MeasurableSpace Omega] [Fintype Idx] [Nonempty Idx]
    (mu : Measure Omega)
    (bad : Nat -> Idx -> Set Omega)
    (delta : Real) (hdelta : 0 <= delta)
    (hbad : forall n i,
      mu (bad n i) <= ENNReal.ofReal
        (geometricConfidenceShare delta n / (Fintype.card Idx : Real))) :
    mu (⋃ n, ⋃ i, bad n i) <= ENNReal.ofReal delta := by
  calc
    mu (⋃ n, ⋃ i, bad n i) <=
        ∑' n, ENNReal.ofReal (geometricConfidenceShare delta n) :=
      measure_iUnion_iUnion_fintype_le_tsum_of_uniform
        mu bad (geometricConfidenceShare delta) hbad
    _ = ENNReal.ofReal delta :=
      tsum_ofReal_geometricConfidenceShare hdelta

end BanditRLProof.Concentration
