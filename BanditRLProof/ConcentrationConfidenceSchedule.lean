import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summable confidence schedules

This module records reusable deterministic schedules for countable confidence
budgets. It contains no stochastic-process or algorithm assumptions.
-/

namespace BanditRLProof.Concentration

open scoped ENNReal

/-- The geometric confidence schedule `delta / 2 / 2^n`. -/
noncomputable def geometricConfidenceShare
    (delta : Real) (n : Nat) : Real :=
  delta / 2 / 2 ^ n

/-- Every geometric confidence share is positive when its outer budget is. -/
theorem geometricConfidenceShare_pos
    {delta : Real} (hdelta : 0 < delta) (n : Nat) :
    0 < geometricConfidenceShare delta n := by
  unfold geometricConfidenceShare
  positivity

/-- The ENNReal masses of the geometric confidence shares sum exactly to the
outer budget. -/
theorem tsum_ofReal_geometricConfidenceShare
    {delta : Real} (hdelta : 0 <= delta) :
    ∑' n, ENNReal.ofReal (geometricConfidenceShare delta n) =
      ENNReal.ofReal delta := by
  have hreal : HasSum (geometricConfidenceShare delta) delta := by
    simpa [geometricConfidenceShare] using hasSum_geometric_two' delta
  have hnonneg : forall n, 0 <= geometricConfidenceShare delta n := by
    intro n
    unfold geometricConfidenceShare
    positivity
  have hnnreal :
      HasSum
          (fun n => (geometricConfidenceShare delta n).toNNReal)
          delta.toNNReal :=
    hreal.toNNReal hnonneg
  have hcoe :
      HasSum
          (fun n => ((geometricConfidenceShare delta n).toNNReal : ENNReal))
          (delta.toNNReal : ENNReal) :=
    ENNReal.hasSum_coe.mpr hnnreal
  have hofReal :
      HasSum
          (fun n => ENNReal.ofReal (geometricConfidenceShare delta n))
          (ENNReal.ofReal delta) := by
    simpa only [ENNReal.ofReal_eq_coe_nnreal] using hcoe
  exact hofReal.tsum_eq

end BanditRLProof.Concentration
