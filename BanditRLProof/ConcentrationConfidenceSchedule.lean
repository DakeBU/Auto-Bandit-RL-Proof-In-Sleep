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

/-- Positive telescoping weight `1 / ((n+1)(n+2))`.  Unlike the geometric
weight, its reciprocal grows only polynomially in time. -/
noncomputable def telescopingConfidenceWeight (n : Nat) : Real :=
  1 / (((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real))

/-- The telescoping weight is a difference of consecutive reciprocals. -/
theorem telescopingConfidenceWeight_eq_sub (n : Nat) :
    telescopingConfidenceWeight n =
      1 / (((n + 1 : Nat) : Real)) -
        1 / (((n + 2 : Nat) : Real)) := by
  unfold telescopingConfidenceWeight
  field_simp
  norm_num [Nat.cast_add]

/-- Exact finite partial sum of the telescoping weights. -/
theorem sum_range_telescopingConfidenceWeight (n : Nat) :
    (Finset.range n).sum telescopingConfidenceWeight =
      1 - 1 / (((n + 1 : Nat) : Real)) := by
  rw [Finset.sum_congr rfl
    (fun i _hi => telescopingConfidenceWeight_eq_sub i)]
  rw [Finset.sum_range_sub']
  norm_num

/-- Every telescoping confidence weight is nonnegative. -/
theorem telescopingConfidenceWeight_nonneg (n : Nat) :
    0 <= telescopingConfidenceWeight n := by
  unfold telescopingConfidenceWeight
  positivity

/-- The telescoping weights sum exactly to one. -/
theorem hasSum_telescopingConfidenceWeight :
    HasSum telescopingConfidenceWeight 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg telescopingConfidenceWeight_nonneg]
  simp_rw [sum_range_telescopingConfidenceWeight]
  have hcast :
      Filter.Tendsto
        (fun n : Nat => (((n + 1 : Nat) : Real)))
        Filter.atTop Filter.atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hinv :
      Filter.Tendsto
        (fun n : Nat => (1 / (((n + 1 : Nat) : Real))))
        Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hcast
  simpa using tendsto_const_nhds.sub hinv

/-- Time-`n` confidence share `delta / ((n+1)(n+2))`. -/
noncomputable def telescopingConfidenceShare
    (delta : Real) (n : Nat) : Real :=
  delta * telescopingConfidenceWeight n

/-- Display the telescoping share as the intended quotient. -/
theorem telescopingConfidenceShare_eq_div (delta : Real) (n : Nat) :
    telescopingConfidenceShare delta n =
      delta /
        (((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real)) := by
  simp [telescopingConfidenceShare, telescopingConfidenceWeight,
    div_eq_mul_inv]

/-- Every telescoping confidence share is positive when its outer budget is. -/
theorem telescopingConfidenceShare_pos
    {delta : Real} (hdelta : 0 < delta) (n : Nat) :
    0 < telescopingConfidenceShare delta n := by
  unfold telescopingConfidenceShare telescopingConfidenceWeight
  positivity

/-- The ENNReal masses of the telescoping confidence shares sum exactly to
the outer budget. -/
theorem tsum_ofReal_telescopingConfidenceShare
    {delta : Real} (hdelta : 0 <= delta) :
    ∑' n, ENNReal.ofReal (telescopingConfidenceShare delta n) =
      ENNReal.ofReal delta := by
  have hreal : HasSum (telescopingConfidenceShare delta) delta := by
    simpa [telescopingConfidenceShare] using
      hasSum_telescopingConfidenceWeight.mul_left delta
  have hnonneg : forall n, 0 <= telescopingConfidenceShare delta n := by
    intro n
    exact mul_nonneg hdelta (telescopingConfidenceWeight_nonneg n)
  have hnnreal :
      HasSum
          (fun n => (telescopingConfidenceShare delta n).toNNReal)
          delta.toNNReal :=
    hreal.toNNReal hnonneg
  have hcoe :
      HasSum
          (fun n => ((telescopingConfidenceShare delta n).toNNReal : ENNReal))
          (delta.toNNReal : ENNReal) :=
    ENNReal.hasSum_coe.mpr hnnreal
  have hofReal :
      HasSum
          (fun n => ENNReal.ofReal (telescopingConfidenceShare delta n))
          (ENNReal.ofReal delta) := by
    simpa only [ENNReal.ofReal_eq_coe_nnreal] using hcoe
  exact hofReal.tsum_eq

end BanditRLProof.Concentration
