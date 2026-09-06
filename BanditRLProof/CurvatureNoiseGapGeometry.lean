import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Curvature--Noise--Gap geometry: finite algebraic leaves

This file contains only route-independent finite-dimensional algebra.  It does
not formalize the full Curvature--Noise--Gap calculus, Tsallis-INF, or a new
bandit theorem.  The intended later use is to test whether these abstractions
replace repeated route-specific proof subgraphs and transfer to held-out proof
families.

The assumptions are deliberately explicit.  Tangent invariance needs only a
zero-sum direction.  The weighted shift minimum needs nonnegative weights and
strictly positive total weight; it does not hide an interiority or
positive-definiteness premise.
-/

namespace BanditRLProof
namespace CurvatureNoiseGap

open scoped BigOperators

/-- A finite direction tangent to the affine simplex hyperplane. -/
def IsSimplexTangent {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (direction : Index -> Real) : Prop :=
  indices.sum direction = 0

/-- The finite pairing used to test a signal against a tangent direction. -/
def tangentPairing {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (signal direction : Index -> Real) : Real :=
  indices.sum (fun i => signal i * direction i)

/-- Adding a constant to a signal is invisible on the simplex tangent space. -/
theorem tangentPairing_add_const_of_isSimplexTangent
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (signal direction : Index -> Real) (shift : Real)
    (hdirection : IsSimplexTangent indices direction) :
    tangentPairing indices (fun i => signal i + shift) direction =
      tangentPairing indices signal direction := by
  unfold tangentPairing IsSimplexTangent at *
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, <- Finset.mul_sum, hdirection, mul_zero, add_zero]

/-- Weighted squared energy after removing one common scalar shift. -/
def weightedShiftEnergy {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal : Index -> Real) (shift : Real) : Real :=
  indices.sum (fun i => weight i * (signal i - shift) ^ 2)

/-- The scalar shift selected by a nondegenerate weighted quadratic energy. -/
noncomputable def weightedCenter {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal : Index -> Real) : Real :=
  indices.sum (fun i => weight i * signal i) / indices.sum weight

/-- The weighted residual about `weightedCenter` has zero weighted sum. -/
theorem sum_weight_mul_sub_weightedCenter_eq_zero
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal : Index -> Real)
    (hweightSum : indices.sum weight ≠ 0) :
    indices.sum (fun i =>
      weight i * (signal i - weightedCenter indices weight signal)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, <- Finset.sum_mul]
  unfold weightedCenter
  field_simp
  ring

/-- Completing the square around any weighted-centered scalar. -/
theorem weightedShiftEnergy_decomposition_of_centered
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal : Index -> Real)
    (center shift : Real)
    (hcenter : indices.sum (fun i => weight i * (signal i - center)) = 0) :
    weightedShiftEnergy indices weight signal shift =
      weightedShiftEnergy indices weight signal center +
        indices.sum weight * (shift - center) ^ 2 := by
  unfold weightedShiftEnergy
  calc
    indices.sum (fun i => weight i * (signal i - shift) ^ 2) =
        indices.sum (fun i =>
          (weight i * (signal i - center) ^ 2 +
            2 * (center - shift) * (weight i * (signal i - center))) +
              weight i * (center - shift) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = indices.sum (fun i => weight i * (signal i - center) ^ 2) +
          2 * (center - shift) *
              indices.sum (fun i => weight i * (signal i - center)) +
            indices.sum weight * (center - shift) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        <- Finset.mul_sum, <- Finset.sum_mul]
    _ = indices.sum (fun i => weight i * (signal i - center) ^ 2) +
          indices.sum weight * (shift - center) ^ 2 := by
      rw [hcenter]
      ring

/-- Exact min-shift decomposition at the weighted center. -/
theorem weightedShiftEnergy_decomposition
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal : Index -> Real) (shift : Real)
    (hweightSum : indices.sum weight ≠ 0) :
    weightedShiftEnergy indices weight signal shift =
      weightedShiftEnergy indices weight signal (weightedCenter indices weight signal) +
        indices.sum weight *
          (shift - weightedCenter indices weight signal) ^ 2 := by
  exact weightedShiftEnergy_decomposition_of_centered
    indices weight signal (weightedCenter indices weight signal) shift
    (sum_weight_mul_sub_weightedCenter_eq_zero
      indices weight signal hweightSum)

/-- The weighted center minimizes the quadratic shift energy. -/
theorem weightedShiftEnergy_center_le
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal : Index -> Real) (shift : Real)
    (hweight : forall i, i ∈ indices -> 0 <= weight i)
    (hweightSum : 0 < indices.sum weight) :
    weightedShiftEnergy indices weight signal (weightedCenter indices weight signal) <=
      weightedShiftEnergy indices weight signal shift := by
  rw [weightedShiftEnergy_decomposition indices weight signal shift hweightSum.ne']
  exact le_add_of_nonneg_right
    (mul_nonneg (Finset.sum_nonneg hweight) (sq_nonneg _))

/-- Strict positivity of the total weight makes the minimizing shift unique. -/
theorem weightedShiftEnergy_eq_center_iff
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal : Index -> Real) (shift : Real)
    (hweightSum : 0 < indices.sum weight) :
    weightedShiftEnergy indices weight signal shift =
        weightedShiftEnergy indices weight signal (weightedCenter indices weight signal) <->
      shift = weightedCenter indices weight signal := by
  rw [weightedShiftEnergy_decomposition indices weight signal shift hweightSum.ne']
  constructor
  · intro henergy
    have hmul : indices.sum weight *
        (shift - weightedCenter indices weight signal) ^ 2 = 0 := by
      linarith
    have hsquare :
        (shift - weightedCenter indices weight signal) ^ 2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hweightSum.ne'
    have hsub : shift - weightedCenter indices weight signal = 0 := by
      nlinarith
    exact sub_eq_zero.mp hsub
  · intro hshift
    rw [hshift]
    ring

/-- Exact signal--noise decomposition, including the interaction term. -/
theorem weightedShiftEnergy_add_decomposition
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal noise : Index -> Real)
    (signalShift noiseShift : Real) :
    weightedShiftEnergy indices weight (fun i => signal i + noise i)
        (signalShift + noiseShift) =
      weightedShiftEnergy indices weight signal signalShift +
        weightedShiftEnergy indices weight noise noiseShift +
          2 * indices.sum (fun i =>
            weight i * (signal i - signalShift) * (noise i - noiseShift)) := by
  unfold weightedShiftEnergy
  calc
    indices.sum (fun i =>
        weight i * (signal i + noise i - (signalShift + noiseShift)) ^ 2) =
      indices.sum (fun i =>
        (weight i * (signal i - signalShift) ^ 2 +
          weight i * (noise i - noiseShift) ^ 2) +
            2 * (weight i * (signal i - signalShift) *
              (noise i - noiseShift))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = indices.sum (fun i => weight i * (signal i - signalShift) ^ 2) +
          indices.sum (fun i => weight i * (noise i - noiseShift) ^ 2) +
            2 * indices.sum (fun i =>
              weight i * (signal i - signalShift) * (noise i - noiseShift)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, <- Finset.mul_sum]

/-- A conservative two-term signal--noise energy bound. -/
theorem weightedShiftEnergy_add_le_two
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight signal noise : Index -> Real)
    (signalShift noiseShift : Real)
    (hweight : forall i, i ∈ indices -> 0 <= weight i) :
    weightedShiftEnergy indices weight (fun i => signal i + noise i)
        (signalShift + noiseShift) <=
      2 * weightedShiftEnergy indices weight signal signalShift +
        2 * weightedShiftEnergy indices weight noise noiseShift := by
  unfold weightedShiftEnergy
  calc
    indices.sum (fun i =>
        weight i * (signal i + noise i - (signalShift + noiseShift)) ^ 2) <=
      indices.sum (fun i =>
        2 * (weight i * (signal i - signalShift) ^ 2) +
          2 * (weight i * (noise i - noiseShift) ^ 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hw := hweight i hi
        nlinarith [sq_nonneg ((signal i - signalShift) -
          (noise i - noiseShift))]
    _ = 2 * indices.sum (fun i => weight i * (signal i - signalShift) ^ 2) +
          2 * indices.sum (fun i => weight i * (noise i - noiseShift) ^ 2) := by
        rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]

end CurvatureNoiseGap
end BanditRLProof
