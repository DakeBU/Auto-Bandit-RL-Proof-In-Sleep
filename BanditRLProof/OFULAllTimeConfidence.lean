import BanditRLProof.OFULUniformTimeConfidence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# All-time scheduled OFUL confidence

This module upgrades the fixed-time scalar-ridge confidence theorem to one
countable union over every deterministic horizon on the same probability
space.  A telescoping confidence schedule allocates the total failure budget
exactly:

`delta_n = delta / ((n + 1) * (n + 2))`.

This is an all-time confidence theorem for one fixed process.  It does not
identify a generated OFUL policy; a one-policy anytime regret consumer must
first use a history algorithm whose confidence parameter follows this schedule.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace OFUL

/-- Countable union of scalar-ridge confidence failures over every horizon. -/
def allTimeScheduledScalarRidgeConfidenceFailureSet
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R : Real)
    (deltaAt : Nat -> Real) : Set Omega :=
  ⋃ n, scalarRidgeConfidenceFailureAt
    lambda thetaStar S feature response R (deltaAt n) n

/-- Membership means failure at at least one deterministic horizon. -/
theorem mem_allTimeScheduledScalarRidgeConfidenceFailureSet_iff
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R : Real)
    (deltaAt : Nat -> Real)
    (omega : Omega) :
    omega ∈ allTimeScheduledScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R deltaAt ↔
      ∃ n, omega ∈ scalarRidgeConfidenceFailureAt
        lambda thetaStar S feature response R (deltaAt n) n := by
  simp [allTimeScheduledScalarRidgeConfidenceFailureSet]

/--
Outside the countable failure union, every deterministic-horizon confidence
ellipsoid holds simultaneously.
-/
theorem not_mem_allTimeScheduledScalarRidgeConfidenceFailureSet_iff
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R : Real)
    (deltaAt : Nat -> Real)
    (omega : Omega) :
    omega ∉ allTimeScheduledScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R deltaAt ↔
      ∀ n,
        matrixNorm
            (Matrix.scalar Feature lambda +
              finiteHorizonFeatureGram feature n omega)
            (finiteHorizonRidgeEstimate
                (Matrix.scalar Feature lambda) feature response n omega -
              thetaStar) <=
          finiteHorizonScalarConfidenceRadius
            feature R (deltaAt n) lambda S n omega := by
  simp only [mem_allTimeScheduledScalarRidgeConfidenceFailureSet_iff,
    scalarRidgeConfidenceFailureAt, Set.mem_setOf_eq, not_exists, not_lt]

/--
All-time scheduled confidence: countable subadditivity bounds the failure
probability by the `ENNReal` sum of the fixed-time budgets.
-/
theorem measure_allTimeScheduledScalarRidgeConfidenceFailureSet_le_tsum
    {Omega : Type u} {Feature : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real) (S : Real)
    (htheta : euclideanLength thetaStar <= S)
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (response noise : Nat -> Omega -> Real)
    (R : Real) (hR : 0 < R)
    (projectionBound : EuclideanSpace Real Feature -> Nat -> Real)
    (hfeature : forall i j,
      StronglyMeasurable[F i] (fun omega => feature i omega j))
    (hnoise : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => noise i omega))
    (hprojectionBound_nonneg : forall theta i,
      0 <= projectionBound theta i)
    (hprojectionBound : forall theta i omega,
      |dotProduct (WithLp.ofLp theta) (feature i omega)| <=
        projectionBound theta i)
    (hsubGaussian : forall i,
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i)
        (constantSquaredVarianceProxy R i) mu)
    (hresponse : forall omega i,
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega)
    (deltaAt : Nat -> Real)
    (hdeltaAt : forall n, 0 < deltaAt n)
    (hdeltaAt_one : forall n, deltaAt n <= 1) :
    mu (allTimeScheduledScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R deltaAt) <=
      ∑' n, ENNReal.ofReal (deltaAt n) := by
  unfold allTimeScheduledScalarRidgeConfidenceFailureSet
  calc
    mu (⋃ n, scalarRidgeConfidenceFailureAt
        lambda thetaStar S feature response R (deltaAt n) n) <=
        ∑' n, mu (scalarRidgeConfidenceFailureAt
          lambda thetaStar S feature response R (deltaAt n) n) := by
      exact MeasureTheory.measure_iUnion_le _
    _ <= ∑' n, ENNReal.ofReal (deltaAt n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [scalarRidgeConfidenceFailureAt] using
        measure_finiteHorizonScalarRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le
          mu lambda hlambda thetaStar S htheta F feature response noise R hR
          projectionBound hfeature hnoise hprojectionBound_nonneg
          hprojectionBound n
          (fun i _hi => hsubGaussian i)
          (deltaAt n) (hdeltaAt n) (hdeltaAt_one n)
          (fun omega i _hi => hresponse omega i)

/-- Positive telescoping weight `1 / ((n+1)(n+2))`. -/
noncomputable def allTimeTelescopingWeight (n : Nat) : Real :=
  1 / (((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real))

/-- The telescoping weight is a difference of consecutive reciprocals. -/
theorem allTimeTelescopingWeight_eq_sub (n : Nat) :
    allTimeTelescopingWeight n =
      1 / (((n + 1 : Nat) : Real)) -
        1 / (((n + 2 : Nat) : Real)) := by
  unfold allTimeTelescopingWeight
  field_simp
  norm_num [Nat.cast_add]

/-- Exact finite partial sum of the telescoping weights. -/
theorem sum_range_allTimeTelescopingWeight (n : Nat) :
    (Finset.range n).sum allTimeTelescopingWeight =
      1 - 1 / (((n + 1 : Nat) : Real)) := by
  rw [Finset.sum_congr rfl
    (fun i _hi => allTimeTelescopingWeight_eq_sub i)]
  rw [Finset.sum_range_sub']
  norm_num

/-- Every telescoping confidence weight is nonnegative. -/
theorem allTimeTelescopingWeight_nonneg (n : Nat) :
    0 <= allTimeTelescopingWeight n := by
  unfold allTimeTelescopingWeight
  positivity

/-- Every telescoping confidence weight is at most one. -/
theorem allTimeTelescopingWeight_le_one (n : Nat) :
    allTimeTelescopingWeight n <= 1 := by
  unfold allTimeTelescopingWeight
  have hfirst :
      (1 : Real) <= (((n + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsecond :
      (1 : Real) <= (((n + 2 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n + 1))
  have hden :
      (1 : Real) <=
        (((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real)) := by
    nlinarith
  have hden_pos :
      0 <
        (((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real)) :=
    lt_of_lt_of_le zero_lt_one hden
  exact (div_le_one hden_pos).2 hden

/-- The telescoping weights sum exactly to one. -/
theorem hasSum_allTimeTelescopingWeight :
    HasSum allTimeTelescopingWeight 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg allTimeTelescopingWeight_nonneg]
  simp_rw [sum_range_allTimeTelescopingWeight]
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

/-- Time-`n` share of an all-time failure budget. -/
noncomputable def allTimeTelescopingDelta
    (delta : Real) (n : Nat) : Real :=
  delta * allTimeTelescopingWeight n

/-- Display the scheduled budget as `delta / ((n+1)(n+2))`. -/
theorem allTimeTelescopingDelta_eq_div (delta : Real) (n : Nat) :
    allTimeTelescopingDelta delta n =
      delta /
        (((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real)) := by
  simp [allTimeTelescopingDelta, allTimeTelescopingWeight, div_eq_mul_inv]

/-- Positive outer budget gives positive timewise budgets. -/
theorem allTimeTelescopingDelta_pos
    {delta : Real} (hdelta : 0 < delta) (n : Nat) :
    0 < allTimeTelescopingDelta delta n :=
  mul_pos hdelta (by
    unfold allTimeTelescopingWeight
    positivity)

/-- If `delta <= 1`, every timewise budget is also at most one. -/
theorem allTimeTelescopingDelta_le_one
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (n : Nat) :
    allTimeTelescopingDelta delta n <= 1 := by
  calc
    allTimeTelescopingDelta delta n <= delta := by
      unfold allTimeTelescopingDelta
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left
          (allTimeTelescopingWeight_le_one n) hdelta.le
    _ <= 1 := hdelta_one

/-- The `ENNReal` scheduled failure budgets sum exactly to `ofReal delta`. -/
theorem tsum_ofReal_allTimeTelescopingDelta
    {delta : Real} (hdelta : 0 <= delta) :
    ∑' n, ENNReal.ofReal (allTimeTelescopingDelta delta n) =
      ENNReal.ofReal delta := by
  have hreal :
      HasSum (allTimeTelescopingDelta delta) delta := by
    simpa [allTimeTelescopingDelta] using
      hasSum_allTimeTelescopingWeight.mul_left delta
  have hnonneg : forall n, 0 <= allTimeTelescopingDelta delta n := by
    intro n
    exact mul_nonneg hdelta (allTimeTelescopingWeight_nonneg n)
  have hnnreal :
      HasSum
          (fun n => (allTimeTelescopingDelta delta n).toNNReal)
          delta.toNNReal :=
    hreal.toNNReal hnonneg
  have hcoe :
      HasSum
          (fun n =>
            ((allTimeTelescopingDelta delta n).toNNReal : ENNReal))
          (delta.toNNReal : ENNReal) :=
    ENNReal.hasSum_coe.mpr hnnreal
  have hofReal :
      HasSum
          (fun n => ENNReal.ofReal (allTimeTelescopingDelta delta n))
          (ENNReal.ofReal delta) := by
    simpa only [ENNReal.ofReal_eq_coe_nnreal] using hcoe
  exact hofReal.tsum_eq

/-- Failure set for the exact telescoping all-time confidence schedule. -/
def allTimeTelescopingScalarRidgeConfidenceFailureSet
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R delta : Real) : Set Omega :=
  allTimeScheduledScalarRidgeConfidenceFailureSet
    lambda thetaStar S feature response R
      (allTimeTelescopingDelta delta)

/--
All-time scalar-ridge confidence under the exact telescoping failure schedule.
The result is one countable event on one process, not a family of
horizon-dependent generated algorithms.
-/
theorem measure_allTimeTelescopingScalarRidgeConfidenceFailureSet_le
    {Omega : Type u} {Feature : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real) (S : Real)
    (htheta : euclideanLength thetaStar <= S)
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (response noise : Nat -> Omega -> Real)
    (R : Real) (hR : 0 < R)
    (projectionBound : EuclideanSpace Real Feature -> Nat -> Real)
    (hfeature : forall i j,
      StronglyMeasurable[F i] (fun omega => feature i omega j))
    (hnoise : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => noise i omega))
    (hprojectionBound_nonneg : forall theta i,
      0 <= projectionBound theta i)
    (hprojectionBound : forall theta i omega,
      |dotProduct (WithLp.ofLp theta) (feature i omega)| <=
        projectionBound theta i)
    (hsubGaussian : forall i,
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i)
        (constantSquaredVarianceProxy R i) mu)
    (hresponse : forall omega i,
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    mu (allTimeTelescopingScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R delta) <=
      ENNReal.ofReal delta := by
  unfold allTimeTelescopingScalarRidgeConfidenceFailureSet
  calc
    mu (allTimeScheduledScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R
          (allTimeTelescopingDelta delta)) <=
        ∑' n, ENNReal.ofReal (allTimeTelescopingDelta delta n) := by
      exact measure_allTimeScheduledScalarRidgeConfidenceFailureSet_le_tsum
        mu lambda hlambda thetaStar S htheta F feature response noise R hR
        projectionBound hfeature hnoise hprojectionBound_nonneg
        hprojectionBound hsubGaussian hresponse
        (allTimeTelescopingDelta delta)
        (allTimeTelescopingDelta_pos hdelta)
        (allTimeTelescopingDelta_le_one hdelta hdelta_one)
    _ = ENNReal.ofReal delta :=
      tsum_ofReal_allTimeTelescopingDelta hdelta.le

end OFUL
end BanditRLProof
