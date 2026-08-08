import BanditRLProof.OFULScalarRegularizationBias
import BanditRLProof.ProbabilityUnionBound

/-!
# Finite-window uniform OFUL confidence

This module assembles the compiled deterministic-horizon scalar-ridge
confidence theorem over every horizon in a finite inclusive window.  It
supports arbitrary confidence schedules with values in `(0, 1]` and an equal
allocation whose budgets sum exactly to `delta`, giving failure probability
at most `delta`.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace OFUL

/-- Failure of the scalar-ridge confidence ellipsoid at one horizon. -/
def scalarRidgeConfidenceFailureAt
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R delta : Real)
    (n : Nat) : Set Omega :=
  {omega |
    matrixNorm
        (Matrix.scalar Feature lambda +
          finiteHorizonFeatureGram feature n omega)
        (finiteHorizonRidgeEstimate
            (Matrix.scalar Feature lambda) feature response n omega -
          thetaStar) >
      finiteHorizonScalarConfidenceRadius
        feature R delta lambda S n omega}

/--
Union of scalar-ridge confidence failures over all `n <= horizon`, with the
confidence level selected by `deltaAt n`.
-/
def finiteHorizonScheduledScalarRidgeConfidenceFailureSet
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R : Real)
    (deltaAt : Nat -> Real)
    (horizon : Nat) : Set Omega :=
  ⋃ n ∈ Finset.range (horizon + 1),
    scalarRidgeConfidenceFailureAt
      lambda thetaStar S feature response R (deltaAt n) n

/-- Membership in the scheduled failure set is failure at some `n <= horizon`. -/
theorem mem_finiteHorizonScheduledScalarRidgeConfidenceFailureSet_iff
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R : Real)
    (deltaAt : Nat -> Real)
    (horizon : Nat) (omega : Omega) :
    omega ∈ finiteHorizonScheduledScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R deltaAt horizon ↔
      ∃ n, n <= horizon ∧
        omega ∈ scalarRidgeConfidenceFailureAt
          lambda thetaStar S feature response R (deltaAt n) n := by
  simp only [finiteHorizonScheduledScalarRidgeConfidenceFailureSet,
    Set.mem_iUnion, exists_prop, Finset.mem_range, Nat.lt_succ_iff]

/--
Outside the scheduled failure union, every scalar-ridge confidence ellipsoid
in the inclusive finite window holds simultaneously.
-/
theorem not_mem_finiteHorizonScheduledScalarRidgeConfidenceFailureSet_iff
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R : Real)
    (deltaAt : Nat -> Real)
    (horizon : Nat) (omega : Omega) :
    omega ∉ finiteHorizonScheduledScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R deltaAt horizon ↔
      ∀ n, n <= horizon ->
        matrixNorm
            (Matrix.scalar Feature lambda +
              finiteHorizonFeatureGram feature n omega)
            (finiteHorizonRidgeEstimate
                (Matrix.scalar Feature lambda) feature response n omega -
              thetaStar) <=
          finiteHorizonScalarConfidenceRadius
            feature R (deltaAt n) lambda S n omega := by
  simp only [mem_finiteHorizonScheduledScalarRidgeConfidenceFailureSet_iff,
    scalarRidgeConfidenceFailureAt, Set.mem_setOf_eq, not_exists,
    not_and, not_lt]

/--
Scheduled finite-window confidence: the failure-union probability is bounded
by the sum of the fixed-time confidence budgets.
-/
theorem measure_finiteHorizonScheduledScalarRidgeConfidenceFailureSet_le_sum
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
    (horizon : Nat)
    (hsubGaussian : forall i, i < horizon ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i)
        (constantSquaredVarianceProxy R i) mu)
    (hresponse : forall omega i, i < horizon ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega)
    (deltaAt : Nat -> Real)
    (hdeltaAt : forall n, n <= horizon -> 0 < deltaAt n)
    (hdeltaAt_one : forall n, n <= horizon -> deltaAt n <= 1) :
    mu (finiteHorizonScheduledScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R deltaAt horizon) <=
      (Finset.range (horizon + 1)).sum
        (fun n => ENNReal.ofReal (deltaAt n)) := by
  unfold finiteHorizonScheduledScalarRidgeConfidenceFailureSet
  calc
    mu (⋃ n ∈ Finset.range (horizon + 1),
        scalarRidgeConfidenceFailureAt
          lambda thetaStar S feature response R (deltaAt n) n) <=
        (Finset.range (horizon + 1)).sum (fun n =>
          mu (scalarRidgeConfidenceFailureAt
            lambda thetaStar S feature response R (deltaAt n) n)) := by
      exact ProbabilityUnionBound.measure_biUnion_finset_le
        mu (Finset.range (horizon + 1)) fun n =>
          scalarRidgeConfidenceFailureAt
            lambda thetaStar S feature response R (deltaAt n) n
    _ <= (Finset.range (horizon + 1)).sum
          (fun n => ENNReal.ofReal (deltaAt n)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnle : n <= horizon :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      simpa only [scalarRidgeConfidenceFailureAt] using
        measure_finiteHorizonScalarRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le
          mu lambda hlambda thetaStar S htheta F feature response noise R hR
          projectionBound hfeature hnoise hprojectionBound_nonneg
          hprojectionBound n
          (fun i hi => hsubGaussian i (lt_of_lt_of_le hi hnle))
          (deltaAt n) (hdeltaAt n hnle) (hdeltaAt_one n hnle)
          (fun omega i hi =>
            hresponse omega i (lt_of_lt_of_le hi hnle))

/--
Equal-share finite-window failure union.  The inclusive window has
`horizon + 1` horizons, so each fixed-time theorem receives
`delta / (horizon + 1)`.
-/
def finiteHorizonUniformScalarRidgeConfidenceFailureSet
    {Omega : Type u} {Feature : Type v}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R delta : Real)
    (horizon : Nat) : Set Omega :=
  finiteHorizonScheduledScalarRidgeConfidenceFailureSet
    lambda thetaStar S feature response R
    (fun _ => delta / ((horizon + 1 : Nat) : Real)) horizon

/--
Uniform scalar-ridge confidence over every deterministic horizon
`n <= horizon`, obtained by equal allocation of the total failure budget.
-/
theorem measure_finiteHorizonUniformScalarRidgeConfidenceFailureSet_le
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
    (horizon : Nat)
    (hsubGaussian : forall i, i < horizon ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i)
        (constantSquaredVarianceProxy R i) mu)
    (hresponse : forall omega i, i < horizon ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    mu (finiteHorizonUniformScalarRidgeConfidenceFailureSet
        lambda thetaStar S feature response R delta horizon) <=
      ENNReal.ofReal delta := by
  unfold finiteHorizonUniformScalarRidgeConfidenceFailureSet
    finiteHorizonScheduledScalarRidgeConfidenceFailureSet
  apply ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
    mu (Finset.range (horizon + 1)) (by simp) delta
  intro n hn
  have hnle : n <= horizon :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hden_pos : 0 < (((horizon + 1 : Nat) : Real)) := by positivity
  have hden_one : (1 : Real) <= ((horizon + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
  have hlocal_pos :
      0 < delta / ((horizon + 1 : Nat) : Real) :=
    div_pos hdelta hden_pos
  have hlocal_one :
      delta / ((horizon + 1 : Nat) : Real) <= 1 :=
    (div_le_one hden_pos).2 (hdelta_one.trans hden_one)
  simpa only [Finset.card_range, scalarRidgeConfidenceFailureAt] using
    measure_finiteHorizonScalarRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le
      mu lambda hlambda thetaStar S htheta F feature response noise R hR
      projectionBound hfeature hnoise hprojectionBound_nonneg hprojectionBound
      n (fun i hi => hsubGaussian i (lt_of_lt_of_le hi hnle))
      (delta / ((horizon + 1 : Nat) : Real)) hlocal_pos hlocal_one
      (fun omega i hi =>
        hresponse omega i (lt_of_lt_of_le hi hnle))

end OFUL
end BanditRLProof
