import BanditRLProof.OFULGeneratedTrajectoryRadiusWidth

/-!
# Normalized scalar-ridge OFUL confidence widths

This module derives the raw `confidenceWidth <= 1` contract from the explicit
normalization `dotProduct x x <= L2 <= lambda`, then exposes the canonical
standard successor-gap tail without a caller-supplied width premise.
-/

namespace BanditRLProof.OFUL

open Real Matrix
open scoped MatrixOrder

universe u

theorem regularizedPrefixFeatureGram_inv_quadratic_le_one
    {Feature : Type u} [Fintype Feature] [DecidableEq Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (feature : Nat -> Feature -> Real) (T : Nat)
    (x : Feature -> Real)
    (hx : dotProduct x x <= lambda) :
    dotProduct x
        ((regularizedPrefixFeatureGram lambda feature T)⁻¹.mulVec x) <=
      1 := by
  let V := regularizedPrefixFeatureGram lambda feature T
  let z := V⁻¹.mulVec x
  have hV : V.PosDef :=
    regularizedPrefixFeatureGram_posDef lambda hlambda feature T
  have hcancel : V.mulVec z = x :=
    posDef_mulVec_nonsingInv_mulVec V hV x
  have hq_eq :
      dotProduct x z = quadraticForm V z := by
    rw [← hcancel, dotProduct_comm,
      dotProduct_mulVec_eq_quadraticForm]
  have hzz_nonneg : 0 <= dotProduct z z := by
    rw [dotProduct]
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hq_nonneg : 0 <= dotProduct x z := by
    simpa [V, z] using
      regularizedPrefixFeatureGram_inv_quadratic_nonneg
        lambda hlambda feature T x
  have hregularization :
      lambda * dotProduct z z <= dotProduct x z := by
    rw [hq_eq]
    dsimp only [V]
    rw [regularizedPrefixFeatureGram_quadraticForm_eq_sum_sq]
    have hsum_nonneg :
        0 <=
          (Finset.range T).sum
            (fun t =>
              ((Finset.univ : Finset Feature).sum
                (fun i => feature t i * z i)) ^ 2) :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simpa [dotProduct, pow_two] using
      (le_add_of_nonneg_right hsum_nonneg :
        lambda * (Finset.univ : Finset Feature).sum (fun i => z i ^ 2) <=
          lambda * (Finset.univ : Finset Feature).sum (fun i => z i ^ 2) +
            (Finset.range T).sum
              (fun t =>
                ((Finset.univ : Finset Feature).sum
                  (fun i => feature t i * z i)) ^ 2))
  have hcauchy :
      dotProduct x z ^ 2 <= dotProduct x x * dotProduct z z := by
    simpa [dotProduct, pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset Feature) x z)
  have hsq_le : dotProduct x z ^ 2 <= dotProduct x z := by
    calc
      dotProduct x z ^ 2 <=
          dotProduct x x * dotProduct z z := hcauchy
      _ <= lambda * dotProduct z z :=
        mul_le_mul_of_nonneg_right hx hzz_nonneg
      _ <= dotProduct x z := hregularization
  have hq_le_one : dotProduct x z <= 1 := by
    nlinarith
  simpa [V, z] using hq_le_one

theorem confidenceWidth_regularizedPrefixFeatureGram_le_one
    {Feature : Type u} [Fintype Feature] [DecidableEq Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (feature : Nat -> Feature -> Real) (T : Nat)
    (x : Feature -> Real)
    (hx : dotProduct x x <= lambda) :
    confidenceWidth
        (regularizedPrefixFeatureGram lambda feature T) x <= 1 := by
  rw [confidenceWidth, Real.sqrt_le_one]
  exact regularizedPrefixFeatureGram_inv_quadratic_le_one
    lambda hlambda feature T x hx

theorem canonicalHistoryTrajectory_confidenceWidth_le_one
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (actionFeature : Fin K -> Feature -> Real)
    (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (trajectory : Nat -> Fin K × Real) (t : Nat) :
    confidenceWidth
        (finiteHorizonScalarGram lambda
          (canonicalHistoryTrajectoryFeature actionFeature)
          t trajectory)
        (actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory t)) <= 1 := by
  rw [finiteHorizonScalarGram_eq_regularizedPrefixFeatureGram]
  exact confidenceWidth_regularizedPrefixFeatureGram_le_one
    lambda hlambda
    (fun s =>
      canonicalHistoryTrajectoryFeature actionFeature s trajectory)
    t
    (actionFeature
      (Thompson.canonicalHistoryTrajectoryAction trajectory t))
    ((hactionFeatureBound
      (Thompson.canonicalHistoryTrajectoryAction trajectory t)).trans
      hL2lambda)

theorem
    canonicalHistoryTrajectory_sum_range_succ_radius_mul_width_le_standard_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (trajectory : Nat -> Fin K × Real) :
    (Finset.range horizon).sum (fun n =>
        2 *
          finiteHorizonScalarConfidenceRadius
            (canonicalHistoryTrajectoryFeature actionFeature)
            R (delta / ((horizon + 1 : Nat) : Real))
            lambda S (n + 1) trajectory *
          confidenceWidth
            (finiteHorizonScalarGram lambda
              (canonicalHistoryTrajectoryFeature actionFeature)
              (n + 1) trajectory)
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1)))) <=
      standardScalarRadiusWidthBound
        (Feature := Feature)
        R (delta / ((horizon + 1 : Nat) : Real))
        lambda S (horizon + 1) L2 := by
  exact
    canonicalHistoryTrajectory_sum_range_succ_radius_mul_width_le_standard
      lambda hlambda actionFeature R delta S hdelta hS
      horizon L2 hL2 hactionFeatureBound trajectory
      (fun t _ht =>
        canonicalHistoryTrajectory_confidenceWidth_le_one
          lambda hlambda actionFeature L2 hactionFeatureBound
          hL2lambda trajectory t)

theorem
    measure_canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (comparator : Nat -> Fin K)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet
          lambda thetaStar actionFeature R delta S horizon L2 comparator) <=
      ENNReal.ofReal delta := by
  exact
    measure_canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet_le_of_linearSubgaussianEnvironment
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment horizon L2 hL2
      hactionFeatureBound comparator
      (fun trajectory t _ht =>
        canonicalHistoryTrajectory_confidenceWidth_le_one
          lambda hlambda actionFeature L2 hactionFeatureBound
          hL2lambda trajectory t)
      source

end BanditRLProof.OFUL
