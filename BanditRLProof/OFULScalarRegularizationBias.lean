import BanditRLProof.OFULConfidenceEllipsoid

/-!
# Scalar-regularization bias for OFUL confidence ellipsoids

This module discharges the deterministic ridge-bias contract in the compiled
finite-horizon confidence ellipsoid when the base matrix is `lambda I`.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp Set
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace MatrixOrder

variable {Omega Feature : Type*}

/-- The Euclidean length written on the same finite-coordinate surface as `dotProduct`. -/
noncomputable def euclideanLength
    [Fintype Feature] (theta : Feature -> Real) : Real :=
  Real.sqrt (dotProduct theta theta)

/-- A positive scalar multiple of the identity is positive definite. -/
theorem scalarIdentity_posDef
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real) (hlambda : 0 < lambda) :
    (Matrix.scalar Feature lambda : Matrix Feature Feature Real).PosDef := by
  rw [Matrix.scalar_apply]
  exact Matrix.PosDef.diagonal (fun _ => hlambda)

/--
For `V = lambda I + G` with `G` positive semidefinite, the `V`-norm of the
ridge bias `V⁻¹ (lambda theta)` is at most `sqrt lambda * ‖theta‖₂`.
-/
theorem matrixNorm_nonsingInv_scalar_mulVec_le_sqrt_mul_euclideanLength
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (G : Matrix Feature Feature Real) (hG : G.PosSemidef)
    (theta : Feature -> Real) :
    matrixNorm
        (Matrix.scalar Feature lambda + G)
        ((Matrix.scalar Feature lambda + G)⁻¹.mulVec
          ((Matrix.scalar Feature lambda).mulVec theta)) <=
      Real.sqrt lambda * euclideanLength theta := by
  let V : Matrix Feature Feature Real := Matrix.scalar Feature lambda + G
  let z : Feature -> Real :=
    V⁻¹.mulVec ((Matrix.scalar Feature lambda).mulVec theta)
  change matrixNorm V z <=
    Real.sqrt lambda * Real.sqrt (dotProduct theta theta)
  have hscalar :
      (Matrix.scalar Feature lambda : Matrix Feature Feature Real).PosDef :=
    scalarIdentity_posDef lambda hlambda
  have hV : V.PosDef := hscalar.add_posSemidef hG
  have hVz :
      V.mulVec z = (Matrix.scalar Feature lambda).mulVec theta := by
    exact posDef_mulVec_nonsingInv_mulVec V hV _
  have hscalar_theta :
      (Matrix.scalar Feature lambda).mulVec theta = lambda • theta := by
    ext i
    simp [Matrix.mulVec, Matrix.scalar_apply, Matrix.diagonal_apply, dotProduct]
  have hz_energy :
      matrixNorm V z ^ 2 = lambda * dotProduct z theta := by
    rw [matrixNorm_sq V hV, hVz, hscalar_theta]
    simp [dotProduct_smul, smul_eq_mul]
  have hV_energy :
      matrixNorm V z ^ 2 =
        lambda * dotProduct z z + dotProduct z (G.mulVec z) := by
    rw [matrixNorm_sq V hV]
    change dotProduct z ((Matrix.scalar Feature lambda + G).mulVec z) =
      lambda * dotProduct z z + dotProduct z (G.mulVec z)
    rw [Matrix.add_mulVec, dotProduct_add]
    have hscalar_z :
        (Matrix.scalar Feature lambda).mulVec z = lambda • z := by
      ext i
      simp [Matrix.mulVec, Matrix.scalar_apply, Matrix.diagonal_apply, dotProduct]
    rw [hscalar_z]
    simp [dotProduct_smul, smul_eq_mul]
  have hG_nonneg : 0 <= dotProduct z (G.mulVec z) :=
    hG.dotProduct_mulVec_nonneg z
  have hbase :
      lambda * dotProduct z z <= matrixNorm V z ^ 2 := by
    rw [hV_energy]
    linarith
  have hdot_self_z :
      dotProduct z z =
        (Finset.univ : Finset Feature).sum (fun i => z i ^ 2) := by
    simp [dotProduct, pow_two]
  have hdot_self_theta :
      dotProduct theta theta =
        (Finset.univ : Finset Feature).sum (fun i => theta i ^ 2) := by
    simp [dotProduct, pow_two]
  have hcs :
      dotProduct z theta <=
        Real.sqrt (dotProduct z z) * Real.sqrt (dotProduct theta theta) := by
    rw [hdot_self_z, hdot_self_theta]
    simpa [dotProduct] using
      Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset Feature) z theta
  have hzz_nonneg : 0 <= dotProduct z z := by
    rw [hdot_self_z]
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg (z i))
  have htt_nonneg : 0 <= dotProduct theta theta := by
    rw [hdot_self_theta]
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg (theta i))
  have hsqrt_lambda_nonneg : 0 <= Real.sqrt lambda := Real.sqrt_nonneg _
  have hsqrt_z_nonneg : 0 <= Real.sqrt (dotProduct z z) := Real.sqrt_nonneg _
  have hsqrt_theta_nonneg :
      0 <= Real.sqrt (dotProduct theta theta) := Real.sqrt_nonneg _
  have hmatrix_nonneg : 0 <= matrixNorm V z := Real.sqrt_nonneg _
  have hsqrt_z_le :
      Real.sqrt lambda * Real.sqrt (dotProduct z z) <= matrixNorm V z := by
    apply (sq_le_sq₀ (mul_nonneg hsqrt_lambda_nonneg hsqrt_z_nonneg)
      hmatrix_nonneg).mp
    rw [mul_pow, Real.sq_sqrt hlambda.le, Real.sq_sqrt hzz_nonneg]
    exact hbase
  have henergy_upper :
      matrixNorm V z ^ 2 <=
        lambda * Real.sqrt (dotProduct z z) *
          Real.sqrt (dotProduct theta theta) := by
    rw [hz_energy]
    calc
      lambda * dotProduct z theta <=
          lambda *
            (Real.sqrt (dotProduct z z) *
              Real.sqrt (dotProduct theta theta)) :=
        mul_le_mul_of_nonneg_left hcs hlambda.le
      _ = _ := by ring
  have hmatrix_sq_le :
      matrixNorm V z ^ 2 <=
        (Real.sqrt lambda * Real.sqrt (dotProduct theta theta)) *
          matrixNorm V z := by
    calc
      matrixNorm V z ^ 2 <=
          lambda * Real.sqrt (dotProduct z z) *
            Real.sqrt (dotProduct theta theta) := henergy_upper
      _ =
          (Real.sqrt lambda * Real.sqrt (dotProduct z z)) *
            (Real.sqrt lambda * Real.sqrt (dotProduct theta theta)) := by
        nlinarith [Real.sq_sqrt hlambda.le]
      _ <=
          matrixNorm V z *
            (Real.sqrt lambda * Real.sqrt (dotProduct theta theta)) := by
        exact mul_le_mul_of_nonneg_right hsqrt_z_le
          (mul_nonneg hsqrt_lambda_nonneg hsqrt_theta_nonneg)
      _ = _ := by ring
  by_cases hz : matrixNorm V z = 0
  · rw [hz]
    exact mul_nonneg hsqrt_lambda_nonneg hsqrt_theta_nonneg
  · have hzpos : 0 < matrixNorm V z := lt_of_le_of_ne hmatrix_nonneg (Ne.symm hz)
    have hcancel :
        matrixNorm V z <=
          Real.sqrt lambda * Real.sqrt (dotProduct theta theta) := by
      have hmul :
          matrixNorm V z * matrixNorm V z <=
            matrixNorm V z *
              (Real.sqrt lambda * Real.sqrt (dotProduct theta theta)) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmatrix_sq_le
      exact le_of_mul_le_mul_left hmul hzpos
    exact hcancel

/-- The standard scalar-regularized OFUL radius `noise radius + sqrt lambda * S`. -/
noncomputable def finiteHorizonScalarConfidenceRadius
    [Fintype Feature] [DecidableEq Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (R delta lambda S : Real) (n : Nat) (omega : Omega) : Real :=
  finiteHorizonConfidenceRadius
    (Matrix.scalar Feature lambda) feature R delta
      (Real.sqrt lambda * S) n omega

/--
The scalar regularization bias is uniformly bounded by `sqrt lambda * S`
whenever the true parameter has Euclidean length at most `S`.
-/
theorem finiteHorizon_scalarRegularizationBias_le
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real) (S : Real)
    (htheta : euclideanLength thetaStar <= S)
    (feature : Nat -> Omega -> Feature -> Real)
    (n : Nat) (omega : Omega) :
    matrixNorm
        (Matrix.scalar Feature lambda +
          finiteHorizonFeatureGram feature n omega)
        ((Matrix.scalar Feature lambda +
            finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
          ((Matrix.scalar Feature lambda).mulVec thetaStar)) <=
      Real.sqrt lambda * S := by
  exact
    (matrixNorm_nonsingInv_scalar_mulVec_le_sqrt_mul_euclideanLength
      lambda hlambda (finiteHorizonFeatureGram feature n omega)
      (finiteHorizonFeatureGram_posSemidef feature n omega)
      thetaStar).trans
      (mul_le_mul_of_nonneg_left htheta (Real.sqrt_nonneg lambda))

/--
Finite-horizon OFUL confidence ellipsoid with scalar ridge regularization.
The explicit bias premise of the general theorem is discharged from
`euclideanLength thetaStar <= S`.
-/
theorem
    measure_finiteHorizonScalarRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le
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
    (n : Nat)
    (hsubGaussian : forall i, i < n ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i)
        (constantSquaredVarianceProxy R i) mu)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hresponse : forall omega i, i < n ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega) :
    mu {omega |
        matrixNorm
            (Matrix.scalar Feature lambda +
              finiteHorizonFeatureGram feature n omega)
            (finiteHorizonRidgeEstimate
                (Matrix.scalar Feature lambda) feature response n omega -
              thetaStar) >
          finiteHorizonScalarConfidenceRadius
            feature R delta lambda S n omega} <=
      ENNReal.ofReal delta := by
  simpa [finiteHorizonScalarConfidenceRadius] using
    measure_finiteHorizonRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le
      mu (Matrix.scalar Feature lambda)
      (scalarIdentity_posDef lambda hlambda)
      thetaStar F feature response noise R hR projectionBound hfeature hnoise
      hprojectionBound_nonneg hprojectionBound n hsubGaussian delta hdelta
      hdelta_one (Real.sqrt lambda * S) hresponse
      (fun omega =>
        finiteHorizon_scalarRegularizationBias_le
          lambda hlambda thetaStar S htheta feature n omega)

end BanditRLProof.OFUL
