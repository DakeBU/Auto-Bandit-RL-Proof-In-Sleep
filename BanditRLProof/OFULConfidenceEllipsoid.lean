import BanditRLProof.OFULSelfNormalizedMarkov

/-!
# Finite-horizon OFUL least-squares confidence ellipsoid

This module consumes the common-`R` vector self-normalized tail. It defines
the finite-horizon ridge estimator from scalar observations, proves its exact
error decomposition into the martingale score and regularization bias, and
transports the score tail to a parameter confidence ellipsoid.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp Set
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace MatrixOrder

variable {Omega Feature : Type*}

/-- Quadratic-form square root; it is a norm when the matrix is positive definite. -/
noncomputable def matrixNorm
    [Fintype Feature]
    (A : Matrix Feature Feature Real) (x : Feature -> Real) : Real :=
  Real.sqrt (x ⬝ᵥ A.mulVec x)

/-- Triangle inequality for the norm induced by a positive-definite matrix. -/
theorem matrixNorm_add_le
    [Fintype Feature] [DecidableEq Feature]
    (A : Matrix Feature Feature Real) (hA : A.PosDef)
    (x y : Feature -> Real) :
    matrixNorm A (x + y) <= matrixNorm A x + matrixNorm A y := by
  have hnorm (z : Feature -> Real) :
      matrixNorm A z =
        @norm (Feature -> Real) (A.toNormedAddCommGroup hA).toNorm z := by
    change Real.sqrt (z ⬝ᵥ A.mulVec z) =
      Real.sqrt ((A.mulVec z) ⬝ᵥ z)
    rw [dotProduct_comm]
  rw [hnorm, hnorm, hnorm]
  exact
    @norm_add_le (Feature -> Real)
      (A.toNormedAddCommGroup hA).toSeminormedAddCommGroup.toSeminormedAddGroup x y

/-- Triangle inequality for subtraction in a positive-definite matrix norm. -/
theorem matrixNorm_sub_le
    [Fintype Feature] [DecidableEq Feature]
    (A : Matrix Feature Feature Real) (hA : A.PosDef)
    (x y : Feature -> Real) :
    matrixNorm A (x - y) <= matrixNorm A x + matrixNorm A y := by
  have hnorm (z : Feature -> Real) :
      matrixNorm A z =
        @norm (Feature -> Real) (A.toNormedAddCommGroup hA).toNorm z := by
    change Real.sqrt (z ⬝ᵥ A.mulVec z) =
      Real.sqrt ((A.mulVec z) ⬝ᵥ z)
    rw [dotProduct_comm]
  rw [hnorm, hnorm, hnorm]
  exact
    @norm_sub_le (Feature -> Real)
      (A.toNormedAddCommGroup hA).toSeminormedAddCommGroup.toSeminormedAddGroup x y

/-- Squaring the positive-definite matrix norm recovers its quadratic form. -/
theorem matrixNorm_sq
    [Fintype Feature] [DecidableEq Feature]
    (A : Matrix Feature Feature Real) (hA : A.PosDef)
    (x : Feature -> Real) :
    matrixNorm A x ^ 2 = x ⬝ᵥ A.mulVec x := by
  exact Real.sq_sqrt (hA.posSemidef.dotProduct_mulVec_nonneg x)

/-- The finite-horizon sufficient statistic `sum_{i<n} x_i y_i`. -/
noncomputable def finiteHorizonResponseVector
    [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Feature -> Real :=
  fun j =>
    (Finset.range n).sum (fun i => feature i omega j * response i omega)

/-- Ridge least-squares estimate with deterministic positive-definite base. -/
noncomputable def finiteHorizonRidgeEstimate
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Feature -> Real :=
  (V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
    (finiteHorizonResponseVector feature response n omega)

/-- The squared self-normalized radius from the common-`R` Markov tail. -/
noncomputable def finiteHorizonConfidenceThreshold
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (R delta : Real) (n : Nat) (omega : Omega) : Real :=
  2 * R ^ 2 *
    Real.log
      (Real.sqrt
          (Matrix.det (V0 + finiteHorizonFeatureGram feature n omega) /
            Matrix.det V0) /
        delta)

/-- Confidence radius with an explicit deterministic regularization-bias cap. -/
noncomputable def finiteHorizonConfidenceRadius
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (R delta biasRadius : Real) (n : Nat) (omega : Omega) : Real :=
  Real.sqrt
      (finiteHorizonConfidenceThreshold V0 feature R delta n omega) +
    biasRadius

/--
Adding a positive-semidefinite Gram to a positive-definite base cannot reduce
the determinant ratio below one.
-/
theorem one_le_det_add_posSemidef_div_det
    [Fintype Feature] [DecidableEq Feature]
    (V0 G : Matrix Feature Feature Real)
    (hV0 : V0.PosDef) (hG : G.PosSemidef) :
    1 <= Matrix.det (V0 + G) / Matrix.det V0 := by
  let C := CFC.sqrt V0⁻¹
  have hC : C.PosSemidef := by
    exact (CFC.sqrt_nonneg V0⁻¹).posSemidef
  have hCGC : (C * G * C).PosSemidef := by
    have hcongr := hG.conjTranspose_mul_mul_same C
    simpa only [hC.isHermitian.eq] using hcongr
  rw [← det_one_add_sqrt_inv_congruence_eq_ratio V0 G hV0,
    det_one_add_posSemidef_eq_prod_eigenvalues (C * G * C) hCGC]
  exact Finset.one_le_prod (fun i hi => by
    linarith [hCGC.eigenvalues_nonneg i])

/-- The squared confidence threshold is nonnegative for `0 < delta <= 1`. -/
theorem finiteHorizonConfidenceThreshold_nonneg
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (feature : Nat -> Omega -> Feature -> Real)
    (R delta : Real) (n : Nat) (omega : Omega)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    0 <= finiteHorizonConfidenceThreshold V0 feature R delta n omega := by
  have hratio :
      1 <= Matrix.det
          (V0 + finiteHorizonFeatureGram feature n omega) /
        Matrix.det V0 :=
    one_le_det_add_posSemidef_div_det V0
      (finiteHorizonFeatureGram feature n omega) hV0
      (finiteHorizonFeatureGram_posSemidef feature n omega)
  have hsqrt :
      1 <= Real.sqrt
        (Matrix.det (V0 + finiteHorizonFeatureGram feature n omega) /
          Matrix.det V0) := Real.one_le_sqrt.mpr hratio
  have harg :
      1 <=
        Real.sqrt
            (Matrix.det (V0 + finiteHorizonFeatureGram feature n omega) /
              Matrix.det V0) /
          delta :=
    (one_le_div hdelta).2 (hdelta_one.trans hsqrt)
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg R))
    (Real.log_nonneg harg)

/--
Under the linear observation model, the response sufficient statistic is the
feature Gram applied to the true parameter plus the martingale-noise score.
-/
theorem finiteHorizonResponseVector_eq_featureGram_mulVec_add_noiseScore
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response noise : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega)
    (hresponse : forall i, i < n ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega) :
    finiteHorizonResponseVector feature response n omega =
      (finiteHorizonFeatureGram feature n omega).mulVec thetaStar +
        WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega) := by
  funext j
  have hmodel :
      (Finset.range n).sum (fun i =>
          feature i omega j * response i omega) =
        (Finset.range n).sum (fun i =>
          feature i omega j *
            (dotProduct thetaStar (feature i omega) + noise i omega)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hresponse i (Finset.mem_range.mp hi)]
  rw [finiteHorizonResponseVector, hmodel]
  simp only [mul_add, Finset.sum_add_distrib, Pi.add_apply]
  congr 1
  simp only [finiteHorizonFeatureGram, prefixFeatureGram, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Applying the nonsingular inverse of a positive-definite matrix cancels it. -/
theorem posDef_nonsingInv_mulVec_mulVec
    [Fintype Feature] [DecidableEq Feature]
    (A : Matrix Feature Feature Real) (hA : A.PosDef)
    (x : Feature -> Real) :
    A⁻¹.mulVec (A.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp hA.isUnit),
    Matrix.one_mulVec]

/-- A positive-definite matrix also cancels its inverse on the left. -/
theorem posDef_mulVec_nonsingInv_mulVec
    [Fintype Feature] [DecidableEq Feature]
    (A : Matrix Feature Feature Real) (hA : A.PosDef)
    (x : Feature -> Real) :
    A.mulVec (A⁻¹.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp hA.isUnit),
    Matrix.one_mulVec]

/--
The squared `A`-norm of `A⁻¹x` is the inverse quadratic form of `x`.
-/
theorem matrixNorm_nonsingInv_mulVec_sq
    [Fintype Feature] [DecidableEq Feature]
    (A : Matrix Feature Feature Real) (hA : A.PosDef)
    (x : Feature -> Real) :
    matrixNorm A (A⁻¹.mulVec x) ^ 2 = x ⬝ᵥ A⁻¹.mulVec x := by
  rw [matrixNorm_sq A hA,
    posDef_mulVec_nonsingInv_mulVec A hA x,
    dotProduct_comm]

/--
Exact ridge-estimation error decomposition into inverse-Gram noise score and
inverse-Gram regularization bias.
-/
theorem finiteHorizonRidgeEstimate_sub_eq_inverseScore_sub_inverseBias
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (thetaStar : Feature -> Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response noise : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega)
    (hresponse : forall i, i < n ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega) :
    finiteHorizonRidgeEstimate V0 feature response n omega - thetaStar =
      (V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
          (WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega)) -
        (V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
          (V0.mulVec thetaStar) := by
  let G := finiteHorizonFeatureGram feature n omega
  let V := V0 + G
  have hG : G.PosSemidef :=
    finiteHorizonFeatureGram_posSemidef feature n omega
  have hV : V.PosDef := hV0.add_posSemidef hG
  have htheta : V⁻¹.mulVec (V.mulVec thetaStar) = thetaStar :=
    posDef_nonsingInv_mulVec_mulVec V hV thetaStar
  rw [finiteHorizonRidgeEstimate,
    finiteHorizonResponseVector_eq_featureGram_mulVec_add_noiseScore
      thetaStar feature response noise n omega hresponse]
  change V⁻¹.mulVec
      (G.mulVec thetaStar +
        WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega)) -
      thetaStar =
    V⁻¹.mulVec
        (WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega)) -
      V⁻¹.mulVec (V0.mulVec thetaStar)
  calc
    _ = V⁻¹.mulVec
          (G.mulVec thetaStar +
            WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega)) -
        V⁻¹.mulVec (V.mulVec thetaStar) :=
      congrArg
        (fun z =>
          V⁻¹.mulVec
              (G.mulVec thetaStar +
                WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega)) -
            z)
        htheta.symm
    _ = V⁻¹.mulVec
          ((G.mulVec thetaStar +
              WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega)) -
            V.mulVec thetaStar) := by
      rw [Matrix.mulVec_sub]
    _ = V⁻¹.mulVec
          (WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega) -
            V0.mulVec thetaStar) := by
      congr 1
      rw [Matrix.add_mulVec]
      abel
    _ = _ := by
      rw [Matrix.mulVec_sub]

/--
Deterministic confidence decomposition: estimator error is bounded by the
self-normalized score plus the regularization-bias norm.
-/
theorem finiteHorizonRidgeEstimate_error_matrixNorm_le_score_add_bias
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (thetaStar : Feature -> Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response noise : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega)
    (hresponse : forall i, i < n ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega) :
    matrixNorm
        (V0 + finiteHorizonFeatureGram feature n omega)
        (finiteHorizonRidgeEstimate V0 feature response n omega - thetaStar) <=
      matrixNorm
          (V0 + finiteHorizonFeatureGram feature n omega)
          ((V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
            (WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega))) +
        matrixNorm
          (V0 + finiteHorizonFeatureGram feature n omega)
          ((V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
            (V0.mulVec thetaStar)) := by
  rw [finiteHorizonRidgeEstimate_sub_eq_inverseScore_sub_inverseBias
    V0 hV0 thetaStar feature response noise n omega hresponse]
  exact matrixNorm_sub_le _
    (hV0.add_posSemidef
      (finiteHorizonFeatureGram_posSemidef feature n omega)) _ _

/--
Pointwise transport from confidence-ellipsoid failure to the compiled
self-normalized score bad event.
-/
theorem
    selfNormalizedQuadratic_gt_of_ridgeEstimate_error_matrixNorm_gt_confidenceRadius
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (thetaStar : Feature -> Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response noise : Nat -> Omega -> Real)
    (R delta biasRadius : Real)
    (n : Nat) (omega : Omega)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hresponse : forall i, i < n ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega)
    (hbias :
      matrixNorm
          (V0 + finiteHorizonFeatureGram feature n omega)
          ((V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
            (V0.mulVec thetaStar)) <=
        biasRadius)
    (hbad :
      matrixNorm
          (V0 + finiteHorizonFeatureGram feature n omega)
          (finiteHorizonRidgeEstimate V0 feature response n omega -
            thetaStar) >
        finiteHorizonConfidenceRadius
          V0 feature R delta biasRadius n omega) :
    (finiteHorizonNoiseScore feature noise n omega) ⬝ᵥ
          (V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
            (finiteHorizonNoiseScore feature noise n omega) >
      finiteHorizonConfidenceThreshold V0 feature R delta n omega := by
  let V := V0 + finiteHorizonFeatureGram feature n omega
  let score : Feature -> Real :=
    WithLp.ofLp (finiteHorizonNoiseScore feature noise n omega)
  have hV : V.PosDef :=
    hV0.add_posSemidef
      (finiteHorizonFeatureGram_posSemidef feature n omega)
  have herror_le :
      matrixNorm V
          (finiteHorizonRidgeEstimate V0 feature response n omega -
            thetaStar) <=
        matrixNorm V (V⁻¹.mulVec score) + biasRadius := by
    have hbias_add :
        matrixNorm V (V⁻¹.mulVec score) +
            matrixNorm V (V⁻¹.mulVec (V0.mulVec thetaStar)) <=
          matrixNorm V (V⁻¹.mulVec score) + biasRadius :=
      add_le_add_right hbias _
    exact
      (finiteHorizonRidgeEstimate_error_matrixNorm_le_score_add_bias
        V0 hV0 thetaStar feature response noise n omega hresponse).trans
        hbias_add
  have hsqrt_lt :
      Real.sqrt
          (finiteHorizonConfidenceThreshold V0 feature R delta n omega) <
        matrixNorm V (V⁻¹.mulVec score) := by
    rw [finiteHorizonConfidenceRadius] at hbad
    linarith
  have hthreshold_nonneg :
      0 <= finiteHorizonConfidenceThreshold V0 feature R delta n omega :=
    finiteHorizonConfidenceThreshold_nonneg
      V0 hV0 feature R delta n omega hdelta hdelta_one
  have hsquared :
      finiteHorizonConfidenceThreshold V0 feature R delta n omega <
        matrixNorm V (V⁻¹.mulVec score) ^ 2 := by
    nlinarith [Real.sq_sqrt hthreshold_nonneg,
      Real.sqrt_nonneg
        (finiteHorizonConfidenceThreshold V0 feature R delta n omega),
      show 0 <= matrixNorm V (V⁻¹.mulVec score) by
        exact Real.sqrt_nonneg _]
  rw [matrixNorm_nonsingInv_mulVec_sq V hV score] at hsquared
  exact hsquared

/--
Finite-horizon OFUL least-squares confidence ellipsoid. With probability at
least `1 - delta`, the ridge-estimation error lies in the current Gram norm
inside the self-normalized radius plus the supplied regularization-bias cap.
-/
theorem
    measure_finiteHorizonRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (thetaStar : Feature -> Real)
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
    (biasRadius : Real)
    (hresponse : forall omega i, i < n ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega)
    (hbias : forall omega,
      matrixNorm
          (V0 + finiteHorizonFeatureGram feature n omega)
          ((V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
            (V0.mulVec thetaStar)) <=
        biasRadius) :
    mu {omega |
        matrixNorm
            (V0 + finiteHorizonFeatureGram feature n omega)
            (finiteHorizonRidgeEstimate V0 feature response n omega -
              thetaStar) >
          finiteHorizonConfidenceRadius
            V0 feature R delta biasRadius n omega} <=
      ENNReal.ofReal delta := by
  calc
    _ <=
        mu {omega |
          (finiteHorizonNoiseScore feature noise n omega) ⬝ᵥ
                (V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
                  (finiteHorizonNoiseScore feature noise n omega) >
            finiteHorizonConfidenceThreshold
              V0 feature R delta n omega} := by
      apply measure_mono
      intro omega hbad
      exact
        selfNormalizedQuadratic_gt_of_ridgeEstimate_error_matrixNorm_gt_confidenceRadius
          V0 hV0 thetaStar feature response noise R delta biasRadius n omega
          hdelta hdelta_one (hresponse omega) (hbias omega) hbad
    _ <= ENNReal.ofReal delta := by
      simpa [finiteHorizonConfidenceThreshold] using
        measure_finiteHorizon_selfNormalizedQuadratic_gt_two_mul_sq_mul_log_detRatio_div_le
          mu V0 hV0 F feature noise R hR projectionBound hfeature hnoise
          hprojectionBound_nonneg hprojectionBound n hsubGaussian delta hdelta

end BanditRLProof.OFUL
