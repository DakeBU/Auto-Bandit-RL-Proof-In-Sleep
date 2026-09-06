import BanditRLProof.OFULGaussianSpectralMixture
import Mathlib.Analysis.Matrix.Order

/-!
# Positive-definite covariance Gaussian mixture for OFUL

This file transports the standard-Gaussian quadratic-exponential identity through
the square root of `V0⁻¹`.  For a positive-definite prior precision `V0` and a
positive-semidefinite Gram matrix `G`, it collects the transformed determinant and
quadratic form into the OFUL-facing matrices `V0 + G` and `(V0 + G)⁻¹`.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace MatrixOrder

variable {Feature : Type*} [Fintype Feature] [DecidableEq Feature]

private theorem inner_toEuclideanCLM_selfAdjoint
    (C : Matrix Feature Feature Real) (hC : C.IsHermitian)
    (x y : EuclideanSpace Real Feature) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := Real) C y⟫_ℝ =
      ⟪Matrix.toEuclideanCLM (𝕜 := Real) C x, y⟫_ℝ := by
  rw [Matrix.inner_toEuclideanCLM]
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM,
    Matrix.dotProduct_mulVec]
  have htranspose : Cᵀ = C := by
    ext i j
    simpa [Matrix.conjTranspose_apply] using
      congrFun (congrFun hC.eq i) j
  rw [← Matrix.vecMul_transpose, htranspose]
  exact dotProduct_comm _ _

private theorem inner_toEuclideanCLM_congruence
    (C G : Matrix Feature Feature Real) (hC : C.IsHermitian)
    (z : EuclideanSpace Real Feature) :
    ⟪Matrix.toEuclideanCLM (𝕜 := Real) C z,
        Matrix.toEuclideanCLM (𝕜 := Real) G
          (Matrix.toEuclideanCLM (𝕜 := Real) C z)⟫_ℝ =
      ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) (C * G * C) z⟫_ℝ := by
  calc
    ⟪Matrix.toEuclideanCLM (𝕜 := Real) C z,
        Matrix.toEuclideanCLM (𝕜 := Real) G
          (Matrix.toEuclideanCLM (𝕜 := Real) C z)⟫_ℝ =
      ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) C
        (Matrix.toEuclideanCLM (𝕜 := Real) G
          (Matrix.toEuclideanCLM (𝕜 := Real) C z))⟫_ℝ := by
      rw [real_inner_comm,
        inner_toEuclideanCLM_selfAdjoint C hC, real_inner_comm]
    _ = ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) (C * G * C) z⟫_ℝ := by
      congr 1
      apply WithLp.ofLp_injective
      simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc]

private theorem integral_exp_inner_sub_quadratic_multivariateGaussian_zero_inv_transformed
    (V0 G : Matrix Feature Feature Real) (hG : G.PosSemidef)
    (score : EuclideanSpace Real Feature) :
    let C := CFC.sqrt V0⁻¹
    integral
        (ProbabilityTheory.multivariateGaussian 0 V0⁻¹)
        (fun z : EuclideanSpace Real Feature =>
          Real.exp
            (⟪score, z⟫_ℝ -
              ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ / 2)) =
      (Real.sqrt (Matrix.det (1 + C * G * C)))⁻¹ *
        Real.exp
          ((Matrix.toEuclideanCLM (𝕜 := Real) C score) ⬝ᵥ
            (1 + C * G * C)⁻¹.mulVec
              (Matrix.toEuclideanCLM (𝕜 := Real) C score) / 2) := by
  dsimp only
  let C := CFC.sqrt V0⁻¹
  have hC : C.PosSemidef := by
    exact (CFC.sqrt_nonneg V0⁻¹).posSemidef
  have hCGC : (C * G * C).PosSemidef := by
    have hcongr := hG.conjTranspose_mul_mul_same C
    simpa only [hC.isHermitian.eq] using hcongr
  rw [ProbabilityTheory.multivariateGaussian, MeasureTheory.integral_map]
  · simp only [zero_add]
    have hpoint :
        (fun z : EuclideanSpace Real Feature =>
          Real.exp
            (⟪score, Matrix.toEuclideanCLM (𝕜 := Real) C z⟫_ℝ -
              ⟪Matrix.toEuclideanCLM (𝕜 := Real) C z,
                Matrix.toEuclideanCLM (𝕜 := Real) G
                  (Matrix.toEuclideanCLM (𝕜 := Real) C z)⟫_ℝ / 2)) =
          (fun z : EuclideanSpace Real Feature =>
            Real.exp
              (⟪Matrix.toEuclideanCLM (𝕜 := Real) C score, z⟫_ℝ -
                ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) (C * G * C) z⟫_ℝ /
                  2)) := by
      funext z
      rw [inner_toEuclideanCLM_selfAdjoint C hC.isHermitian,
        inner_toEuclideanCLM_congruence C G hC.isHermitian]
    rw [hpoint]
    exact integral_exp_inner_sub_quadratic_stdGaussian_det
      (C * G * C) hCGC
        (Matrix.toEuclideanCLM (𝕜 := Real) C score)
  · fun_prop
  · fun_prop

private theorem sqrt_inv_congruence_factorization
    (V0 G : Matrix Feature Feature Real) (hV0 : V0.PosDef) :
    let D := CFC.sqrt V0
    let C := CFC.sqrt V0⁻¹
    D * (1 + C * G * C) * D = V0 + G := by
  dsimp only
  let D := CFC.sqrt V0
  let C := CFC.sqrt V0⁻¹
  have hDpos : D.PosDef := hV0.isStrictlyPositive.sqrt.posDef
  have hdetD : IsUnit D.det :=
    D.isUnit_iff_isUnit_det.mp hDpos.isUnit
  have hCeq : C = D⁻¹ := by
    exact hV0.posSemidef.inv_sqrt.symm
  have hDC : D * C = 1 := by
    rw [hCeq, Matrix.mul_nonsing_inv D hdetD]
  have hCD : C * D = 1 := by
    rw [hCeq, Matrix.nonsing_inv_mul D hdetD]
  have hDD : D * D = V0 := by
    exact CFC.sqrt_mul_sqrt_self V0 hV0.posSemidef.nonneg
  calc
    D * (1 + C * G * C) * D =
        D * D + (D * C) * G * (C * D) := by
      noncomm_ring
    _ = V0 + G := by
      rw [hDD, hDC, hCD]
      simp

theorem det_one_add_sqrt_inv_congruence_eq_ratio
    (V0 G : Matrix Feature Feature Real) (hV0 : V0.PosDef) :
    let C := CFC.sqrt V0⁻¹
    Matrix.det (1 + C * G * C) =
      Matrix.det (V0 + G) / Matrix.det V0 := by
  dsimp only
  let D := CFC.sqrt V0
  let C := CFC.sqrt V0⁻¹
  have hfactor :
      D * (1 + C * G * C) * D = V0 + G :=
    sqrt_inv_congruence_factorization V0 G hV0
  have hDD : D * D = V0 := by
    exact CFC.sqrt_mul_sqrt_self V0 hV0.posSemidef.nonneg
  have hdetV0 : Matrix.det V0 ≠ 0 :=
    ne_of_gt hV0.det_pos
  have hdetDD :
      Matrix.det V0 = Matrix.det D * Matrix.det D := by
    calc
      Matrix.det V0 = Matrix.det (D * D) := by rw [hDD]
      _ = Matrix.det D * Matrix.det D := by rw [Matrix.det_mul]
  have hdetFactor :
      Matrix.det (V0 + G) =
        Matrix.det D * Matrix.det (1 + C * G * C) * Matrix.det D := by
    calc
      Matrix.det (V0 + G) =
          Matrix.det (D * (1 + C * G * C) * D) := by rw [hfactor]
      _ = Matrix.det D * Matrix.det (1 + C * G * C) * Matrix.det D := by
        rw [Matrix.det_mul, Matrix.det_mul]
  apply (eq_div_iff hdetV0).2
  rw [hdetDD, hdetFactor]
  ring

theorem sqrt_inv_congruence_inverse
    (V0 G : Matrix Feature Feature Real) (hV0 : V0.PosDef) :
    let C := CFC.sqrt V0⁻¹
    C * (1 + C * G * C)⁻¹ * C = (V0 + G)⁻¹ := by
  dsimp only
  let D := CFC.sqrt V0
  let C := CFC.sqrt V0⁻¹
  let B := 1 + C * G * C
  have hCeq : C = D⁻¹ := by
    exact hV0.posSemidef.inv_sqrt.symm
  have hfactor : D * B * D = V0 + G := by
    exact sqrt_inv_congruence_factorization V0 G hV0
  calc
    C * B⁻¹ * C = D⁻¹ * B⁻¹ * D⁻¹ := by rw [hCeq]
    _ = (D * B * D)⁻¹ := by
      symm
      calc
        (D * B * D)⁻¹ = D⁻¹ * (D * B)⁻¹ := by
          exact Matrix.mul_inv_rev (D * B) D
        _ = D⁻¹ * (B⁻¹ * D⁻¹) := by
          rw [Matrix.mul_inv_rev]
        _ = D⁻¹ * B⁻¹ * D⁻¹ := by
          rw [Matrix.mul_assoc]
    _ = (V0 + G)⁻¹ := by rw [hfactor]

theorem dotProduct_sqrt_inv_congruence_inverse
    (V0 G : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (score : EuclideanSpace Real Feature) :
    let C := CFC.sqrt V0⁻¹
    (Matrix.toEuclideanCLM (𝕜 := Real) C score) ⬝ᵥ
        (1 + C * G * C)⁻¹.mulVec
          (Matrix.toEuclideanCLM (𝕜 := Real) C score) =
      score ⬝ᵥ (V0 + G)⁻¹.mulVec score := by
  dsimp only
  let C := CFC.sqrt V0⁻¹
  let B := 1 + C * G * C
  have hC : C.PosSemidef := by
    exact (CFC.sqrt_nonneg V0⁻¹).posSemidef
  have hinv : C * B⁻¹ * C = (V0 + G)⁻¹ := by
    exact sqrt_inv_congruence_inverse V0 G hV0
  rw [← Matrix.inner_toEuclideanCLM, ← Matrix.inner_toEuclideanCLM]
  calc
    ⟪Matrix.toEuclideanCLM (𝕜 := Real) C score,
        Matrix.toEuclideanCLM (𝕜 := Real) B⁻¹
          (Matrix.toEuclideanCLM (𝕜 := Real) C score)⟫_ℝ =
      ⟪score, Matrix.toEuclideanCLM (𝕜 := Real) C
        (Matrix.toEuclideanCLM (𝕜 := Real) B⁻¹
          (Matrix.toEuclideanCLM (𝕜 := Real) C score))⟫_ℝ := by
      rw [real_inner_comm,
        inner_toEuclideanCLM_selfAdjoint C hC.isHermitian, real_inner_comm]
    _ = ⟪score,
        Matrix.toEuclideanCLM (𝕜 := Real) (C * B⁻¹ * C) score⟫_ℝ := by
      congr 1
      apply WithLp.ofLp_injective
      simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc]
    _ = ⟪score,
        Matrix.toEuclideanCLM (𝕜 := Real) (V0 + G)⁻¹ score⟫_ℝ := by
      rw [hinv]

theorem integral_exp_inner_sub_quadratic_multivariateGaussian_zero_inv_detRatio
    (V0 G : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (hG : G.PosSemidef) (score : EuclideanSpace Real Feature) :
    integral
        (ProbabilityTheory.multivariateGaussian 0 V0⁻¹)
        (fun z : EuclideanSpace Real Feature =>
          Real.exp
            (⟪score, z⟫_ℝ -
              ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ / 2)) =
      (Real.sqrt (Matrix.det (V0 + G) / Matrix.det V0))⁻¹ *
        Real.exp
          (score ⬝ᵥ (V0 + G)⁻¹.mulVec score / 2) := by
  rw [
    integral_exp_inner_sub_quadratic_multivariateGaussian_zero_inv_transformed
      V0 G hG score,
    det_one_add_sqrt_inv_congruence_eq_ratio V0 G hV0,
    dotProduct_sqrt_inv_congruence_inverse V0 G hV0 score]

theorem integral_exp_inner_sub_quadratic_multivariateGaussian_zero_inv
    (V0 G : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (hG : G.PosSemidef) (score : EuclideanSpace Real Feature) :
    integral
        (ProbabilityTheory.multivariateGaussian 0 V0⁻¹)
        (fun z : EuclideanSpace Real Feature =>
          Real.exp
            (⟪score, z⟫_ℝ -
              ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ / 2)) =
      Real.sqrt (Matrix.det V0 / Matrix.det (V0 + G)) *
        Real.exp
          (score ⬝ᵥ (V0 + G)⁻¹.mulVec score / 2) := by
  rw [
    integral_exp_inner_sub_quadratic_multivariateGaussian_zero_inv_detRatio
      V0 G hV0 hG score]
  congr 1
  have hV0det : 0 < Matrix.det V0 := hV0.det_pos
  have hsumdet : 0 < Matrix.det (V0 + G) :=
    (hV0.add_posSemidef hG).det_pos
  rw [Real.sqrt_div (le_of_lt hsumdet),
    Real.sqrt_div (le_of_lt hV0det)]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hV0det),
    ne_of_gt (Real.sqrt_pos.2 hsumdet)]

end BanditRLProof.OFUL
