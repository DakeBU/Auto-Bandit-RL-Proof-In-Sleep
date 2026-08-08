import BanditRLProof.OFULSelfNormalizedConfidence
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gaussian mixture identities for OFUL

This module develops the exact Gaussian quadratic-exponential integrals used
after the fixed-direction exponential-supermartingale bound. The scalar
identity is the normalization step needed before the finite-dimensional
spectral/product assembly.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal ProbabilityTheory

/--
The exact scalar quadratic-exponential integral under a standard Gaussian.

This is the one-coordinate completed-square identity used by the Gaussian
method of mixtures. The nonnegative quadratic coefficient is the scalar
eigenvalue contract that will arise from a positive-semidefinite Gram matrix.
-/
theorem integral_exp_linear_sub_quadratic_gaussianReal_zero_one
    (s q : Real) (hq : 0 <= q) :
    integral
        (ProbabilityTheory.gaussianReal 0 1)
        (fun x : Real => Real.exp (s * x - q * x ^ 2 / 2)) =
      (Real.sqrt (1 + q))⁻¹ *
        Real.exp (s ^ 2 / (2 * (1 + q))) := by
  let a : Real := 1 + q
  have ha : 0 < a := by
    dsimp [a]
    linarith
  let v : NNReal := ⟨a⁻¹, inv_nonneg.mpr ha.le⟩
  have hv : v ≠ 0 := by
    intro hv0
    have hcoe : (v : Real) = 0 := by rw [hv0]; rfl
    dsimp [v] at hcoe
    exact (inv_ne_zero (ne_of_gt ha)) hcoe
  let m : Real := s / a
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have hpoint : forall x : Real,
      ProbabilityTheory.gaussianPDFReal 0 1 x *
          Real.exp (s * x - q * x ^ 2 / 2) =
        (Real.sqrt a)⁻¹ * Real.exp (s ^ 2 / (2 * a)) *
          ProbabilityTheory.gaussianPDFReal m v x := by
    intro x
    rw [ProbabilityTheory.gaussianPDFReal_def,
      ProbabilityTheory.gaussianPDFReal_def]
    dsimp [m, v]
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hsqrt_a : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
    have hsqrt_two_pi : Real.sqrt (2 * Real.pi) ≠ 0 := by
      positivity
    have hsqrt_div :
        Real.sqrt (2 * Real.pi * a⁻¹) =
          Real.sqrt (2 * Real.pi) / Real.sqrt a := by
      rw [show 2 * Real.pi * a⁻¹ = (2 * Real.pi) / a by
        field_simp]
      exact Real.sqrt_div (by positivity : 0 <= 2 * Real.pi) a
    simp only [mul_one, sub_zero, hsqrt_div]
    have hconst :
        (Real.sqrt (2 * Real.pi))⁻¹ =
          (Real.sqrt a)⁻¹ *
            (Real.sqrt (2 * Real.pi) / Real.sqrt a)⁻¹ := by
      field_simp
    have hexponent :
        -x ^ 2 / 2 + (s * x - q * x ^ 2 / 2) =
          s ^ 2 / (2 * a) -
            (x - s / a) ^ 2 / (2 * a⁻¹) := by
      have haq : 1 + q ≠ 0 := by linarith
      dsimp [a]
      field_simp [haq]
      ring
    calc
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
            Real.exp (s * x - q * x ^ 2 / 2) =
          (Real.sqrt a)⁻¹ *
            (Real.sqrt (2 * Real.pi) / Real.sqrt a)⁻¹ *
              (Real.exp (-x ^ 2 / 2) *
                Real.exp (s * x - q * x ^ 2 / 2)) := by
        rw [hconst]
        ring
      _ = (Real.sqrt a)⁻¹ *
            (Real.sqrt (2 * Real.pi) / Real.sqrt a)⁻¹ *
              Real.exp (-x ^ 2 / 2 + (s * x - q * x ^ 2 / 2)) := by
        rw [Real.exp_add]
      _ = (Real.sqrt a)⁻¹ *
            (Real.sqrt (2 * Real.pi) / Real.sqrt a)⁻¹ *
              Real.exp
                (s ^ 2 / (2 * a) -
                  (x - s / a) ^ 2 / (2 * a⁻¹)) := by
        rw [hexponent]
      _ = (Real.sqrt a)⁻¹ * Real.exp (s ^ 2 / (2 * a)) *
            ((Real.sqrt (2 * Real.pi) / Real.sqrt a)⁻¹ *
              Real.exp (-(x - s / a) ^ 2 / (2 * a⁻¹))) := by
        rw [show
          s ^ 2 / (2 * a) - (x - s / a) ^ 2 / (2 * a⁻¹) =
            s ^ 2 / (2 * a) +
              (-(x - s / a) ^ 2 / (2 * a⁻¹)) by ring,
          Real.exp_add]
        ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul,
    ProbabilityTheory.integral_gaussianPDFReal_eq_one m hv, mul_one]

/--
Finite independent-coordinate version of the scalar completed-square identity.

The right-hand side is deliberately left as a finite product. The following
matrix-facing lemmas identify that product with the square-root determinant
factor and the exponential term with an inverse-diagonal quadratic form.
-/
theorem integral_exp_sum_linear_sub_diagonal_quadratic_pi_gaussianReal
    {Feature : Type*} [Fintype Feature]
    (score quadratic : Feature -> Real)
    (hquadratic : forall i, 0 <= quadratic i) :
    integral
        (Measure.pi (fun _ : Feature =>
          ProbabilityTheory.gaussianReal 0 1))
        (fun z : Feature -> Real =>
          Real.exp
            (Finset.univ.sum (fun i =>
              score i * z i - quadratic i * (z i) ^ 2 / 2))) =
      Finset.univ.prod (fun i =>
        (Real.sqrt (1 + quadratic i))⁻¹ *
          Real.exp (score i ^ 2 / (2 * (1 + quadratic i)))) := by
  simp_rw [Real.exp_sum]
  have hprod :
      integral
          (Measure.pi (fun _ : Feature =>
            ProbabilityTheory.gaussianReal 0 1))
          (fun z : Feature -> Real =>
            Finset.univ.prod (fun i =>
              Real.exp
                (score i * z i - quadratic i * (z i) ^ 2 / 2))) =
        Finset.univ.prod (fun i =>
          integral
            (ProbabilityTheory.gaussianReal 0 1)
            (fun x : Real =>
              Real.exp
                (score i * x - quadratic i * x ^ 2 / 2))) := by
    exact MeasureTheory.integral_fintype_prod_eq_prod
      (fun i (x : Real) =>
        Real.exp (score i * x - quadratic i * x ^ 2 / 2))
  rw [hprod]
  congr with i
  exact integral_exp_linear_sub_quadratic_gaussianReal_zero_one
    (score i) (quadratic i) (hquadratic i)

/--
Finite product identity with the normalization and exponential factors
collected separately.
-/
theorem integral_exp_sum_linear_sub_diagonal_quadratic_pi_gaussianReal_eq
    {Feature : Type*} [Fintype Feature]
    (score quadratic : Feature -> Real)
    (hquadratic : forall i, 0 <= quadratic i) :
    integral
        (Measure.pi (fun _ : Feature =>
          ProbabilityTheory.gaussianReal 0 1))
        (fun z : Feature -> Real =>
          Real.exp
            (Finset.univ.sum (fun i =>
              score i * z i - quadratic i * (z i) ^ 2 / 2))) =
      (Finset.univ.prod (fun i =>
        Real.sqrt (1 + quadratic i)))⁻¹ *
        Real.exp
          (Finset.univ.sum (fun i =>
            score i ^ 2 / (2 * (1 + quadratic i)))) := by
  rw [integral_exp_sum_linear_sub_diagonal_quadratic_pi_gaussianReal
    score quadratic hquadratic]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Real.exp_sum]

/--
Diagonal matrix form of the finite Gaussian quadratic-exponential identity.

This is the diagonal-coordinate determinant-ratio and inverse-quadratic
expression intended for later transport through a PSD matrix eigenbasis.
-/
theorem integral_exp_sum_linear_sub_diagonal_quadratic_pi_gaussianReal_det
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (score quadratic : Feature -> Real)
    (hquadratic : forall i, 0 <= quadratic i) :
    integral
        (Measure.pi (fun _ : Feature =>
          ProbabilityTheory.gaussianReal 0 1))
        (fun z : Feature -> Real =>
          Real.exp
            (Finset.univ.sum (fun i =>
              score i * z i - quadratic i * (z i) ^ 2 / 2))) =
      (Real.sqrt
        (Matrix.det
          (Matrix.diagonal (fun i : Feature =>
            1 + quadratic i))))⁻¹ *
        Real.exp
          (score ⬝ᵥ
            ((Matrix.diagonal (fun i : Feature =>
              1 + quadratic i))⁻¹).mulVec score / 2) := by
  rw [integral_exp_sum_linear_sub_diagonal_quadratic_pi_gaussianReal_eq
    score quadratic hquadratic]
  have hdiag_nonneg : forall i : Feature, 0 <= 1 + quadratic i := by
    intro i
    linarith [hquadratic i]
  have hdiag_ne : forall i : Feature, 1 + quadratic i ≠ 0 := by
    intro i
    linarith [hquadratic i]
  have hdet :
      Real.sqrt
          (Matrix.det
            (Matrix.diagonal (fun i : Feature =>
              1 + quadratic i))) =
        Finset.univ.prod (fun i =>
          Real.sqrt (1 + quadratic i)) := by
    rw [Matrix.det_diagonal]
    exact Real.sqrt_prod Finset.univ (fun i _ => hdiag_nonneg i)
  have hdiag_unit :
      IsUnit (fun i : Feature => 1 + quadratic i) := by
    rw [Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr (hdiag_ne i)
  have hdiag_inverse :
      Ring.inverse (fun i : Feature => 1 + quadratic i) =
        fun i => (1 + quadratic i)⁻¹ := by
    funext i
    apply eq_inv_of_mul_eq_one_right
    simpa only [Pi.mul_apply, Pi.one_apply] using
      congrFun
        (Ring.mul_inverse_cancel
          (fun i : Feature => 1 + quadratic i) hdiag_unit) i
  have hquad :
      score ⬝ᵥ
          ((Matrix.diagonal (fun i : Feature =>
            1 + quadratic i))⁻¹).mulVec score =
        Finset.univ.sum (fun i =>
          score i ^ 2 / (1 + quadratic i)) := by
    rw [Matrix.inv_diagonal, hdiag_inverse]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Matrix.mulVec_diagonal]
    ring
  have hsum :
      Finset.univ.sum (fun i =>
          score i ^ 2 / (2 * (1 + quadratic i))) =
        Finset.univ.sum (fun i =>
          score i ^ 2 / (1 + quadratic i)) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hdiag_ne i]
  rw [hdet, hquad, hsum]

end OFUL
end BanditRLProof
