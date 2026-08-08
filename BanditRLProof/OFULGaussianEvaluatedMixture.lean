import BanditRLProof.OFULFiniteHorizonScoreGram
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Evaluated Gaussian mixtures for finite-horizon OFUL scores

This module evaluates the inner Gaussian direction integral in the
finite-horizon score/variance-Gram mixture and transports the product-space
bound to the determinant-ratio inverse-Gram exponential.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace MatrixOrder

variable {Omega Feature : Type*}

/--
The positive-semidefinite Gaussian quadratic exponential is integrable.
Fernique supplies a square-exponential envelope for the linear term.
-/
theorem integrable_exp_inner_sub_quadratic_multivariateGaussian_zero_inv
    [Fintype Feature] [DecidableEq Feature]
    (V0 G : Matrix Feature Feature Real)
    (hG : G.PosSemidef) (score : EuclideanSpace Real Feature) :
    Integrable
      (fun z : EuclideanSpace Real Feature =>
        Real.exp
          (⟪score, z⟫_ℝ -
            ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ / 2))
      (ProbabilityTheory.multivariateGaussian 0 V0⁻¹) := by
  let nu :=
    ProbabilityTheory.multivariateGaussian
      (0 : EuclideanSpace Real Feature) V0⁻¹
  obtain ⟨C, hC, hFernique⟩ :=
    IsGaussian.exists_integrable_exp_sq nu
  have hdom :
      Integrable
        (fun z : EuclideanSpace Real Feature =>
          Real.exp (‖score‖ ^ 2 / (4 * C)) *
            Real.exp (C * ‖z‖ ^ 2))
        nu := by
    exact hFernique.const_mul (Real.exp (‖score‖ ^ 2 / (4 * C)))
  refine Integrable.mono' hdom (by fun_prop) ?_
  exact Filter.Eventually.of_forall (fun z => by
    have hquad :
        0 <=
          ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ := by
      rw [Matrix.inner_toEuclideanCLM]
      have hnonneg := hG.dotProduct_mulVec_nonneg (WithLp.ofLp z)
      have hstar : star (WithLp.ofLp z) = WithLp.ofLp z := by
        funext i
        simp
      simpa [hstar] using hnonneg
    have hinner :
        ⟪score, z⟫_ℝ <= ‖score‖ * ‖z‖ :=
      real_inner_le_norm score z
    have hyoung :
        ‖score‖ * ‖z‖ <=
          C * ‖z‖ ^ 2 + ‖score‖ ^ 2 / (4 * C) := by
      have h :=
        two_mul_le_add_mul_sq
          (a := ‖z‖) (b := ‖score‖) (ε := 2 * C) (by positivity)
      calc
        ‖score‖ * ‖z‖ =
            (2 * ‖z‖ * ‖score‖) / 2 := by ring
        _ <=
            ((2 * C) * ‖z‖ ^ 2 +
              (2 * C)⁻¹ * ‖score‖ ^ 2) / 2 := by
              exact div_le_div_of_nonneg_right h (by norm_num)
        _ =
            C * ‖z‖ ^ 2 + ‖score‖ ^ 2 / (4 * C) := by
              field_simp [ne_of_gt hC]
              ring
    have hexponent :
        ⟪score, z⟫_ℝ -
            ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ / 2 <=
          ‖score‖ ^ 2 / (4 * C) + C * ‖z‖ ^ 2 := by
      calc
        ⟪score, z⟫_ℝ -
              ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ / 2
            <= ⟪score, z⟫_ℝ := by linarith
        _ <= ‖score‖ * ‖z‖ := hinner
        _ <= C * ‖z‖ ^ 2 + ‖score‖ ^ 2 / (4 * C) := hyoung
        _ = ‖score‖ ^ 2 / (4 * C) + C * ‖z‖ ^ 2 := by ring
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp
          (⟪score, z⟫_ℝ -
            ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ / 2) <=
          Real.exp
            (‖score‖ ^ 2 / (4 * C) + C * ‖z‖ ^ 2) :=
        Real.exp_le_exp.mpr hexponent
      _ =
          Real.exp (‖score‖ ^ 2 / (4 * C)) *
            Real.exp (C * ‖z‖ ^ 2) := Real.exp_add _ _)

/--
The `ENNReal` Gaussian direction integral equals the completed-square
determinant-ratio expression.
-/
theorem lintegral_gaussianQuadraticExponentialENNReal_multivariateGaussian_zero_inv
    [Fintype Feature] [DecidableEq Feature]
    (V0 G : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (hG : G.PosSemidef) (score : EuclideanSpace Real Feature) :
    ∫⁻ z : EuclideanSpace Real Feature,
        ENNReal.ofReal
          (Real.exp
            (⟪score, z⟫_ℝ -
              ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) G z⟫_ℝ / 2))
      ∂ProbabilityTheory.multivariateGaussian 0 V0⁻¹ =
      ENNReal.ofReal
        (Real.sqrt (Matrix.det V0 / Matrix.det (V0 + G)) *
          Real.exp
            (score ⬝ᵥ (V0 + G)⁻¹.mulVec score / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_inner_sub_quadratic_multivariateGaussian_zero_inv
      V0 G hG score)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  rw [integral_exp_inner_sub_quadratic_multivariateGaussian_zero_inv
    V0 G hV0 hG score]

/--
The evaluated determinant-ratio inverse-Gram exponential for a finite-horizon
score and variance Gram.
-/
noncomputable def finiteHorizonDetRatioInvGramExponential
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
    (n : Nat) (omega : Omega) : ENNReal :=
  ENNReal.ofReal
    (Real.sqrt
        (Matrix.det V0 /
          Matrix.det
            (V0 +
              finiteHorizonVarianceGram feature varianceProxy n omega)) *
      Real.exp
        ((finiteHorizonNoiseScore feature noise n omega) ⬝ᵥ
            (V0 +
              finiteHorizonVarianceGram
                feature varianceProxy n omega)⁻¹.mulVec
              (finiteHorizonNoiseScore feature noise n omega) / 2))

/--
Samplewise evaluation of the finite-horizon Gaussian direction integral.
-/
theorem lintegral_gaussianQuadraticExponentialENNReal_finiteHorizon_multivariateGaussian_zero_inv
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
    (n : Nat) (omega : Omega) :
    ∫⁻ theta : EuclideanSpace Real Feature,
        gaussianQuadraticExponentialENNReal
          (finiteHorizonNoiseScore feature noise n)
          (finiteHorizonVarianceGram feature varianceProxy n)
          (omega, theta)
      ∂ProbabilityTheory.multivariateGaussian 0 V0⁻¹ =
      finiteHorizonDetRatioInvGramExponential
        V0 feature noise varianceProxy n omega := by
  simpa [gaussianQuadraticExponentialENNReal,
    gaussianQuadraticExponential,
    finiteHorizonDetRatioInvGramExponential] using
    lintegral_gaussianQuadraticExponentialENNReal_multivariateGaussian_zero_inv
      V0
      (finiteHorizonVarianceGram feature varianceProxy n omega)
      hV0
      (finiteHorizonVarianceGram_posSemidef
        feature varianceProxy n omega)
      (finiteHorizonNoiseScore feature noise n omega)

/--
The evaluated finite-horizon mixture is measurable in the sample.
-/
theorem measurable_finiteHorizonDetRatioInvGramExponential
    [MeasurableSpace Omega]
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
    (n : Nat)
    (hfeature : forall i j,
      Measurable (fun omega => feature i omega j))
    (hnoise : forall i, Measurable (noise i)) :
    Measurable
      (finiteHorizonDetRatioInvGramExponential
        V0 feature noise varianceProxy n) := by
  have hscore :
      Measurable (finiteHorizonNoiseScore feature noise n) :=
    measurable_finiteHorizonNoiseScore
      feature noise n hfeature hnoise
  have hgram : forall j k,
      Measurable
        (fun omega =>
          finiteHorizonVarianceGram feature varianceProxy n omega j k) :=
    measurable_finiteHorizonVarianceGram_apply
      feature varianceProxy n hfeature
  have hjoint :
      Measurable
        (gaussianQuadraticExponentialENNReal
          (finiteHorizonNoiseScore feature noise n)
          (finiteHorizonVarianceGram feature varianceProxy n)) :=
    measurable_gaussianQuadraticExponentialENNReal
      _ _ hscore hgram
  rw [show
      finiteHorizonDetRatioInvGramExponential
          V0 feature noise varianceProxy n =
        fun omega => ∫⁻ theta : EuclideanSpace Real Feature,
          gaussianQuadraticExponentialENNReal
            (finiteHorizonNoiseScore feature noise n)
            (finiteHorizonVarianceGram feature varianceProxy n)
            (omega, theta)
          ∂ProbabilityTheory.multivariateGaussian 0 V0⁻¹ by
    funext omega
    exact
      (lintegral_gaussianQuadraticExponentialENNReal_finiteHorizon_multivariateGaussian_zero_inv
        V0 hV0 feature noise varianceProxy n omega).symm]
  exact hjoint.lintegral_prod_right'

/--
The evaluated finite-horizon Gaussian mixture has `ENNReal` expectation at
most one.
-/
theorem lintegral_finiteHorizon_detRatio_invGramExponential_le_one
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
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
        (F i) (F.le i) (noise i) (varianceProxy i) mu) :
    ∫⁻ omega,
        finiteHorizonDetRatioInvGramExponential
          V0 feature noise varianceProxy n omega
      ∂mu <= 1 := by
  have hfeatureMeas : forall i j,
      Measurable (fun omega => feature i omega j) := by
    intro i j
    exact (hfeature i j).measurable.mono (F.le i) le_rfl
  have hnoiseMeas : forall i, Measurable (noise i) := by
    intro i
    have hi : StronglyMeasurable[F (i + 1)] (noise i) := by
      simpa using hnoise (i + 1)
    exact hi.measurable.mono (F.le (i + 1)) le_rfl
  have hscore :
      Measurable (finiteHorizonNoiseScore feature noise n) :=
    measurable_finiteHorizonNoiseScore
      feature noise n hfeatureMeas hnoiseMeas
  have hgram : forall j k,
      Measurable
        (fun omega =>
          finiteHorizonVarianceGram feature varianceProxy n omega j k) :=
    measurable_finiteHorizonVarianceGram_apply
      feature varianceProxy n hfeatureMeas
  calc
    ∫⁻ omega,
        finiteHorizonDetRatioInvGramExponential
          V0 feature noise varianceProxy n omega
      ∂mu =
        ∫⁻ omega, ∫⁻ theta,
          gaussianQuadraticExponentialENNReal
            (finiteHorizonNoiseScore feature noise n)
            (finiteHorizonVarianceGram feature varianceProxy n)
            (omega, theta)
          ∂ProbabilityTheory.multivariateGaussian 0 V0⁻¹ ∂mu := by
            apply lintegral_congr
            intro omega
            exact
              (lintegral_gaussianQuadraticExponentialENNReal_finiteHorizon_multivariateGaussian_zero_inv
                V0 hV0 feature noise varianceProxy n omega).symm
    _ =
        ∫⁻ p,
          gaussianQuadraticExponentialENNReal
            (finiteHorizonNoiseScore feature noise n)
            (finiteHorizonVarianceGram feature varianceProxy n) p
          ∂mu.prod
            (ProbabilityTheory.multivariateGaussian 0 V0⁻¹) := by
              symm
              exact
                lintegral_gaussianQuadraticExponentialENNReal_prod_multivariateGaussian_zero_inv
                  mu V0
                  (finiteHorizonNoiseScore feature noise n)
                  (finiteHorizonVarianceGram feature varianceProxy n)
                  hscore hgram
    _ <= 1 :=
      lintegral_gaussianQuadraticExponentialENNReal_finiteHorizon_prod_multivariateGaussian_zero_inv_le_one
        mu V0 F feature noise varianceProxy projectionBound hfeature hnoise
        hprojectionBound_nonneg hprojectionBound n hsubGaussian

end BanditRLProof.OFUL
