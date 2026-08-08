import BanditRLProof.OFULGaussianCovarianceMixture
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Joint measurability for the OFUL Gaussian mixture

This file packages the random-score/random-Gram quadratic exponential on the
product of a sample space and a finite-dimensional Gaussian parameter space.
It proves the joint measurable surface needed by Tonelli and exposes both a
generic product-measure identity and the `N(0, V0⁻¹)` specialization.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace MatrixOrder

variable {Omega Feature : Type*}
  [MeasurableSpace Omega]
  [Fintype Feature] [DecidableEq Feature]

/-- The quadratic exponential mixed over the Gaussian direction in OFUL. -/
noncomputable def gaussianQuadraticExponential
    (score : Omega -> EuclideanSpace Real Feature)
    (gram : Omega -> Matrix Feature Feature Real)
    (p : Omega × EuclideanSpace Real Feature) : Real :=
  Real.exp
    (⟪score p.1, p.2⟫_ℝ -
      ⟪p.2, Matrix.toEuclideanCLM (𝕜 := Real) (gram p.1) p.2⟫_ℝ / 2)

omit [DecidableEq Feature] in
private theorem measurable_gaussianQuadraticExponential_dot
    (score : Omega -> EuclideanSpace Real Feature)
    (gram : Omega -> Matrix Feature Feature Real)
    (hscore : Measurable score)
    (hgram : forall i j, Measurable (fun omega => gram omega i j)) :
    Measurable
      (fun p : Omega × EuclideanSpace Real Feature =>
        Real.exp
          ((WithLp.ofLp (score p.1)) ⬝ᵥ (WithLp.ofLp p.2) -
            (WithLp.ofLp p.2) ⬝ᵥ
                (gram p.1).mulVec (WithLp.ofLp p.2) / 2)) := by
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/--
Joint measurability of the quadratic exponential from measurable random
scores and coordinatewise measurable random Gram matrices.
-/
theorem measurable_gaussianQuadraticExponential
    (score : Omega -> EuclideanSpace Real Feature)
    (gram : Omega -> Matrix Feature Feature Real)
    (hscore : Measurable score)
    (hgram : forall i j, Measurable (fun omega => gram omega i j)) :
    Measurable (gaussianQuadraticExponential score gram) := by
  change Measurable
    (fun p : Omega × EuclideanSpace Real Feature =>
      Real.exp
        (⟪score p.1, p.2⟫_ℝ -
          ⟪p.2, Matrix.toEuclideanCLM (𝕜 := Real) (gram p.1) p.2⟫_ℝ / 2))
  have hdot :=
    measurable_gaussianQuadraticExponential_dot score gram hscore hgram
  simpa [EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.inner_toEuclideanCLM, dotProduct_comm] using hdot

/-- The nonnegative extended-real surface used by Tonelli. -/
noncomputable def gaussianQuadraticExponentialENNReal
    (score : Omega -> EuclideanSpace Real Feature)
    (gram : Omega -> Matrix Feature Feature Real)
    (p : Omega × EuclideanSpace Real Feature) : ENNReal :=
  ENNReal.ofReal (gaussianQuadraticExponential score gram p)

/-- Joint measurability of the `ENNReal` Tonelli surface. -/
theorem measurable_gaussianQuadraticExponentialENNReal
    (score : Omega -> EuclideanSpace Real Feature)
    (gram : Omega -> Matrix Feature Feature Real)
    (hscore : Measurable score)
    (hgram : forall i j, Measurable (fun omega => gram omega i j)) :
    Measurable (gaussianQuadraticExponentialENNReal score gram) :=
  (measurable_gaussianQuadraticExponential score gram hscore hgram).ennreal_ofReal

/-- Tonelli for the quadratic exponential under an arbitrary `SFinite` parameter law. -/
theorem lintegral_gaussianQuadraticExponentialENNReal_prod
    (mu : Measure Omega) (nu : Measure (EuclideanSpace Real Feature))
    [SFinite nu]
    (score : Omega -> EuclideanSpace Real Feature)
    (gram : Omega -> Matrix Feature Feature Real)
    (hscore : Measurable score)
    (hgram : forall i j, Measurable (fun omega => gram omega i j)) :
    ∫⁻ p, gaussianQuadraticExponentialENNReal score gram p ∂mu.prod nu =
      ∫⁻ omega, ∫⁻ theta,
        gaussianQuadraticExponentialENNReal score gram (omega, theta) ∂nu ∂mu := by
  exact MeasureTheory.lintegral_prod _
    (measurable_gaussianQuadraticExponentialENNReal
      score gram hscore hgram).aemeasurable

/-- Tonelli specialized to the `N(0, V0⁻¹)` parameter law used by OFUL. -/
theorem lintegral_gaussianQuadraticExponentialENNReal_prod_multivariateGaussian_zero_inv
    (mu : Measure Omega) (V0 : Matrix Feature Feature Real)
    (score : Omega -> EuclideanSpace Real Feature)
    (gram : Omega -> Matrix Feature Feature Real)
    (hscore : Measurable score)
    (hgram : forall i j, Measurable (fun omega => gram omega i j)) :
    ∫⁻ p, gaussianQuadraticExponentialENNReal score gram p
        ∂mu.prod (ProbabilityTheory.multivariateGaussian 0 V0⁻¹) =
      ∫⁻ omega, ∫⁻ theta,
        gaussianQuadraticExponentialENNReal score gram (omega, theta)
          ∂ProbabilityTheory.multivariateGaussian 0 V0⁻¹ ∂mu := by
  exact lintegral_gaussianQuadraticExponentialENNReal_prod
    mu (ProbabilityTheory.multivariateGaussian 0 V0⁻¹)
      score gram hscore hgram

end BanditRLProof.OFUL
