import BanditRLProof.OFULSelfNormalizedConfidence
import BanditRLProof.OFULGaussianMixtureMeasurability

/-!
# Finite-horizon score and variance Gram for OFUL

This module identifies the scalar compensated process from the fixed-direction
conditional-MGF theorem with the random score/random-Gram quadratic
exponential used by the Gaussian method of mixtures.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace MatrixOrder

variable {Omega Feature : Type*}

/-- The finite-horizon martingale score `sum_{i<n} x_i eta_i`. -/
noncomputable def finiteHorizonNoiseScore
    [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : EuclideanSpace Real Feature :=
  WithLp.toLp 2 (fun j =>
    (Finset.range n).sum (fun i => feature i omega j * noise i omega))

/-- Feature rescaling whose ordinary Gram is weighted by the variance proxy. -/
noncomputable def varianceWeightedFeature
    (feature : Nat -> Omega -> Feature -> Real)
    (varianceProxy : Nat -> NNReal)
    (i : Nat) (omega : Omega) (j : Feature) : Real :=
  Real.sqrt (((varianceProxy i : NNReal) : Real)) * feature i omega j

/-- The finite-horizon variance-weighted Gram `sum_{i<n} c_i x_i x_i^T`. -/
noncomputable def finiteHorizonVarianceGram
    [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (varianceProxy : Nat -> NNReal)
    (n : Nat) (omega : Omega) : Matrix Feature Feature Real :=
  prefixFeatureGram
    (fun i => varianceWeightedFeature feature varianceProxy i omega) n

/-- The score inner product is the finite sum of projected noise increments. -/
theorem inner_finiteHorizonNoiseScore_eq_sum_projection_mul_noise
    [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega)
    (theta : EuclideanSpace Real Feature) :
    ⟪finiteHorizonNoiseScore feature noise n omega, theta⟫_Real =
      (Finset.range n).sum (fun i =>
        dotProduct (WithLp.ofLp theta) (feature i omega) * noise i omega) := by
  change
    dotProduct (WithLp.ofLp theta)
        (fun j =>
          (Finset.range n).sum
            (fun i => feature i omega j * noise i omega)) =
      (Finset.range n).sum (fun i =>
        dotProduct (WithLp.ofLp theta) (feature i omega) * noise i omega)
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The weighted Gram quadratic form is the variance-weighted projection sum. -/
theorem finiteHorizonVarianceGram_quadraticForm_eq_sum
    [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (varianceProxy : Nat -> NNReal)
    (n : Nat) (omega : Omega) (theta : Feature -> Real) :
    quadraticForm
        (finiteHorizonVarianceGram feature varianceProxy n omega) theta =
      (Finset.range n).sum (fun i =>
        (((varianceProxy i : NNReal) : Real)) *
          (dotProduct theta (feature i omega)) ^ 2) := by
  rw [finiteHorizonVarianceGram,
    prefixFeatureGram_quadraticForm_eq_sum_sq]
  apply Finset.sum_congr rfl
  intro i hi
  have hnonneg :
      0 <= (((varianceProxy i : NNReal) : Real)) := by positivity
  rw [show
      (Finset.univ : Finset Feature).sum (fun j =>
          varianceWeightedFeature feature varianceProxy i omega j * theta j) =
        Real.sqrt (((varianceProxy i : NNReal) : Real)) *
          dotProduct theta (feature i omega) by
    simp only [varianceWeightedFeature, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring]
  rw [mul_pow, Real.sq_sqrt hnonneg]

/-- The finite-horizon variance Gram is positive semidefinite. -/
theorem finiteHorizonVarianceGram_posSemidef
    [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (varianceProxy : Nat -> NNReal)
    (n : Nat) (omega : Omega) :
    (finiteHorizonVarianceGram feature varianceProxy n omega).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (prefixFeatureGram_isHermitian
      (fun i => varianceWeightedFeature feature varianceProxy i omega) n) ?_
  intro theta
  have hstar : star theta = theta := by
    funext i
    simp
  rw [hstar, dotProduct_mulVec_eq_quadraticForm,
    finiteHorizonVarianceGram_quadraticForm_eq_sum]
  exact Finset.sum_nonneg (fun i hi =>
    mul_nonneg (by positivity) (sq_nonneg _))

/-- Coordinatewise measurability of the finite-horizon variance Gram. -/
theorem measurable_finiteHorizonVarianceGram_apply
    [MeasurableSpace Omega] [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (varianceProxy : Nat -> NNReal)
    (n : Nat)
    (hfeature : forall i j, Measurable (fun omega => feature i omega j)) :
    forall j k,
      Measurable
        (fun omega =>
          finiteHorizonVarianceGram feature varianceProxy n omega j k) := by
  intro j k
  simp only [finiteHorizonVarianceGram, prefixFeatureGram,
    varianceWeightedFeature]
  fun_prop

/-- Measurability of the finite-horizon score from coordinatewise inputs. -/
theorem measurable_finiteHorizonNoiseScore
    [MeasurableSpace Omega] [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (n : Nat)
    (hfeature : forall i j, Measurable (fun omega => feature i omega j))
    (hnoise : forall i, Measurable (noise i)) :
    Measurable (finiteHorizonNoiseScore feature noise n) := by
  refine (WithLp.measurable_toLp 2 (Feature -> Real)).comp ?_
  fun_prop

/--
Pointwise identification of the fixed-direction compensated finite sum with
the random score/random-Gram quadratic exponent.
-/
theorem compensatedScore_eq_inner_sub_varianceGram
    [Fintype Feature] [DecidableEq Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
    (n : Nat) (omega : Omega)
    (theta : EuclideanSpace Real Feature) :
    (Finset.range (n + 1)).sum (fun t =>
      match t with
      | 0 => 0
      | i + 1 =>
          dotProduct (WithLp.ofLp theta) (feature i omega) * noise i omega -
            (((varianceProxy i : NNReal) : Real) *
              (dotProduct (WithLp.ofLp theta) (feature i omega)) ^ 2 / 2)) =
      ⟪finiteHorizonNoiseScore feature noise n omega, theta⟫_Real -
        ⟪theta,
          Matrix.toEuclideanCLM (𝕜 := Real)
            (finiteHorizonVarianceGram feature varianceProxy n omega)
            theta⟫_Real / 2 := by
  rw [Finset.sum_range_succ']
  simp only [inner_finiteHorizonNoiseScore_eq_sum_projection_mul_noise,
    Matrix.inner_toEuclideanCLM, dotProduct_mulVec_eq_quadraticForm,
    finiteHorizonVarianceGram_quadraticForm_eq_sum,
    Finset.sum_sub_distrib, Finset.sum_div]
  ring

/--
The fixed-direction conditional-MGF endpoint transported to the random
finite-horizon score and variance Gram.
-/
theorem finiteHorizonScoreVarianceGram_hasMGFUpperBoundAt
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
    (theta : EuclideanSpace Real Feature)
    (projectionBound : Nat -> Real)
    (hprojection : forall i,
      StronglyMeasurable[F i]
        (fun omega => dotProduct (WithLp.ofLp theta) (feature i omega)))
    (hnoise : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => noise i omega))
    (hprojectionBound_nonneg : forall i, 0 <= projectionBound i)
    (hprojectionBound : forall i omega,
      |dotProduct (WithLp.ofLp theta) (feature i omega)| <= projectionBound i)
    (n : Nat)
    (hsubGaussian : forall i, i < n ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i) (varianceProxy i) mu) :
    Concentration.HasMGFUpperBoundAt
      (fun omega =>
        ⟪finiteHorizonNoiseScore feature noise n omega, theta⟫_Real -
          ⟪theta,
            Matrix.toEuclideanCLM (𝕜 := Real)
              (finiteHorizonVarianceGram feature varianceProxy n omega)
              theta⟫_Real / 2)
      1 0 mu := by
  have h :=
    fixedDirectionCompensatedScore_hasMGFUpperBoundAt
      mu F feature noise varianceProxy (WithLp.ofLp theta)
      projectionBound hprojection hnoise hprojectionBound_nonneg
      hprojectionBound n hsubGaussian
  constructor
  · intro s
    refine (h.integrable_exp_mul s).congr ?_
    exact Filter.Eventually.of_forall (fun omega =>
      congrArg (fun x : Real => Real.exp (s * x))
        (compensatedScore_eq_inner_sub_varianceGram
          feature noise varianceProxy n omega theta))
  · rw [ProbabilityTheory.mgf]
    calc
      ∫ omega,
          Real.exp
            (1 *
              (⟪finiteHorizonNoiseScore feature noise n omega, theta⟫_Real -
                ⟪theta,
                  Matrix.toEuclideanCLM (𝕜 := Real)
                    (finiteHorizonVarianceGram feature varianceProxy n omega)
                    theta⟫_Real / 2))
          ∂mu =
          ∫ omega,
            Real.exp
              (1 *
                (Finset.range (n + 1)).sum (fun t =>
                  match t with
                  | 0 => 0
                  | i + 1 =>
                      dotProduct (WithLp.ofLp theta) (feature i omega) *
                          noise i omega -
                        (((varianceProxy i : NNReal) : Real) *
                          (dotProduct (WithLp.ofLp theta)
                            (feature i omega)) ^ 2 / 2)))
            ∂mu := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun omega =>
                congrArg (fun x : Real => Real.exp (1 * x))
                  (compensatedScore_eq_inner_sub_varianceGram
                    feature noise varianceProxy n omega theta).symm)
      _ <= Real.exp 0 := by
        simpa [ProbabilityTheory.mgf] using h.mgf_le

/-- Explicit unit expectation bound for the score/Gram quadratic exponential. -/
theorem integral_exp_inner_finiteHorizonScore_sub_varianceGram_le_one
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
    (theta : EuclideanSpace Real Feature)
    (projectionBound : Nat -> Real)
    (hprojection : forall i,
      StronglyMeasurable[F i]
        (fun omega => dotProduct (WithLp.ofLp theta) (feature i omega)))
    (hnoise : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => noise i omega))
    (hprojectionBound_nonneg : forall i, 0 <= projectionBound i)
    (hprojectionBound : forall i omega,
      |dotProduct (WithLp.ofLp theta) (feature i omega)| <= projectionBound i)
    (n : Nat)
    (hsubGaussian : forall i, i < n ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i) (varianceProxy i) mu) :
    ∫ omega,
        Real.exp
          (⟪finiteHorizonNoiseScore feature noise n omega, theta⟫_Real -
            ⟪theta,
              Matrix.toEuclideanCLM (𝕜 := Real)
                (finiteHorizonVarianceGram feature varianceProxy n omega)
                theta⟫_Real / 2)
      ∂mu <= 1 := by
  have h :=
    finiteHorizonScoreVarianceGram_hasMGFUpperBoundAt
      mu F feature noise varianceProxy theta projectionBound hprojection
      hnoise hprojectionBound_nonneg hprojectionBound n hsubGaussian
  simpa [ProbabilityTheory.mgf] using h.mgf_le

/--
The fixed-direction expectation bound on the exact Gaussian-mixture consumer
surface.
-/
theorem integral_gaussianQuadraticExponential_finiteHorizon_le_one
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
    (theta : EuclideanSpace Real Feature)
    (projectionBound : Nat -> Real)
    (hprojection : forall i,
      StronglyMeasurable[F i]
        (fun omega => dotProduct (WithLp.ofLp theta) (feature i omega)))
    (hnoise : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => noise i omega))
    (hprojectionBound_nonneg : forall i, 0 <= projectionBound i)
    (hprojectionBound : forall i omega,
      |dotProduct (WithLp.ofLp theta) (feature i omega)| <= projectionBound i)
    (n : Nat)
    (hsubGaussian : forall i, i < n ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i) (varianceProxy i) mu) :
    ∫ omega,
        gaussianQuadraticExponential
          (finiteHorizonNoiseScore feature noise n)
          (finiteHorizonVarianceGram feature varianceProxy n)
          (omega, theta)
      ∂mu <= 1 := by
  simpa [gaussianQuadraticExponential] using
    integral_exp_inner_finiteHorizonScore_sub_varianceGram_le_one
      mu F feature noise varianceProxy theta projectionBound hprojection
      hnoise hprojectionBound_nonneg hprojectionBound n hsubGaussian

/--
Tonelli transport of all fixed-direction bounds through an arbitrary
probability law on Gaussian directions.
-/
theorem lintegral_gaussianQuadraticExponentialENNReal_finiteHorizon_prod_le_one
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (nu : Measure (EuclideanSpace Real Feature)) [IsProbabilityMeasure nu]
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
    ∫⁻ p,
        gaussianQuadraticExponentialENNReal
          (finiteHorizonNoiseScore feature noise n)
          (finiteHorizonVarianceGram feature varianceProxy n) p
      ∂mu.prod nu <= 1 := by
  have hprojection : forall (theta : EuclideanSpace Real Feature) i,
      StronglyMeasurable[F i]
        (fun omega => dotProduct (WithLp.ofLp theta) (feature i omega)) := by
    intro theta i
    simp only [dotProduct]
    fun_prop
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
  have hjoint :
      Measurable
        (gaussianQuadraticExponentialENNReal
          (finiteHorizonNoiseScore feature noise n)
          (finiteHorizonVarianceGram feature varianceProxy n)) :=
    measurable_gaussianQuadraticExponentialENNReal
      _ _ hscore hgram
  rw [MeasureTheory.lintegral_prod_symm' _ hjoint]
  calc
    ∫⁻ theta, ∫⁻ omega,
        gaussianQuadraticExponentialENNReal
          (finiteHorizonNoiseScore feature noise n)
          (finiteHorizonVarianceGram feature varianceProxy n)
          (omega, theta)
      ∂mu ∂nu <= ∫⁻ _theta, (1 : ENNReal) ∂nu := by
        apply lintegral_mono
        intro theta
        have hfixed :=
          finiteHorizonScoreVarianceGram_hasMGFUpperBoundAt
            mu F feature noise varianceProxy theta (projectionBound theta)
            (hprojection theta) hnoise
            (hprojectionBound_nonneg theta)
            (hprojectionBound theta) n hsubGaussian
        have hintegrable :
            Integrable
              (fun omega =>
                gaussianQuadraticExponential
                  (finiteHorizonNoiseScore feature noise n)
                  (finiteHorizonVarianceGram feature varianceProxy n)
                  (omega, theta))
              mu := by
          simpa [gaussianQuadraticExponential] using
            hfixed.integrable_exp_mul 1
        have hle :=
          integral_gaussianQuadraticExponential_finiteHorizon_le_one
            mu F feature noise varianceProxy theta (projectionBound theta)
            (hprojection theta) hnoise
            (hprojectionBound_nonneg theta)
            (hprojectionBound theta) n hsubGaussian
        calc
          ∫⁻ omega,
              gaussianQuadraticExponentialENNReal
                (finiteHorizonNoiseScore feature noise n)
                (finiteHorizonVarianceGram feature varianceProxy n)
                (omega, theta)
              ∂mu =
              ENNReal.ofReal
                (∫ omega,
                  gaussianQuadraticExponential
                    (finiteHorizonNoiseScore feature noise n)
                    (finiteHorizonVarianceGram feature varianceProxy n)
                    (omega, theta)
                  ∂mu) := by
                    rw [ofReal_integral_eq_lintegral_ofReal hintegrable
                      (Filter.Eventually.of_forall
                        (fun omega =>
                          (Real.exp_pos _).le))]
                    rfl
          _ <= ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hle
          _ = 1 := by norm_num
    _ = 1 := by simp

/-- Gaussian-direction specialization of the finite-horizon Tonelli bound. -/
theorem lintegral_gaussianQuadraticExponentialENNReal_finiteHorizon_prod_multivariateGaussian_zero_inv_le_one
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (V0 : Matrix Feature Feature Real)
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
    ∫⁻ p,
        gaussianQuadraticExponentialENNReal
          (finiteHorizonNoiseScore feature noise n)
          (finiteHorizonVarianceGram feature varianceProxy n) p
      ∂mu.prod (ProbabilityTheory.multivariateGaussian 0 V0⁻¹) <= 1 := by
  exact
    lintegral_gaussianQuadraticExponentialENNReal_finiteHorizon_prod_le_one
      mu (ProbabilityTheory.multivariateGaussian 0 V0⁻¹)
      F feature noise varianceProxy projectionBound hfeature hnoise
      hprojectionBound_nonneg hprojectionBound n hsubGaussian

end BanditRLProof.OFUL
