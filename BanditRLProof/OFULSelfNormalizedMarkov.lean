import BanditRLProof.OFULGaussianEvaluatedMixture
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Markov transport for finite-horizon OFUL self-normalization

This module consumes the evaluated Gaussian-mixture `lintegral <= 1` and
converts it into a probability bound. It then transports the paper-facing
inverse-Gram/log-determinant bad event into the Markov threshold event.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp Set
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace MatrixOrder

variable {Omega Feature : Type*}

/-- The common conditional sub-Gaussian variance proxy `R²`. -/
def constantSquaredVarianceProxy (R : Real) : Nat -> NNReal :=
  fun _ => ⟨R ^ 2, sq_nonneg R⟩

/-- The unweighted finite-horizon feature Gram `sum_{i<n} x_i x_i^T`. -/
noncomputable def finiteHorizonFeatureGram
    (feature : Nat -> Omega -> Feature -> Real)
    (n : Nat) (omega : Omega) : Matrix Feature Feature Real :=
  prefixFeatureGram (fun i => feature i omega) n

/--
At common proxy `R²`, the variance Gram is `R²` times the unweighted feature
Gram.
-/
theorem finiteHorizonVarianceGram_constantSquared_eq_smul_featureGram
    [Fintype Feature]
    (R : Real) (hR : 0 < R)
    (feature : Nat -> Omega -> Feature -> Real)
    (n : Nat) (omega : Omega) :
    finiteHorizonVarianceGram
        feature (constantSquaredVarianceProxy R) n omega =
      R ^ 2 • finiteHorizonFeatureGram feature n omega := by
  ext j k
  simp [finiteHorizonVarianceGram, prefixFeatureGram,
    varianceWeightedFeature, constantSquaredVarianceProxy,
    finiteHorizonFeatureGram, Real.sqrt_sq_eq_abs, abs_of_pos hR]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The unweighted finite-horizon feature Gram is positive semidefinite. -/
theorem finiteHorizonFeatureGram_posSemidef
    [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (n : Nat) (omega : Omega) :
    (finiteHorizonFeatureGram feature n omega).PosSemidef := by
  have h :=
    finiteHorizonVarianceGram_posSemidef
      feature (constantSquaredVarianceProxy 1) n omega
  rw [finiteHorizonVarianceGram_constantSquared_eq_smul_featureGram
    1 one_pos feature n omega] at h
  simpa using h

/-- Positive scalar-square rescaling preserves positive definiteness. -/
theorem sq_smul_posDef
    [Fintype Feature] [DecidableEq Feature]
    (R : Real) (hR : 0 < R)
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef) :
    (R ^ 2 • V0).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (hV0.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))) ?_
  intro x hx
  have hquad := hV0.dotProduct_mulVec_pos hx
  simpa [Matrix.smul_mulVec, dotProduct_smul] using
    mul_pos (sq_pos_of_pos hR) hquad

/-- A common nonzero scalar factor cancels from a determinant ratio. -/
theorem det_sq_smul_div_det_sq_smul
    [Fintype Feature] [DecidableEq Feature]
    (R : Real) (hR : 0 < R)
    (A B : Matrix Feature Feature Real) :
    Matrix.det (R ^ 2 • A) / Matrix.det (R ^ 2 • B) =
      Matrix.det A / Matrix.det B := by
  rw [Matrix.det_smul, Matrix.det_smul]
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  field_simp [pow_ne_zero (Fintype.card Feature) hR2]

/--
The inverse quadratic form of a matrix scaled by `R²` is the original
quadratic form divided by `R²`.
-/
theorem dotProduct_sq_smul_inv_mulVec
    [Fintype Feature] [DecidableEq Feature]
    (R : Real) (hR : 0 < R)
    (A : Matrix Feature Feature Real) (hA : A.PosDef)
    (score : EuclideanSpace Real Feature) :
    score ⬝ᵥ (R ^ 2 • A)⁻¹.mulVec score =
      (score ⬝ᵥ A⁻¹.mulVec score) / R ^ 2 := by
  letI : Invertible (R ^ 2) :=
    invertibleOfNonzero (pow_ne_zero 2 hR.ne')
  rw [Matrix.inv_smul A (R ^ 2)
    (A.isUnit_iff_isUnit_det.mp hA.isUnit)]
  simp [Matrix.smul_mulVec, dotProduct_smul, div_eq_mul_inv]
  ring

/--
Markov's inequality for the evaluated finite-horizon Gaussian-mixture
surface, with an arbitrary nonzero finite `ENNReal` confidence level.
-/
theorem measure_inv_le_finiteHorizonDetRatioInvGramExponential_le
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
        (F i) (F.le i) (noise i) (varianceProxy i) mu)
    (delta : ENNReal) (hdelta_zero : delta ≠ 0)
    (hdelta_top : delta ≠ ∞) :
    mu {omega |
        delta⁻¹ <=
          finiteHorizonDetRatioInvGramExponential
            V0 feature noise varianceProxy n omega} <= delta := by
  have hfeatureMeas : forall i j,
      Measurable (fun omega => feature i omega j) := by
    intro i j
    exact (hfeature i j).measurable.mono (F.le i) le_rfl
  have hnoiseMeas : forall i, Measurable (noise i) := by
    intro i
    have hi : StronglyMeasurable[F (i + 1)] (noise i) := by
      simpa using hnoise (i + 1)
    exact hi.measurable.mono (F.le (i + 1)) le_rfl
  have hmeas :
      Measurable
        (finiteHorizonDetRatioInvGramExponential
          V0 feature noise varianceProxy n) :=
    measurable_finiteHorizonDetRatioInvGramExponential
      V0 hV0 feature noise varianceProxy n hfeatureMeas hnoiseMeas
  have hmoment :
      ∫⁻ omega,
          finiteHorizonDetRatioInvGramExponential
            V0 feature noise varianceProxy n omega
        ∂mu <= 1 :=
    lintegral_finiteHorizon_detRatio_invGramExponential_le_one
      mu V0 hV0 F feature noise varianceProxy projectionBound hfeature hnoise
      hprojectionBound_nonneg hprojectionBound n hsubGaussian
  have hmarkov :=
    meas_ge_le_lintegral_div (μ := mu) hmeas.aemeasurable
      (ENNReal.inv_ne_zero.mpr hdelta_top)
      (ENNReal.inv_ne_top.mpr hdelta_zero)
  calc
    mu {omega |
        delta⁻¹ <=
          finiteHorizonDetRatioInvGramExponential
            V0 feature noise varianceProxy n omega} <=
        (∫⁻ omega,
            finiteHorizonDetRatioInvGramExponential
              V0 feature noise varianceProxy n omega
          ∂mu) / delta⁻¹ := hmarkov
    _ <= 1 / delta⁻¹ := by gcongr
    _ = delta := by simp

/--
Real-confidence specialization of the evaluated-mixture Markov bound.
-/
theorem measure_invOfReal_le_finiteHorizonDetRatioInvGramExponential_le
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
        (F i) (F.le i) (noise i) (varianceProxy i) mu)
    (delta : Real) (hdelta : 0 < delta) :
    mu {omega |
        (ENNReal.ofReal delta)⁻¹ <=
          finiteHorizonDetRatioInvGramExponential
            V0 feature noise varianceProxy n omega} <=
      ENNReal.ofReal delta := by
  exact
    measure_inv_le_finiteHorizonDetRatioInvGramExponential_le
      mu V0 hV0 F feature noise varianceProxy projectionBound hfeature hnoise
      hprojectionBound_nonneg hprojectionBound n hsubGaussian
      (ENNReal.ofReal delta)
      (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
      ENNReal.ofReal_ne_top

/--
The inverse-Gram/log-determinant bad-event inequality implies the evaluated
Gaussian-mixture Markov threshold, pointwise.
-/
theorem invOfReal_le_gaussianDetRatioExponential_of_invGramQuadratic_gt
    [Fintype Feature] [DecidableEq Feature]
    (V0 G : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (hG : G.PosSemidef) (score : EuclideanSpace Real Feature)
    (delta : Real) (hdelta : 0 < delta)
    (hbad :
      score ⬝ᵥ (V0 + G)⁻¹.mulVec score >
        2 *
          Real.log
            (Real.sqrt
                (Matrix.det (V0 + G) / Matrix.det V0) / delta)) :
    (ENNReal.ofReal delta)⁻¹ <=
      ENNReal.ofReal
        (Real.sqrt (Matrix.det V0 / Matrix.det (V0 + G)) *
          Real.exp
            (score ⬝ᵥ (V0 + G)⁻¹.mulVec score / 2)) := by
  have hV0det : 0 < Matrix.det V0 := hV0.det_pos
  have hsumdet : 0 < Matrix.det (V0 + G) :=
    (hV0.add_posSemidef hG).det_pos
  have hscale_pos :
      0 < Real.sqrt (Matrix.det V0 / Matrix.det (V0 + G)) :=
    Real.sqrt_pos.2 (div_pos hV0det hsumdet)
  have hratio_pos :
      0 < Real.sqrt (Matrix.det (V0 + G) / Matrix.det V0) :=
    Real.sqrt_pos.2 (div_pos hsumdet hV0det)
  have hreciprocal :
      Real.sqrt (Matrix.det V0 / Matrix.det (V0 + G)) *
          Real.sqrt (Matrix.det (V0 + G) / Matrix.det V0) =
        1 := by
    rw [Real.sqrt_div hV0det.le, Real.sqrt_div hsumdet.le]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hV0det),
      ne_of_gt (Real.sqrt_pos.2 hsumdet)]
  have hlogarg :
      0 <
        Real.sqrt (Matrix.det (V0 + G) / Matrix.det V0) / delta :=
    div_pos hratio_pos hdelta
  have hhalf :
      Real.log
          (Real.sqrt (Matrix.det (V0 + G) / Matrix.det V0) / delta) <
        score ⬝ᵥ (V0 + G)⁻¹.mulVec score / 2 := by
    linarith
  have hexp :
      Real.sqrt (Matrix.det (V0 + G) / Matrix.det V0) / delta <
        Real.exp
          (score ⬝ᵥ (V0 + G)⁻¹.mulVec score / 2) := by
    rw [← Real.exp_log hlogarg]
    exact Real.exp_lt_exp.mpr hhalf
  have hreal :
      delta⁻¹ <
        Real.sqrt (Matrix.det V0 / Matrix.det (V0 + G)) *
          Real.exp
            (score ⬝ᵥ (V0 + G)⁻¹.mulVec score / 2) := by
    calc
      delta⁻¹ =
          Real.sqrt (Matrix.det V0 / Matrix.det (V0 + G)) *
            (Real.sqrt (Matrix.det (V0 + G) / Matrix.det V0) /
                delta) := by
                symm
                rw [← mul_div_assoc, hreciprocal, one_div]
      _ <
          Real.sqrt (Matrix.det V0 / Matrix.det (V0 + G)) *
            Real.exp
              (score ⬝ᵥ (V0 + G)⁻¹.mulVec score / 2) :=
        mul_lt_mul_of_pos_left hexp hscale_pos
  rw [← ENNReal.ofReal_inv_of_pos hdelta]
  exact ENNReal.ofReal_le_ofReal hreal.le

/--
Finite-horizon inverse-Gram/log-determinant bad-event probability bound for
the variance-weighted Gram produced by the conditional-MGF route.
-/
theorem measure_finiteHorizon_invGramQuadratic_gt_two_log_detRatio_div_le
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
        (F i) (F.le i) (noise i) (varianceProxy i) mu)
    (delta : Real) (hdelta : 0 < delta) :
    mu {omega |
        (finiteHorizonNoiseScore feature noise n omega) ⬝ᵥ
              (V0 +
                finiteHorizonVarianceGram
                  feature varianceProxy n omega)⁻¹.mulVec
                (finiteHorizonNoiseScore feature noise n omega) >
          2 *
            Real.log
              (Real.sqrt
                  (Matrix.det
                      (V0 +
                        finiteHorizonVarianceGram
                          feature varianceProxy n omega) /
                    Matrix.det V0) /
                delta)} <=
      ENNReal.ofReal delta := by
  calc
    mu {omega |
        (finiteHorizonNoiseScore feature noise n omega) ⬝ᵥ
              (V0 +
                finiteHorizonVarianceGram
                  feature varianceProxy n omega)⁻¹.mulVec
                (finiteHorizonNoiseScore feature noise n omega) >
          2 *
            Real.log
              (Real.sqrt
                  (Matrix.det
                      (V0 +
                        finiteHorizonVarianceGram
                          feature varianceProxy n omega) /
                    Matrix.det V0) /
                delta)} <=
        mu {omega |
          (ENNReal.ofReal delta)⁻¹ <=
            finiteHorizonDetRatioInvGramExponential
              V0 feature noise varianceProxy n omega} := by
      apply measure_mono
      intro omega hbad
      simpa [finiteHorizonDetRatioInvGramExponential] using
        invOfReal_le_gaussianDetRatioExponential_of_invGramQuadratic_gt
          V0
          (finiteHorizonVarianceGram feature varianceProxy n omega)
          hV0
          (finiteHorizonVarianceGram_posSemidef
            feature varianceProxy n omega)
          (finiteHorizonNoiseScore feature noise n omega)
          delta hdelta hbad
    _ <= ENNReal.ofReal delta :=
      measure_invOfReal_le_finiteHorizonDetRatioInvGramExponential_le
        mu V0 hV0 F feature noise varianceProxy projectionBound hfeature
        hnoise hprojectionBound_nonneg hprojectionBound n hsubGaussian
        delta hdelta

/--
Finite-horizon self-normalized tail bound with the conventional common
conditional sub-Gaussian scale `R`. The matrix in the reported norm is the
unweighted feature Gram, while the confidence radius carries the factor `R²`.
-/
theorem
    measure_finiteHorizon_selfNormalizedQuadratic_gt_two_mul_sq_mul_log_detRatio_div_le
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (V0 : Matrix Feature Feature Real) (hV0 : V0.PosDef)
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
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
    (delta : Real) (hdelta : 0 < delta) :
    mu {omega |
        (finiteHorizonNoiseScore feature noise n omega) ⬝ᵥ
              (V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
                (finiteHorizonNoiseScore feature noise n omega) >
          2 * R ^ 2 *
            Real.log
              (Real.sqrt
                  (Matrix.det
                      (V0 + finiteHorizonFeatureGram feature n omega) /
                    Matrix.det V0) /
                delta)} <=
      ENNReal.ofReal delta := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  calc
    mu {omega |
        (finiteHorizonNoiseScore feature noise n omega) ⬝ᵥ
              (V0 + finiteHorizonFeatureGram feature n omega)⁻¹.mulVec
                (finiteHorizonNoiseScore feature noise n omega) >
          2 * R ^ 2 *
            Real.log
              (Real.sqrt
                  (Matrix.det
                      (V0 + finiteHorizonFeatureGram feature n omega) /
                    Matrix.det V0) /
                delta)} <=
        mu {omega |
          (finiteHorizonNoiseScore feature noise n omega) ⬝ᵥ
                ((R ^ 2 • V0) +
                  finiteHorizonVarianceGram feature
                    (constantSquaredVarianceProxy R) n omega)⁻¹.mulVec
                  (finiteHorizonNoiseScore feature noise n omega) >
            2 *
              Real.log
                (Real.sqrt
                    (Matrix.det
                        ((R ^ 2 • V0) +
                          finiteHorizonVarianceGram feature
                            (constantSquaredVarianceProxy R) n omega) /
                      Matrix.det (R ^ 2 • V0)) /
                  delta)} := by
      apply measure_mono
      intro omega hbad
      simp only [Set.mem_setOf_eq] at hbad ⊢
      have hG :
          (finiteHorizonFeatureGram feature n omega).PosSemidef :=
        finiteHorizonFeatureGram_posSemidef feature n omega
      have hsum :
          (V0 + finiteHorizonFeatureGram feature n omega).PosDef :=
        hV0.add_posSemidef hG
      have hscaledSum :
          (R ^ 2 • V0) +
                finiteHorizonVarianceGram feature
                  (constantSquaredVarianceProxy R) n omega =
            R ^ 2 •
              (V0 + finiteHorizonFeatureGram feature n omega) := by
        rw [finiteHorizonVarianceGram_constantSquared_eq_smul_featureGram
          R hR feature n omega, smul_add]
      rw [hscaledSum,
        dotProduct_sq_smul_inv_mulVec R hR
          (V0 + finiteHorizonFeatureGram feature n omega) hsum,
        det_sq_smul_div_det_sq_smul R hR
          (V0 + finiteHorizonFeatureGram feature n omega) V0]
      apply (lt_div_iff₀ hR2).2
      nlinarith
    _ <= ENNReal.ofReal delta :=
      measure_finiteHorizon_invGramQuadratic_gt_two_log_detRatio_div_le
        mu (R ^ 2 • V0) (sq_smul_posDef R hR V0 hV0)
        F feature noise (constantSquaredVarianceProxy R)
        projectionBound hfeature hnoise hprojectionBound_nonneg
        hprojectionBound n hsubGaussian delta hdelta

end BanditRLProof.OFUL
