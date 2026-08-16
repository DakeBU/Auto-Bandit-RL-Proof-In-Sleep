import BanditRLProof.LowerBounds.InformationTheory
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Finite-armed minimax lower-bound dependencies

This file starts the source-faithful Chapter 15 spine for Lattimore--Szepesvári,
*Bandit Algorithms* (2020).  The compiled surface currently proves the exact
unit-variance Gaussian likelihood ratio and KL formula used in Theorem 15.2.

It deliberately does **not** claim Lemma 15.1's adaptive-history divergence
decomposition or Theorem 15.2.  Those terminals require a common stochastic
policy-kernel history law and a conditional composition-product KL integral;
the repository currently has neither complete interface.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

/-- A unit-variance Gaussian arm with mean `mu`. -/
abbrev unitGaussianArm (mu : Real) : Measure Real :=
  gaussianReal mu (1 : NNReal)

/-- The finite family of unit-variance Gaussian arms indexed by a mean vector. -/
abbrev unitGaussianBandit {k : Nat} (mean : Fin k -> Real) :
    Fin k -> Measure Real :=
  fun arm => unitGaussianArm (mean arm)

/-- Pointwise log-density ratio for two unit-variance Gaussian laws. -/
theorem log_gaussianPDFReal_div_gaussianPDFReal_one
    (mu nu x : Real) :
    Real.log
        (gaussianPDFReal mu (1 : NNReal) x /
          gaussianPDFReal nu (1 : NNReal) x) =
      (mu - nu) * x + (nu ^ 2 - mu ^ 2) / 2 := by
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]
  have hnorm : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by positivity
  have hden : Real.exp (-(x - nu) ^ 2 / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [mul_div_mul_left _ _ hnorm]
  rw [Real.log_div (Real.exp_ne_zero _) hden]
  rw [Real.log_exp, Real.log_exp]
  ring

/-- The log Radon--Nikodym derivative has the expected affine form under the
first Gaussian law.  The direction is `N(mu,1)` to `N(nu,1)`. -/
theorem llr_gaussianReal_one_ae
    (mu nu : Real) :
    llr (unitGaussianArm mu) (unitGaussianArm nu)
      =ᵐ[unitGaussianArm mu]
        fun x => (mu - nu) * x + (nu ^ 2 - mu ^ 2) / 2 := by
  let P := unitGaussianArm mu
  let Q := unitGaussianArm nu
  have hPvol : P ≪ volume := gaussianReal_absolutelyContinuous mu one_ne_zero
  have hQvol : Q ≪ volume := gaussianReal_absolutelyContinuous nu one_ne_zero
  have hvolQ : volume ≪ Q := gaussianReal_absolutelyContinuous' nu one_ne_zero
  have hPQ : P ≪ Q := hPvol.trans hvolQ
  have hratio := hPQ.ae_le (Measure.rnDeriv_eq_div hPvol hQvol)
  have hPpdf := hPvol.ae_le (rnDeriv_gaussianReal mu (1 : NNReal))
  have hQpdf := hPvol.ae_le (rnDeriv_gaussianReal nu (1 : NNReal))
  filter_upwards [hratio, hPpdf, hQpdf] with x hratio_x hPpdf_x hQpdf_x
  rw [llr, hratio_x, hPpdf_x, hQpdf_x, ENNReal.toReal_div,
    toReal_gaussianPDF, toReal_gaussianPDF]
  exact log_gaussianPDFReal_div_gaussianPDFReal_one mu nu x

/-- The Gaussian log likelihood ratio is integrable under its first law. -/
theorem integrable_llr_gaussianReal_one
    (mu nu : Real) :
    Integrable (llr (unitGaussianArm mu) (unitGaussianArm nu))
      (unitGaussianArm mu) := by
  rw [integrable_congr (llr_gaussianReal_one_ae mu nu)]
  have hid : Integrable (fun x : Real => x) (unitGaussianArm mu) :=
    (memLp_id_gaussianReal (μ := mu) (v := (1 : NNReal)) 1).integrable
      (by norm_num)
  exact (hid.const_mul (mu - nu)).add (integrable_const _)

/-- Exact KL divergence between unit-variance Gaussian laws:
`D(N(mu,1),N(nu,1))=(mu-nu)^2/2`.

The result is stated in `ENNReal`, matching Mathlib's measure-KL API and
retaining the source direction even though this equal-variance value happens
to be symmetric in the two means. -/
theorem klDiv_gaussianReal_one
    (mu nu : Real) :
    InformationTheory.klDiv (unitGaussianArm mu) (unitGaussianArm nu) =
      ENNReal.ofReal ((mu - nu) ^ 2 / 2) := by
  have hPvol : unitGaussianArm mu ≪ volume :=
    gaussianReal_absolutelyContinuous mu one_ne_zero
  have hvolQ : volume ≪ unitGaussianArm nu :=
    gaussianReal_absolutelyContinuous' nu one_ne_zero
  have hPQ : unitGaussianArm mu ≪ unitGaussianArm nu := hPvol.trans hvolQ
  have hllr := integrable_llr_gaussianReal_one mu nu
  rw [InformationTheory.klDiv_of_ac_of_integrable hPQ hllr]
  simp only [probReal_univ]
  rw [integral_congr_ae (llr_gaussianReal_one_ae mu nu)]
  have hid : Integrable (fun x : Real => x) (unitGaussianArm mu) :=
    (memLp_id_gaussianReal (μ := mu) (v := (1 : NNReal)) 1).integrable
      (by norm_num)
  have hconst : Integrable (fun _x : Real => (nu ^ 2 - mu ^ 2) / 2)
      (unitGaussianArm mu) := integrable_const _
  have hlinear :
      ∫ x, (mu - nu) * x ∂unitGaussianArm mu = (mu - nu) * mu := by
    rw [integral_const_mul, integral_id_gaussianReal]
  have hconstant :
      ∫ _x, (nu ^ 2 - mu ^ 2) / 2 ∂unitGaussianArm mu =
        (nu ^ 2 - mu ^ 2) / 2 := by
    simp
  rw [integral_add (hid.const_mul (mu - nu)) hconst]
  rw [hlinear, hconstant]
  congr 1
  ring

/-- Source-specialized Gaussian KL value for the changed arm in the proof of
Theorem 15.2. -/
theorem klDiv_unitGaussianArm_zero_two_mul (gap : Real) :
    InformationTheory.klDiv (unitGaussianArm 0) (unitGaussianArm (2 * gap)) =
      ENNReal.ofReal (2 * gap ^ 2) := by
  rw [klDiv_gaussianReal_one]
  congr 1
  ring

end

end LowerBounds
end BanditRLProof
