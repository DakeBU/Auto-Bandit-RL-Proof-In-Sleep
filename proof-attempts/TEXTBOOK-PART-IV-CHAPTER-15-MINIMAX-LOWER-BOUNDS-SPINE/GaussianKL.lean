import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace BanditRLProof.LowerBounds

lemma log_gaussianPDFReal_div_gaussianPDFReal_one
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

lemma llr_gaussianReal_one_ae
    (mu nu : Real) :
    llr (gaussianReal mu (1 : NNReal)) (gaussianReal nu (1 : NNReal))
      =ᵐ[gaussianReal mu (1 : NNReal)]
        fun x => (mu - nu) * x + (nu ^ 2 - mu ^ 2) / 2 := by
  let P := gaussianReal mu (1 : NNReal)
  let Q := gaussianReal nu (1 : NNReal)
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

lemma integrable_llr_gaussianReal_one
    (mu nu : Real) :
    Integrable
      (llr (gaussianReal mu (1 : NNReal))
        (gaussianReal nu (1 : NNReal)))
      (gaussianReal mu (1 : NNReal)) := by
  rw [integrable_congr (llr_gaussianReal_one_ae mu nu)]
  have hid : Integrable (fun x : Real => x)
      (gaussianReal mu (1 : NNReal)) :=
    (memLp_id_gaussianReal (μ := mu) (v := (1 : NNReal)) 1).integrable
      (by norm_num)
  exact (hid.const_mul (mu - nu)).add (integrable_const _)

theorem klDiv_gaussianReal_one
    (mu nu : Real) :
    InformationTheory.klDiv
        (gaussianReal mu (1 : NNReal))
        (gaussianReal nu (1 : NNReal)) =
      ENNReal.ofReal ((mu - nu) ^ 2 / 2) := by
  have hPvol : gaussianReal mu (1 : NNReal) ≪ volume :=
    gaussianReal_absolutelyContinuous mu one_ne_zero
  have hvolQ : volume ≪ gaussianReal nu (1 : NNReal) :=
    gaussianReal_absolutelyContinuous' nu one_ne_zero
  have hPQ : gaussianReal mu (1 : NNReal) ≪
      gaussianReal nu (1 : NNReal) := hPvol.trans hvolQ
  have hllr := integrable_llr_gaussianReal_one mu nu
  rw [InformationTheory.klDiv_of_ac_of_integrable hPQ hllr]
  simp only [probReal_univ, sub_self, add_zero]
  rw [integral_congr_ae (llr_gaussianReal_one_ae mu nu)]
  have hid : Integrable (fun x : Real => x)
      (gaussianReal mu (1 : NNReal)) :=
    (memLp_id_gaussianReal (μ := mu) (v := (1 : NNReal)) 1).integrable
      (by norm_num)
  have hconst : Integrable (fun _x : Real => (nu ^ 2 - mu ^ 2) / 2)
      (gaussianReal mu (1 : NNReal)) := integrable_const _
  have hlinear :
      ∫ x, (mu - nu) * x ∂gaussianReal mu (1 : NNReal) =
        (mu - nu) * mu := by
    rw [integral_const_mul, integral_id_gaussianReal]
  have hconstant :
      ∫ _x, (nu ^ 2 - mu ^ 2) / 2 ∂gaussianReal mu (1 : NNReal) =
        (nu ^ 2 - mu ^ 2) / 2 := by
    simp
  rw [integral_add (hid.const_mul (mu - nu)) hconst]
  rw [hlinear, hconstant]
  congr 1
  ring

end BanditRLProof.LowerBounds
