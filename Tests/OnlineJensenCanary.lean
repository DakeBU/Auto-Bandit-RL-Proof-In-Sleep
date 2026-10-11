import BanditRLProof
import Tests.OnlineConvexMinorantCanary
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Convex.Mul

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Tests.OnlineJensenInfinite

def law : Measure ℕ := geometricMeasure (p := (3/4 : ℝ)) (by norm_num) (by norm_num)
instance : IsProbabilityMeasure law := isProbabilityMeasure_geometricMeasure _ _
def X (n : ℕ) : ℝ := 2 ^ n
lemma atom (n : ℕ) : law {n} = ENNReal.ofReal ((1/4 : ℝ)^n * (3/4)) := by
  rw [law, geometricMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change ENNReal.ofReal ((1 - 3/4 : ℝ)^n * (3/4)) = _
  norm_num

lemma weighted (n : ℕ) : X n * ((1/4 : ℝ)^n * (3/4)) = (1/2 : ℝ)^n * (3/4) := by
  dsimp [X]
  rw [← mul_assoc, ← mul_pow]
  norm_num

lemma X_integrable : Integrable X law := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (ae_of_all law (fun n => pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n))).mp
  rw [lintegral_countable']
  have hxn (n : ℕ) : (0:ℝ) ≤ X n := pow_nonneg (by norm_num) n
  simp_rw [atom]
  have he (n : ℕ) : ENNReal.ofReal (2 ^ n : ℝ) * ENNReal.ofReal ((1/4 : ℝ)^n * (3/4)) = ENNReal.ofReal ((1/2 : ℝ)^n * (3/4)) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n)]
    exact congrArg ENNReal.ofReal (weighted n)
  simp_rw [he]
  exact ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_right (3/4)).tsum_ofReal_ne_top

lemma square_infinite : (∫⁻ n, ENNReal.ofReal ((X n)^2) ∂law) = ∞ := by
  rw [lintegral_countable']
  have hterm (n : ℕ) : ENNReal.ofReal ((X n)^2) * law {n} = ENNReal.ofReal (3/4 : ℝ) := by
    rw [atom, ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    dsimp [X]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_assoc, ← mul_pow]
    norm_num
  simp_rw [hterm]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)


open BanditRL.OnlineConvex
lemma source_infinite_instance :
    (((∫ n, X n ∂law)^2 : ℝ) : EReal) ≤ signedExpectation law (fun n => (((X n)^2 : ℝ) : EReal)) ∧
    signedExpectation law (fun n => (((X n)^2 : ℝ) : EReal)) = ⊤ := by
  have hf : IsConvexExtended (fun x : ℝ => ((x^2 : ℝ) : EReal)) :=
    (convexExtended_coe_iff _).mpr (Even.convexOn_pow (by decide : Even 2))
  have hbot : ∀ x : ℝ, ((x^2 : ℝ) : EReal) ≠ ⊥ := fun x => EReal.coe_ne_bot _
  have hm : Measurable (fun x : ℝ => ((x^2 : ℝ) : EReal)) := (measurable_id.pow_const 2).coe_real_ereal
  have hXm : Measurable X := measurable_of_countable _
  have hd : ∀ᵐ n ∂law, X n ∈ effectiveDomain (fun x : ℝ => ((x^2 : ℝ) : EReal)) :=
    ae_of_all law (fun n => EReal.coe_lt_top _)
  refine ⟨theorem_2_9 law _ hbot hf hm X hXm X_integrable hd, ?_⟩
  apply signedExpectation_eq_top
  · exact square_infinite
  · exact jensen_negativeIntegral_ne_top law _ hbot hf hm X hXm X_integrable hd
#print axioms source_infinite_instance
end Tests.OnlineJensenInfinite

namespace Tests.OnlineJensenFinite
open BanditRL.OnlineConvex

def law : Measure ℝ := (1/2 : ℝ≥0∞) • Measure.dirac 1 + (1/2 : ℝ≥0∞) • Measure.dirac 3
instance : IsProbabilityMeasure law := by
  constructor
  norm_num [law, ENNReal.inv_two_add_inv_two]
lemma integrable_atom_function (g : ℝ → ℝ) : Integrable g law := by
  exact ((integrable_dirac (by simp)).smul_measure (by norm_num)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))
lemma mean : (∫ x : ℝ, x ∂law) = 2 := by
  rw [law, integral_add_measure, integral_smul_measure, integral_smul_measure]
  · norm_num
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)
lemma square_expectation : signedExpectation law (fun x : ℝ => ((x^2 : ℝ) : EReal)) = (5 : ℝ) := by
  rw [signedExpectation_coe_integrable law _ (integrable_atom_function _)]
  congr 1
  rw [law, integral_add_measure, integral_smul_measure, integral_smul_measure]
  · norm_num
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)
lemma source_finite_instance : (((∫ x : ℝ, x ∂law)^2 : ℝ) : EReal) ≤
    signedExpectation law (fun x : ℝ => ((x^2 : ℝ) : EReal)) := by
  apply theorem_2_9 law (fun x : ℝ => ((x^2 : ℝ) : EReal)) (fun x => EReal.coe_ne_bot _) _ _ id measurable_id
    (integrable_atom_function id) (ae_of_all law (fun x => EReal.coe_lt_top _))
  · exact (convexExtended_coe_iff _).mpr (Even.convexOn_pow (by decide : Even 2))
  · exact (measurable_id.pow_const 2).coe_real_ereal
#print axioms source_finite_instance
end Tests.OnlineJensenFinite

#print axioms BanditRL.OnlineConvex.jensen_negativeIntegral_ne_top
#print axioms BanditRL.OnlineConvex.theorem_2_9

namespace Tests.OnlineJensenNonclosed
open BanditRL.OnlineConvex Tests.OnlineConvexBarycenter Tests.OnlineConvexMinorant

lemma measurable_ray : MeasurableSet ray := by
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_eq_fun measurable_snd measurable_const)
lemma loss_measurable : Measurable loss := by
  classical
  have hh : Measurable (fun p : ℝ × ℝ => if p ∈ ray then (p.1 : EReal) else ⊤) :=
    measurable_fst.coe_real_ereal.ite measurable_ray measurable_const
  convert hh using 1
  ext p
  exact loss_formula p
lemma source_nonclosed_instance :
    loss (∫ x, vector x ∂Tests.OnlineConvexBarycenter.law) ≤
      signedExpectation Tests.OnlineConvexBarycenter.law (fun x => loss (vector x)) := by
  apply theorem_2_9 _ loss loss_noBot loss_convex loss_measurable vector
    (measurable_id.prodMk measurable_const) vector_integrable
  simpa only [loss_domain] using vector_in_ray
lemma domain_is_nonclosed : ¬ IsClosed (effectiveDomain loss) := by
  rw [loss_domain]
  exact ray_not_closed
#print axioms source_nonclosed_instance
#print axioms domain_is_nonclosed
end Tests.OnlineJensenNonclosed
