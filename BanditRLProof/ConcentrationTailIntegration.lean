import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic

noncomputable section
open MeasureTheory Real Set Filter
namespace BanditRLProof.Concentration

theorem integral_positive_tail_le_two_sqrt (f : ℝ → ℝ) (hf : Measurable f)
    (hn : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1)
    (c : ℝ) (hc : 0 < c) (ht : ∀ t, 0 < t → f t ≤ c/t^2) :
    ∫ t in Ioi 0, f t ≤ 2*sqrt c := by
  let a := sqrt c
  have ha : 0 < a := sqrt_pos.mpr hc
  have heq (t : ℝ) (ht : 0 ≤ t) : c / t^2 = c * t^(-2 : ℝ) := by
    rw [Real.rpow_neg ht, Real.rpow_two]
    rfl
  have hpow : IntegrableOn (fun t : ℝ => c*t^(-2 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).const_mul c
  have hsmall : IntegrableOn f (Ioc 0 a) := by
    apply (integrableOn_const (C := (1 : ℝ)) (hs := by simp)).mono' hf.aestronglyMeasurable
    exact Eventually.of_forall (fun t => by simpa [abs_of_nonneg (hn t)] using h1 t)
  have hlarge : IntegrableOn f (Ioi a) := by
    apply hpow.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t htmem
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn t), ← heq t (ha.trans htmem).le] using ht t (ha.trans htmem)
  have hall : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact hsmall.union hlarge
  have hs : ∫ t in Ioc 0 a, f t ≤ a := by
    calc
      _ ≤ ∫ t in Ioc 0 a, (1 : ℝ) := integral_mono hsmall (integrableOn_const (hs := by simp))
        (fun t => h1 t)
      _ = a := by simp [ha.le]
  have hl : ∫ t in Ioi a, f t ≤ c/a := by
    calc
      _ ≤ ∫ t in Ioi a, c*t^(-2 : ℝ) := integral_mono_ae hlarge hpow (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t htmem
        simpa only [← heq t (ha.trans htmem).le] using ht t (ha.trans htmem))
      _ = c/a := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
        norm_num [Real.rpow_neg_one, div_eq_mul_inv]
  have hsplit : (∫ t in Ioc 0 a, f t) + (∫ t in Ioi a, f t) = ∫ t in Ioi 0, f t := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsmall hlarge,
      Ioc_union_Ioi_eq_Ioi ha.le]
  rw [← hsplit]
  have hsq : a^2 = c := sq_sqrt hc.le
  have hdiv : c/a = a := (div_eq_iff ha.ne').mpr (by nlinarith)
  rw [hdiv] at hl
  dsimp [a] at hs hl
  linarith

end BanditRLProof.Concentration
