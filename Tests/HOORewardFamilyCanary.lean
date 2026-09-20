import BanditRLProof

open MeasureTheory ProbabilityTheory BanditRLProof.HOO
open BanditRLProof.HOO.CantorModel

noncomputable section
namespace HOORewardFamilyCanary
set_option autoImplicit false

example : Infinite Arm := inferInstance
example (x : Arm) (r : ℝ) : law x ≠ Measure.dirac r := law_not_dirac x r

example : covering.toCovering.familyNodeLaw (fun x => law x) =
    covering.toCovering.nodeLaw law := covering.toCovering.familyNodeLaw_eq_nodeLaw law

-- Consume the new family theorem, not merely the old final-rate canary.
example : ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
    (∫ Y, (∑ n ∈ Finset.range N, ((1/2:ℝ)-Y n))
      ∂trajectory 1 (1/2) (covering.toCovering.familyNodeLaw (fun x => law x))) ≤
      γ*(N:ℝ)^(4/5:ℝ)*(Real.log (max (N:ℝ) 2))^(1/5:ℝ) := by
  have hr (x : Arm) : mean x ∈ Set.Icc (0:ℝ) 1 := by
    unfold mean; split_ifs <;> norm_num
  have hd : covering.nearOptimalityDimension mean (1/2) (4*covering.nu1/covering.nu2) < (3:EReal) :=
    (dimension_le_two _).trans_lt (by exact_mod_cast (by norm_num : (2:ℝ)<3))
  have he := covering.expected_actualRegret_rate_family (fun x => law x) mean (1/2) 3
    law_mean mean_le_best hr global_sup weaklyLipschitz law_bounded hd
  norm_num only [covering, one_mul, one_div, Nat.cast_ofNat, add_zero] at he ⊢
  convert he using 1

-- The generic consumer exposes no global family measurability premise.
example (reward : Arm → Measure ℝ) [∀ x, IsProbabilityMeasure (reward x)]
    (hm : ∀ x, (∫ y, y ∂reward x) = mean x)
    (hb : ∀ x, ∀ᵐ y ∂reward x, y ∈ Set.Icc (0:ℝ) 1) (N : ℕ) :
    (∫ Y, (∑ n ∈ Finset.range N, ((1/2:ℝ)-Y n))
      ∂trajectory 1 (1/2) (covering.toCovering.familyNodeLaw reward)) =
    (∫ Y, (∑ n ∈ Finset.range N,
      ((1/2:ℝ)-mean (covering.toCovering.arm 1 (1/2) Y n)))
      ∂trajectory 1 (1/2) (covering.toCovering.familyNodeLaw reward)) := by
  apply covering.expected_actual_eq_pseudoRegret_family reward mean (1/2) hm
  intro x
  unfold mean; split_ifs <;> norm_num
  exact hb

#print axioms BanditRLProof.HOO.RegularCovering.expected_pseudoRegret_rate_family
#print axioms BanditRLProof.HOO.RegularCovering.expected_actual_eq_pseudoRegret_family
#print axioms BanditRLProof.HOO.RegularCovering.expected_actualRegret_rate_family
end HOORewardFamilyCanary
