import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Conditional-kernel KL integral for Chapter 15

Mathlib's composition-product chain rule deliberately leaves the conditional
term as another measure-level KL divergence because measurability of
`x \mapsto klDiv (kappa x) (eta x)` is not automatic. For countably generated
target spaces, kernel Radon--Nikodym derivatives provide a measurable
replacement. This module proves the resulting iterated-lintegral identity.

The result is a dependency for Lattimore--Szepesvari, *Bandit Algorithms*,
Lemma 15.1. It is not itself the adaptive-history divergence decomposition.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/--
The conditional KL term for two composition products with one common left
measure is the iterated integral of `klFun` applied to the measurable kernel
Radon--Nikodym derivative.

This is the measurable formulation of the conditional-KL integral needed by
the Chapter 15 history chain rule. Pointwise absolute continuity is explicit;
without it, individual conditional KL terms may be infinite because of
support mismatch.
-/
theorem klDiv_compProd_same_left_eq_lintegral_kernelRN_ae
    {Base Target : Type*}
    [MeasurableSpace Base] [MeasurableSpace Target]
    [MeasurableSpace.CountablyGenerated Target]
    (mu : Measure Base) [IsFiniteMeasure mu]
    (kappa eta : Kernel Base Target)
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (h_ac : ∀ᵐ base ∂mu, kappa base ≪ eta base) :
    InformationTheory.klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ eta) =
      ∫⁻ x, ∫⁻ y,
        ENNReal.ofReal
          (InformationTheory.klFun
            ((kappa.rnDeriv eta x y).toReal))
          ∂eta x ∂mu := by
  have hkappa :
      kappa =ᵐ[mu] eta.withDensity (kappa.rnDeriv eta) := by
    filter_upwards [h_ac] with base hbase
    exact (Kernel.withDensity_rnDeriv_eq hbase).symm
  have hmeasurable :
      Measurable (Function.uncurry (kappa.rnDeriv eta)) :=
    Kernel.measurable_rnDeriv kappa eta
  have hjoint :
      mu ⊗ₘ kappa =
        (mu ⊗ₘ eta).withDensity
          (fun pair => kappa.rnDeriv eta pair.1 pair.2) := by
    calc
      mu ⊗ₘ kappa =
          mu ⊗ₘ eta.withDensity (kappa.rnDeriv eta) :=
        Measure.compProd_congr hkappa
      _ = (mu ⊗ₘ eta).withDensity
          (fun pair => kappa.rnDeriv eta pair.1 pair.2) :=
        Measure.compProd_withDensity hmeasurable
  have hjoint_ac : mu ⊗ₘ kappa ≪ mu ⊗ₘ eta := by
    exact Measure.AbsolutelyContinuous.compProd_right h_ac
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hjoint_ac]
  have hrn :
      (mu ⊗ₘ kappa).rnDeriv (mu ⊗ₘ eta) =ᵐ[mu ⊗ₘ eta]
        fun pair => kappa.rnDeriv eta pair.1 pair.2 := by
    rw [hjoint]
    exact Measure.rnDeriv_withDensity _ hmeasurable
  calc
    ∫⁻ pair,
        ENNReal.ofReal
          (InformationTheory.klFun
            (((mu ⊗ₘ kappa).rnDeriv (mu ⊗ₘ eta) pair).toReal))
        ∂mu ⊗ₘ eta =
        ∫⁻ pair,
          ENNReal.ofReal
            (InformationTheory.klFun
              ((kappa.rnDeriv eta pair.1 pair.2).toReal))
          ∂mu ⊗ₘ eta := by
            refine lintegral_congr_ae ?_
            filter_upwards [hrn] with pair hpair
            rw [hpair]
    _ = ∫⁻ x, ∫⁻ y,
          ENNReal.ofReal
            (InformationTheory.klFun
              ((kappa.rnDeriv eta x y).toReal))
          ∂eta x ∂mu := by
            rw [Measure.lintegral_compProd]
            fun_prop

/-- Pointwise absolute continuity is a convenient sufficient specialization. -/
theorem klDiv_compProd_same_left_eq_lintegral_kernelRN
    {Base Target : Type*}
    [MeasurableSpace Base] [MeasurableSpace Target]
    [MeasurableSpace.CountablyGenerated Target]
    (mu : Measure Base) [IsFiniteMeasure mu]
    (kappa eta : Kernel Base Target)
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (h_ac : forall base, kappa base ≪ eta base) :
    InformationTheory.klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ eta) =
      ∫⁻ x, ∫⁻ y,
        ENNReal.ofReal
          (InformationTheory.klFun
            ((kappa.rnDeriv eta x y).toReal))
          ∂eta x ∂mu :=
  klDiv_compProd_same_left_eq_lintegral_kernelRN_ae mu kappa eta
    (Filter.Eventually.of_forall h_ac)

/--
Under pointwise absolute continuity, the measurable kernel-RN formulation is
equal to the familiar conditional-KL integral.  This closes Mathlib's stated
`klDiv_compProd_eq_add` TODO for the countably generated target-space branch.
-/
theorem klDiv_compProd_same_left_eq_lintegral_klDiv
    {Base Target : Type*}
    [MeasurableSpace Base] [MeasurableSpace Target]
    [MeasurableSpace.CountablyGenerated Target]
    (mu : Measure Base) [IsFiniteMeasure mu]
    (kappa eta : Kernel Base Target)
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (h_ac : forall base, kappa base ≪ eta base) :
    InformationTheory.klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ eta) =
      ∫⁻ base,
        InformationTheory.klDiv (kappa base) (eta base) ∂mu := by
  rw [klDiv_compProd_same_left_eq_lintegral_kernelRN mu kappa eta h_ac]
  refine lintegral_congr fun base => ?_
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (h_ac base)]
  have hmeasurable :
      Measurable (fun target => kappa.rnDeriv eta base target) :=
    (Kernel.measurable_rnDeriv kappa eta).comp
      (measurable_const.prodMk measurable_id)
  have hkappa :
      kappa base =
        (eta base).withDensity (fun target => kappa.rnDeriv eta base target) :=
    by
      rw [← Kernel.withDensity_apply eta
        (Kernel.measurable_rnDeriv kappa eta) base]
      exact (Kernel.withDensity_rnDeriv_eq (h_ac base)).symm
  have hrn :
      (kappa base).rnDeriv (eta base) =ᵐ[eta base]
        fun target => kappa.rnDeriv eta base target := by
    rw [hkappa]
    exact Measure.rnDeriv_withDensity _ hmeasurable
  refine lintegral_congr_ae ?_
  filter_upwards [hrn] with target htarget
  rw [htarget]

/-- Conditional-KL integral under almost-everywhere conditional absolute continuity. -/
theorem klDiv_compProd_same_left_eq_lintegral_klDiv_ae
    {Base Target : Type*}
    [MeasurableSpace Base] [MeasurableSpace Target]
    [MeasurableSpace.CountablyGenerated Target]
    (mu : Measure Base) [IsFiniteMeasure mu]
    (kappa eta : Kernel Base Target)
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (h_ac : ∀ᵐ base ∂mu, kappa base ≪ eta base) :
    InformationTheory.klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ eta) =
      ∫⁻ base,
        InformationTheory.klDiv (kappa base) (eta base) ∂mu := by
  rw [klDiv_compProd_same_left_eq_lintegral_kernelRN_ae
    mu kappa eta h_ac]
  refine lintegral_congr_ae ?_
  filter_upwards [h_ac] with base hbase
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hbase]
  have hmeasurable :
      Measurable (fun target => kappa.rnDeriv eta base target) :=
    (Kernel.measurable_rnDeriv kappa eta).comp
      (measurable_const.prodMk measurable_id)
  have hkappa :
      kappa base =
        (eta base).withDensity (fun target => kappa.rnDeriv eta base target) := by
    rw [← Kernel.withDensity_apply eta
      (Kernel.measurable_rnDeriv kappa eta) base]
    exact (Kernel.withDensity_rnDeriv_eq hbase).symm
  have hrn :
      (kappa base).rnDeriv (eta base) =ᵐ[eta base]
        fun target => kappa.rnDeriv eta base target := by
    rw [hkappa]
    exact Measure.rnDeriv_withDensity _ hmeasurable
  refine lintegral_congr_ae ?_
  filter_upwards [hrn] with target htarget
  rw [htarget]

/--
If the conditional KL function is measurable, the same-left composition-product
identity holds without an absolute-continuity hypothesis. Singular conditional
fibres correctly contribute `∞` on sets of positive base measure.
-/
theorem klDiv_compProd_same_left_eq_lintegral_klDiv_of_measurable
    {Base Target : Type*}
    [MeasurableSpace Base] [MeasurableSpace Target]
    [MeasurableSpace.CountablyGenerated Target]
    (mu : Measure Base) [IsFiniteMeasure mu]
    (kappa eta : Kernel Base Target)
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (hmeasurable : Measurable (fun base =>
      InformationTheory.klDiv (kappa base) (eta base))) :
    InformationTheory.klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ eta) =
      ∫⁻ base,
        InformationTheory.klDiv (kappa base) (eta base) ∂mu := by
  by_cases hjoint : mu ⊗ₘ kappa ≪ mu ⊗ₘ eta
  · exact klDiv_compProd_same_left_eq_lintegral_klDiv_ae
      mu kappa eta hjoint.kernel_of_compProd
  · have hnot_ae : ¬∀ᵐ base ∂mu, kappa base ≪ eta base := by
      intro hae
      exact hjoint (Measure.AbsolutelyContinuous.compProd_right hae)
    have hintegral_top :
        (∫⁻ base,
          InformationTheory.klDiv (kappa base) (eta base) ∂mu) = ∞ := by
      by_contra hne
      have hlt := MeasureTheory.ae_lt_top hmeasurable hne
      have hae : ∀ᵐ base ∂mu, kappa base ≪ eta base := by
        filter_upwards [hlt] with base hbase
        by_contra hnot_ac
        rw [InformationTheory.klDiv_of_not_ac hnot_ac] at hbase
        exact (not_lt_of_ge le_rfl) hbase
      exact hnot_ae hae
    rw [InformationTheory.klDiv_of_not_ac hjoint, hintegral_top]

/-- Relative entropy is invariant under a measurable equivalence. -/
theorem klDiv_map_measurableEquiv
    {Source Target : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target]
    (mu nu : Measure Source) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (equiv : Source ≃ᵐ Target) :
    InformationTheory.klDiv (mu.map equiv) (nu.map equiv) =
      InformationTheory.klDiv mu nu := by
  by_cases h_ac : mu ≪ nu
  · have hmap_ac : mu.map equiv ≪ nu.map equiv :=
      equiv.measurableEmbedding.absolutelyContinuous_map h_ac
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hmap_ac,
      InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac]
    calc
      ∫⁻ target,
          ENNReal.ofReal
            (InformationTheory.klFun
              (((mu.map equiv).rnDeriv (nu.map equiv) target).toReal))
          ∂nu.map equiv =
          ∫⁻ source,
            ENNReal.ofReal
              (InformationTheory.klFun
                (((mu.map equiv).rnDeriv (nu.map equiv)
                  (equiv source)).toReal))
            ∂nu :=
        equiv.measurableEmbedding.lintegral_map _
      _ = ∫⁻ source,
          ENNReal.ofReal
            (InformationTheory.klFun ((mu.rnDeriv nu source).toReal))
          ∂nu := by
        refine lintegral_congr_ae ?_
        filter_upwards [equiv.measurableEmbedding.rnDeriv_map mu nu]
          with source hsource
        rw [hsource]
  · have hmap_not_ac : ¬mu.map equiv ≪ nu.map equiv := by
      intro hmap_ac
      have hback :=
        equiv.symm.measurableEmbedding.absolutelyContinuous_map hmap_ac
      have hmu_back : (mu.map equiv).map equiv.symm = mu := by
        rw [Measure.map_map equiv.symm.measurable equiv.measurable]
        rw [show (equiv.symm : Target → Source) ∘ equiv = id from by
          funext source
          exact equiv.symm_apply_apply source]
        exact Measure.map_id
      have hnu_back : (nu.map equiv).map equiv.symm = nu := by
        rw [Measure.map_map equiv.symm.measurable equiv.measurable]
        rw [show (equiv.symm : Target → Source) ∘ equiv = id from by
          funext source
          exact equiv.symm_apply_apply source]
        exact Measure.map_id
      rw [hmu_back, hnu_back] at hback
      exact h_ac hback
    rw [InformationTheory.klDiv_of_not_ac hmap_not_ac,
      InformationTheory.klDiv_of_not_ac h_ac]

/--
For one adaptive bandit round, a common randomized policy contributes no KL
cost of its own.  The conditional history-extension cost is the first-law
policy average of the selected arm reward-law KL divergences.

The policy is an arbitrary Markov kernel from the complete visible history to
the action space; in particular, this statement is not restricted to a
deterministic action rule.
-/
theorem klDiv_historyStep_samePolicy_eq_iterated_lintegral_armKL
    {History Action Reward : Type*}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSpace.CountablyGenerated Action]
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (historyLaw : Measure History) [IsFiniteMeasure historyLaw]
    (policy : Kernel History Action) [IsMarkovKernel policy]
    (armLaw referenceArmLaw : Kernel Action Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (h_ac : forall arm, armLaw arm ≪ referenceArmLaw arm) :
    InformationTheory.klDiv
        (historyLaw ⊗ₘ
          (policy ⊗ₖ armLaw.comap Prod.snd measurable_snd))
        (historyLaw ⊗ₘ
          (policy ⊗ₖ referenceArmLaw.comap Prod.snd measurable_snd)) =
      ∫⁻ history, ∫⁻ arm,
        InformationTheory.klDiv (armLaw arm) (referenceArmLaw arm)
          ∂policy history ∂historyLaw := by
  let feedback : Kernel (History × Action) Reward :=
    armLaw.comap Prod.snd measurable_snd
  let referenceFeedback : Kernel (History × Action) Reward :=
    referenceArmLaw.comap Prod.snd measurable_snd
  have hstep_apply (history : History) :
      (policy ⊗ₖ feedback) history = policy history ⊗ₘ armLaw := by
    ext event hevent
    rw [Kernel.compProd_apply hevent, Measure.compProd_apply hevent]
    congr with arm
  have hreferenceStep_apply (history : History) :
      (policy ⊗ₖ referenceFeedback) history =
        policy history ⊗ₘ referenceArmLaw := by
    ext event hevent
    rw [Kernel.compProd_apply hevent, Measure.compProd_apply hevent]
    congr with arm
  have hstep_ac : forall history,
      (policy ⊗ₖ feedback) history ≪
        (policy ⊗ₖ referenceFeedback) history := by
    intro history
    rw [hstep_apply history, hreferenceStep_apply history]
    exact Measure.AbsolutelyContinuous.compProd_right
      (Filter.Eventually.of_forall h_ac)
  change InformationTheory.klDiv
      (historyLaw ⊗ₘ (policy ⊗ₖ feedback))
      (historyLaw ⊗ₘ (policy ⊗ₖ referenceFeedback)) = _
  rw [klDiv_compProd_same_left_eq_lintegral_klDiv
    historyLaw (policy ⊗ₖ feedback) (policy ⊗ₖ referenceFeedback) hstep_ac]
  refine lintegral_congr fun history => ?_
  rw [hstep_apply history, hreferenceStep_apply history]
  rw [klDiv_compProd_same_left_eq_lintegral_klDiv
    (policy history) armLaw referenceArmLaw h_ac]

/-- A finite action law admits the conditional-KL identity without an AC hypothesis. -/
theorem klDiv_finiteAction_compProd_eq_lintegral_armKL
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (actionLaw : Measure (Fin K)) [IsFiniteMeasure actionLaw]
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw] :
    InformationTheory.klDiv
        (actionLaw ⊗ₘ armLaw) (actionLaw ⊗ₘ referenceArmLaw) =
      ∫⁻ arm,
        InformationTheory.klDiv (armLaw arm) (referenceArmLaw arm)
        ∂actionLaw := by
  exact klDiv_compProd_same_left_eq_lintegral_klDiv_of_measurable
    actionLaw armLaw referenceArmLaw (measurable_of_finite _)

/-- Finite-action conditional KL written as a weighted finite sum. -/
theorem klDiv_finiteAction_compProd_eq_sum_mass_mul_armKL
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (actionLaw : Measure (Fin K)) [IsFiniteMeasure actionLaw]
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw] :
    InformationTheory.klDiv
        (actionLaw ⊗ₘ armLaw) (actionLaw ⊗ₘ referenceArmLaw) =
      ∑ arm : Fin K,
        actionLaw ({arm} : Set (Fin K)) *
          InformationTheory.klDiv (armLaw arm) (referenceArmLaw arm) := by
  rw [klDiv_finiteAction_compProd_eq_lintegral_armKL]
  rw [MeasureTheory.lintegral_fintype]
  apply Finset.sum_congr rfl
  intro arm _harm
  rw [mul_comm]

/--
General finite-action same-policy one-round KL identity.  Unlike the AC
specialization above, this theorem also covers infinite arm divergences and
zero-probability singular arms, with the standard `ENNReal` convention
`0 * ∞ = 0`.
-/
theorem klDiv_historyStep_samePolicy_eq_iterated_lintegral_armKL_general
    {History Reward : Type*} {K : Nat}
    [MeasurableSpace History]
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (historyLaw : Measure History) [IsFiniteMeasure historyLaw]
    (policy : Kernel History (Fin K)) [IsMarkovKernel policy]
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw] :
    InformationTheory.klDiv
        (historyLaw ⊗ₘ
          (policy ⊗ₖ armLaw.comap Prod.snd measurable_snd))
        (historyLaw ⊗ₘ
          (policy ⊗ₖ referenceArmLaw.comap Prod.snd measurable_snd)) =
      ∫⁻ history, ∫⁻ arm,
        InformationTheory.klDiv (armLaw arm) (referenceArmLaw arm)
          ∂policy history ∂historyLaw := by
  let feedback : Kernel (History × Fin K) Reward :=
    armLaw.comap Prod.snd measurable_snd
  let referenceFeedback : Kernel (History × Fin K) Reward :=
    referenceArmLaw.comap Prod.snd measurable_snd
  have hstep_apply (history : History) :
      (policy ⊗ₖ feedback) history = policy history ⊗ₘ armLaw := by
    ext event hevent
    rw [Kernel.compProd_apply hevent, Measure.compProd_apply hevent]
    congr with arm
  have hreferenceStep_apply (history : History) :
      (policy ⊗ₖ referenceFeedback) history =
        policy history ⊗ₘ referenceArmLaw := by
    ext event hevent
    rw [Kernel.compProd_apply hevent, Measure.compProd_apply hevent]
    congr with arm
  have hpointwise (history : History) :
      InformationTheory.klDiv
          ((policy ⊗ₖ feedback) history)
          ((policy ⊗ₖ referenceFeedback) history) =
        ∑ arm : Fin K,
          policy history ({arm} : Set (Fin K)) *
            InformationTheory.klDiv
              (armLaw arm) (referenceArmLaw arm) := by
    rw [hstep_apply, hreferenceStep_apply]
    exact klDiv_finiteAction_compProd_eq_sum_mass_mul_armKL
      (policy history) armLaw referenceArmLaw
  have hconditionalMeasurable :
      Measurable (fun history =>
        InformationTheory.klDiv
          ((policy ⊗ₖ feedback) history)
          ((policy ⊗ₖ referenceFeedback) history)) := by
    rw [show (fun history =>
        InformationTheory.klDiv
          ((policy ⊗ₖ feedback) history)
          ((policy ⊗ₖ referenceFeedback) history)) =
        fun history => ∑ arm : Fin K,
          policy history ({arm} : Set (Fin K)) *
            InformationTheory.klDiv
              (armLaw arm) (referenceArmLaw arm) by
      funext history
      exact hpointwise history]
    exact Finset.measurable_sum _ fun arm _harm =>
      (policy.measurable_coe (MeasurableSet.singleton arm)).mul measurable_const
  change InformationTheory.klDiv
      (historyLaw ⊗ₘ (policy ⊗ₖ feedback))
      (historyLaw ⊗ₘ (policy ⊗ₖ referenceFeedback)) = _
  rw [klDiv_compProd_same_left_eq_lintegral_klDiv_of_measurable
    historyLaw (policy ⊗ₖ feedback) (policy ⊗ₖ referenceFeedback)
    hconditionalMeasurable]
  refine lintegral_congr fun history => ?_
  rw [hstep_apply, hreferenceStep_apply]
  exact klDiv_finiteAction_compProd_eq_lintegral_armKL
    (policy history) armLaw referenceArmLaw

end

end LowerBounds
end BanditRLProof
