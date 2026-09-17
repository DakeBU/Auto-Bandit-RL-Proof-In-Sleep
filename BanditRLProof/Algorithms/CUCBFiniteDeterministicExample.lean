import BanditRLProof.Algorithms.CUCBFiniteSourceExample

/-! Deterministic-trigger recovery of the same noisy three-arm example. -/
namespace BanditRLProof.CUCB.FiniteExample
open MeasureTheory ProbabilityTheory
open scoped Classical
set_option autoImplicit false

def fullFeedback (a : Bool) (x : Sample) : Feedback 3 :=
  (fun _ => true,(feedback a x).2)
noncomputable def fullEnvironment : Kernel Bool (Feedback 3) where
  toFun a := sampleLaw.map (fullFeedback a)
  measurable' := Measurable.of_discrete
instance : IsMarkovKernel fullEnvironment where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure (sampleLaw.map (fullFeedback a))
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

theorem full_observed (a : Bool) (i : Fin 3) : fullEnvironment a (observedSet i)=1 := by
  change (sampleLaw.map (fullFeedback a)) (observedSet i)=1
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_observedSet i)]
  simp [observedSet,fullFeedback]

theorem full_compatible (a : Bool) (i : Fin 3) :
    ObservationCompatible (fullEnvironment a) (law i) i := by
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun z : Feedback 3 => z.2.1 i) := by fun_prop
  rw [Measure.map_apply hm hs,Measure.restrict_apply (hm hs),Measure.smul_apply,full_observed,one_smul]
  change (sampleLaw.map (fullFeedback a)) ((fun z => z.2.1 i) ⁻¹' s ∩ observedSet i)=law i s
  rw [Measure.map_apply Measurable.of_discrete ((hm hs).inter (measurableSet_observedSet i)),
    law,Measure.map_apply Measurable.of_discrete hs]
  congr 1
  ext x
  simp [fullFeedback,feedback,observedSet]

theorem full_reward_integrable (a : Bool) : Integrable (fun z => z.2.2) (fullEnvironment a) := by
  change Integrable (fun z : Feedback 3 => z.2.2) (sampleLaw.map (fullFeedback a))
  exact (integrable_map_measure (by fun_prop) Measurable.of_discrete.aemeasurable).2 Integrable.of_finite

theorem full_reward_nonneg (a : Bool) : ∀ᵐ z ∂fullEnvironment a, 0≤z.2.2 := by
  change ∀ᵐ z ∂sampleLaw.map (fullFeedback a), 0≤z.2.2
  rw [ae_map_iff Measurable.of_discrete.aemeasurable (by measurability)]
  apply Filter.Eventually.of_forall
  intro x
  cases a <;> exact mul_nonneg (outcome x _).property.1 (outcome x _).property.1

noncomputable def fullModel : FeedbackModel Bool 3 where
  selected := selected
  selected_injective := model.selected_injective
  possible := fun _ => Finset.univ
  possible_nonempty := fun _ => Finset.univ_nonempty
  selected_subset := fun _ => Finset.subset_univ _
  triggerable := fun _ => ⟨false,Finset.mem_univ _⟩
  environment := fullEnvironment
  environment_markov := inferInstance
  laws := law
  laws_probability := fun _ => inferInstance
  observation_compatible := full_compatible
  possible_iff_positive := by intro a i; simp [full_observed]
  selected_observed := by intro a i hi; exact full_observed a i
  reward_nonneg := full_reward_nonneg
  reward_integrable := full_reward_integrable

theorem full_expected_reward (a : Bool) : fullModel.expectedReward a=model.expectedReward a := by
  change (∫z : Feedback 3, z.2.2 ∂sampleLaw.map (fullFeedback a))=
    (∫z : Feedback 3, z.2.2 ∂sampleLaw.map (feedback a))
  rw [integral_map Measurable.of_discrete.aemeasurable (by fun_prop),
    integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  rfl

noncomputable def fullSource : SourceModel fullModel where
  score := score
  score_nonneg := source.score_nonneg
  score_true := by intro a; rw [full_expected_reward]; exact source.score_true a
  modulus := fun x => 2*x
  modulus_zero := source.modulus_zero
  modulus_continuous := source.modulus_continuous
  modulus_strictMono := source.modulus_strictMono
  score_monotone := source.score_monotone
  score_smooth := source.score_smooth
  alpha := 1
  beta := 1
  alpha_mem := source.alpha_mem
  beta_mem := source.beta_mem
  oracle := source.oracle
  oracle_markov := inferInstance
  oracle_success := source.oracle_success
  inverse_range := source.inverse_range

theorem full_minTrigger (i : Fin 3) : fullModel.minTrigger i=1 := by
  apply le_antisymm (fullModel.minTrigger_le_one i)
  apply Finset.le_inf'
  intro a ha
  change 1≤(fullEnvironment a (observedSet i)).toReal
  simp [full_observed]

theorem full_globalMinTrigger : fullModel.globalMinTrigger=1 :=
  fullModel.globalMinTrigger_eq_one_iff.mpr full_minTrigger

theorem deterministic_regret (H : ℕ) (hH : 1≤H) :
    fullSource.approximationRegret H≤
      4*(18*Real.log (H:ℝ))^((1:ℝ)/2)*(H:ℝ)^((1:ℝ)/2)+(1+Real.pi^2/3)*(3/4) := by
  have h := fullSource.theorem_two_deterministic H hH full_globalMinTrigger
    2 1 (by norm_num) (by norm_num) (by norm_num) (by intro u hu; simp [fullSource])
  have hg : maxPositiveGap fullSource.score fullModel.trueInput fullSource.alpha=1/4 := max_gap
  rw [hg] at h
  norm_num at h
  convert h using 1; ring_nf

end BanditRLProof.CUCB.FiniteExample
