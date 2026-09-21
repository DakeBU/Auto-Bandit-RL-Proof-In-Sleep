import BanditRLProof.Algorithms.CUCBSourceModel
import BanditRLProof.Algorithms.ThompsonRecursiveSampler
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! A finite noisy triggered-feedback witness. Independent primitive coordinates
produce three Bernoulli arms and a fresh extra-trigger coin. -/
namespace BanditRLProof.CUCB.FiniteExample
open MeasureTheory ProbabilityTheory
open scoped Classical
set_option autoImplicit false

abbrev Sample := Fin 4 × Bool × Fin 4 × Bool
noncomputable def sampleLaw : Measure Sample := Thompson.uniformActionMeasure Sample
instance : IsProbabilityMeasure sampleLaw := by unfold sampleLaw; infer_instance

def bit (b : Bool) : UnitOutcome := ⟨if b then 1 else 0, by cases b <;> norm_num⟩
def outcome (x : Sample) (i : Fin 3) : UnitOutcome :=
  if i=0 then bit (decide (x.1=0))
  else if i=1 then bit x.2.1 else bit (decide (x.2.2.1≠0))
def selected (a : Bool) : Finset (Fin 3) := if a then {1,2} else {0,1}
def feedback (a : Bool) (x : Sample) : Feedback 3 :=
  (fun i => decide (i∈selected a) || x.2.2.2,
   outcome x, if a then (outcome x 1:ℝ)*(outcome x 2:ℝ)
      else (outcome x 0:ℝ)*(outcome x 1:ℝ))

noncomputable def environment : Kernel Bool (Feedback 3) where
  toFun a := sampleLaw.map (feedback a)
  measurable' := by exact Measurable.of_discrete
instance : IsMarkovKernel environment where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure (sampleLaw.map (feedback a))
    exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable)
noncomputable def law (i : Fin 3) : Measure UnitOutcome :=
  sampleLaw.map (fun x => outcome x i)
instance (i : Fin 3) : IsProbabilityMeasure (law i) := by
  unfold law
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable)

theorem sampleLaw_apply (s : Set Sample) :
    sampleLaw s=∑x:Sample, if x∈s then (1/64:ENNReal) else 0 := by
  classical
  rw [sampleLaw,Thompson.uniformActionMeasure,PMF.toMeasure_apply _ MeasurableSet.of_discrete,tsum_fintype]
  simp [Set.indicator, Fintype.card_prod]

theorem environment_apply (a : Bool) (s : Set (Feedback 3)) (hs : MeasurableSet s) :
    environment a s=∑x:Sample, if feedback a x∈s then (1/64:ENNReal) else 0 := by
  change (sampleLaw.map (feedback a)) s=_
  rw [Measure.map_apply Measurable.of_discrete hs,sampleLaw_apply]
  rfl

theorem law_apply (i : Fin 3) (s : Set UnitOutcome) (hs : MeasurableSet s) :
    law i s=∑x:Sample, if outcome x i∈s then (1/64:ENNReal) else 0 := by
  rw [law,Measure.map_apply Measurable.of_discrete hs,sampleLaw_apply]
  rfl

theorem environment_observed (a : Bool) (i : Fin 3) :
    environment a (observedSet i)=if i∈selected a then 1 else 1/2 := by
  rw [environment_apply a _ (measurableSet_observedSet i)]
  cases a <;> fin_cases i <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,observedSet,feedback,selected,show (0:Fin 3)≠2 by decide, show (⟨2,by decide⟩:Fin 3)=2 by rfl, show (2:Fin 3)≠0 by decide, show (2:Fin 3)≠1 by decide]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul,ENNReal.toReal_inv]
    norm_num

theorem observation_compatible (a : Bool) (i : Fin 3) :
    ObservationCompatible (environment a) (law i) i := by
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun z : Feedback 3 => z.2.1 i) := by fun_prop
  rw [Measure.map_apply hm hs,Measure.restrict_apply (hm hs),
    environment_apply a _ ((hm hs).inter (measurableSet_observedSet i)),Measure.smul_apply,environment_observed,
    law_apply i s hs]
  cases a <;> fin_cases i <;>
    by_cases h0 : bit false∈s <;> by_cases h1 : bit true∈s <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,observedSet,feedback,selected,
      outcome,Set.mem_inter_iff,Set.mem_preimage,h0,h1,smul_eq_mul,show (0:Fin 3)≠2 by decide, show (⟨2,by decide⟩:Fin 3)=2 by rfl, show (2:Fin 3)≠0 by decide, show (2:Fin 3)≠1 by decide]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_inv]
    norm_num

theorem reward_integrable (a : Bool) : Integrable (fun z => z.2.2) (environment a) := by
  change Integrable (fun z : Feedback 3 => z.2.2) (sampleLaw.map (feedback a))
  exact (integrable_map_measure (by fun_prop) Measurable.of_discrete.aemeasurable).2
    (Integrable.of_finite)

theorem reward_nonneg (a : Bool) : ∀ᵐ z ∂environment a, 0≤z.2.2 := by
  change ∀ᵐ z ∂sampleLaw.map (feedback a), 0≤z.2.2
  rw [ae_map_iff Measurable.of_discrete.aemeasurable (by measurability)]
  apply Filter.Eventually.of_forall
  intro x
  cases a <;> exact mul_nonneg (outcome x _).property.1 (outcome x _).property.1

noncomputable def model : FeedbackModel Bool 3 where
  selected := selected
  selected_injective := by
    intro a b h
    cases a <;> cases b
    · rfl
    · have hh := congrArg (fun t => (0:Fin 3)∈t) h
      norm_num [selected,show (0:Fin 3)≠2 by decide] at hh
    · have hh := congrArg (fun t => (0:Fin 3)∈t) h
      norm_num [selected,show (0:Fin 3)≠2 by decide] at hh
    · rfl
  possible := fun _ => Finset.univ
  possible_nonempty := fun _ => Finset.univ_nonempty
  selected_subset := fun _ => Finset.subset_univ _
  triggerable := fun _ => ⟨false,Finset.mem_univ _⟩
  environment := environment
  environment_markov := inferInstance
  laws := law
  laws_probability := fun _ => inferInstance
  observation_compatible := observation_compatible
  possible_iff_positive := by
    intro a i
    rw [environment_observed]
    by_cases h : i∈selected a <;> simp [h,ENNReal.toReal_inv]
  selected_observed := by
    intro a i hi
    simp [environment_observed,hi]
  reward_nonneg := reward_nonneg
  reward_integrable := reward_integrable

theorem mean_value (i : Fin 3) : marginalMean (law i)=if i=0 then 1/4 else if i=1 then 1/2 else 3/4 := by
  rw [marginalMean,law,integral_map Measurable.of_discrete.aemeasurable
    measurable_subtype_coe.aestronglyMeasurable]
  rw [sampleLaw,Thompson.uniformActionMeasure,PMF.integral_eq_sum]
  fin_cases i <;> norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,outcome,bit,
    Fintype.card_prod,smul_eq_mul,show (⟨2,by decide⟩:Fin 3)=2 by rfl,
    show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide]

theorem expected_reward (a : Bool) : model.expectedReward a=if a then 3/8 else 1/8 := by
  change (∫z : Feedback 3, z.2.2 ∂sampleLaw.map (feedback a))=_
  rw [integral_map Measurable.of_discrete.aemeasurable (by fun_prop),
    sampleLaw,Thompson.uniformActionMeasure,PMF.integral_eq_sum]
  cases a <;> norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,feedback,outcome,bit,
    Fintype.card_prod,smul_eq_mul,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide]

theorem law_one_mass (i : Fin 3) :
    (law i {bit true}).toReal=if i=0 then 1/4 else if i=1 then 1/2 else 3/4 := by
  rw [law_apply i _ (measurableSet_singleton _)]
  fin_cases i <;> norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,outcome,bit,
    show (⟨2,by decide⟩:Fin 3)=2 by rfl,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide]
  all_goals
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_inv]
    norm_num

theorem noisy_each_arm (i : Fin 3) : 0<(law i {bit true}).toReal ∧ (law i {bit true}).toReal<1 := by
  rw [law_one_mass]
  split_ifs <;> norm_num

theorem selected_size (a : Bool) : (selected a).card=2 := by
  cases a <;> norm_num [selected,show (1:Fin 3)≠2 by decide]

end BanditRLProof.CUCB.FiniteExample


