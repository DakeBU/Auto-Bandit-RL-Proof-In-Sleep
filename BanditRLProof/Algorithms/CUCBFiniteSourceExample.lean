import BanditRLProof.Algorithms.CUCBFiniteExample
import BanditRLProof.Algorithms.CUCBPolynomialRegret

/-! Concrete nonlinear score and input-dependent maximizing oracle for the
finite noisy feedback model. Ties choose the inferior true-reward action. -/
namespace BanditRLProof.CUCB.FiniteExample
open MeasureTheory ProbabilityTheory
open scoped Classical
set_option autoImplicit false

def score (v : Input 3) (a : Bool) : ℝ :=
  if a then (v 1:ℝ)*(v 2:ℝ) else (v 0:ℝ)*(v 1:ℝ)
noncomputable def choose (v : Input 3) : Bool :=
  if score v false < score v true then true else false

theorem measurable_choose : Measurable choose := by
  apply Measurable.ite
  · exact measurableSet_lt (by change Measurable (fun v : Input 3 => (v 0:ℝ)*(v 1:ℝ)); fun_prop)
      (by change Measurable (fun v : Input 3 => (v 1:ℝ)*(v 2:ℝ)); fun_prop)
  · exact measurable_const
  · exact measurable_const

theorem choose_max (v : Input 3) : scoreOptimum score v≤score v (choose v) := by
  apply Finset.sup'_le
  intro a ha
  cases a <;> unfold choose <;> split_ifs with h
  · exact le_of_lt h
  · exact le_rfl
  · exact le_rfl
  · exact le_of_not_gt h

theorem product_smooth (x y u v : UnitOutcome) (L : ℝ) (hL : 0≤L)
    (hx : |(x:ℝ)-u|≤L) (hy : |(y:ℝ)-v|≤L) :
    |(x:ℝ)*y-(u:ℝ)*v|≤2*L := by
  have hxu := abs_le.mp hx
  have hyv := abs_le.mp hy
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg (show 0≤L+((x:ℝ)-u) by linarith) y.property.1,
      mul_nonneg hL (sub_nonneg.mpr y.property.2),
      mul_nonneg u.property.1 (show 0≤L+((y:ℝ)-v) by linarith),
      mul_nonneg hL (sub_nonneg.mpr u.property.2)]
  · nlinarith [mul_nonneg (show 0≤L-((x:ℝ)-u) by linarith) y.property.1,
      mul_nonneg hL (sub_nonneg.mpr y.property.2),
      mul_nonneg u.property.1 (show 0≤L-((y:ℝ)-v) by linarith),
      mul_nonneg hL (sub_nonneg.mpr u.property.2)]

noncomputable def source : SourceModel model where
  score := score
  score_nonneg := by intro v a; cases a <;> exact mul_nonneg (v _).property.1 (v _).property.1
  score_true := by
    intro a
    rw [expected_reward]
    change (if a then marginalMean (law 1)*marginalMean (law 2)
      else marginalMean (law 0)*marginalMean (law 1))=_
    cases a <;> norm_num [mean_value,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide]
  modulus := fun x => 2*x
  modulus_zero := by ring
  modulus_continuous := by fun_prop
  modulus_strictMono := by intro x hx y hy h; dsimp; linarith
  score_monotone := by
    intro v w h a
    cases a <;> exact mul_le_mul (h _) (h _) (v _).property.1 (w _).property.1
  score_smooth := by
    intro v w a L hL h
    have hh (i : Fin 3) : |(v i:ℝ)-(w i:ℝ)|≤L := h i (Finset.mem_univ i)
    cases a <;> exact product_smooth _ _ _ _ L hL (hh _) (hh _)
  alpha := 1
  beta := 1
  alpha_mem := by norm_num
  beta_mem := by norm_num
  oracle := Kernel.deterministic choose measurable_choose
  oracle_markov := inferInstance
  oracle_success := by
    intro v
    simp only [Kernel.deterministic_apply,Measure.dirac_apply' _ MeasurableSet.of_discrete,
      one_mul,ENNReal.ofReal_one]
    simp [choose_max]
  inverse_range := by
    intro d hd hD
    exact ⟨d/2,by positivity,by ring⟩

theorem trigger_value (a : Bool) (i : Fin 3) :
    model.triggerProbability a i=if i∈selected a then 1 else 1/2 := by
  change (environment a (observedSet i)).toReal=_
  rw [environment_observed]
  split_ifs <;> norm_num [ENNReal.toReal_inv]

theorem minTrigger_value (i : Fin 3) : model.minTrigger i=if i=1 then 1 else 1/2 := by
  apply le_antisymm
  · fin_cases i
    · have h := model.minTrigger_le true 0 (Finset.mem_univ _)
      simpa [trigger_value,selected,show (0:Fin 3)≠2 by decide] using h
    · have h := model.minTrigger_le false 1 (Finset.mem_univ _)
      simpa [trigger_value,selected] using h
    · have h := model.minTrigger_le false 2 (Finset.mem_univ _)
      simpa [trigger_value,selected,show (⟨2,by decide⟩:Fin 3)=2 by rfl,
        show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide] using h
  · apply Finset.le_inf'
    intro a ha
    rw [trigger_value]
    by_cases hi : i=1
    · subst i; cases a <;> simp [selected]
    · simp only [hi,ite_false]
      split_ifs <;> norm_num

theorem globalMinTrigger_value : model.globalMinTrigger=1/2 := by
  apply le_antisymm
  · have h := model.globalMinTrigger_le 0
    simpa [minTrigger_value] using h
  · apply Finset.le_inf'
    intro i hi
    rw [minTrigger_value]
    split_ifs <;> norm_num

theorem true_score (a : Bool) : score model.trueInput a=if a then 3/8 else 1/8 := by
  exact (source.score_true a).trans (expected_reward a)

theorem true_optimum : scoreOptimum score model.trueInput=3/8 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    rw [true_score]
    cases a <;> norm_num
  · simpa [true_score] using score_le_optimum score model.trueInput true

theorem max_gap : maxPositiveGap source.score model.trueInput source.alpha=1/4 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    change max 0 (1*scoreOptimum score model.trueInput-score model.trueInput a)≤1/4
    rw [true_optimum,true_score]
    cases a <;> norm_num
  · have h := gap_le_maxPositiveGap score model.trueInput 1 false
    change 1/4≤maxPositiveGap score model.trueInput 1
    norm_num [sourceGap,true_optimum,true_score] at h
    linarith

theorem choose_initial : choose (initialInput 3)=false := by
  norm_num [choose,score,initialInput]

theorem initial_action_gap : source.gap (choose (initialInput 3))=1/4 := by
  rw [choose_initial]
  change 1*scoreOptimum score model.trueInput-score model.trueInput false=1/4
  norm_num [true_optimum,true_score]

theorem probabilistic_regret (H : ℕ) (hH : 1≤H) :
    source.approximationRegret H≤
      4*(72*Real.log (H:ℝ))^((1:ℝ)/2)*(H:ℝ)^((1:ℝ)/2)+
      (1+Real.pi^2/2)*(3/4)+30*Real.log (H:ℝ) := by
  have h := source.theorem_two_probabilistic H hH
    (by rw [globalMinTrigger_value]; norm_num) 2 1 (by norm_num) (by norm_num)
    (by norm_num) (by intro u hu; simp [source])
  rw [globalMinTrigger_value,max_gap] at h
  simp only [minTrigger_value] at h
  norm_num [Fin.sum_univ_succ,show (⟨2,by decide⟩:Fin 3)=2 by rfl,
    show (2:Fin 3)≠1 by decide] at h
  convert h using 1; ring_nf

noncomputable def randomizedSource : SourceModel model :=
  { source with
    beta := 1/2
    beta_mem := by norm_num
    oracle := Kernel.const (Input 3) (Thompson.uniformActionMeasure Bool)
    oracle_markov := inferInstance
    oracle_success := by
      intro v
      have hsub : {choose v} ⊆ {a | scoreOptimum score v≤score v a} :=
        Set.singleton_subset_iff.mpr (choose_max v)
      have h := measure_mono (μ:=Thompson.uniformActionMeasure Bool) hsub
      have he : Thompson.uniformActionMeasure Bool {choose v}=(1/2:ENNReal) := by
        rw [Thompson.uniformActionMeasure,PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
        simp
      rw [he] at h
      simpa [source] using h }

theorem randomized_action_mass (v : Input 3) (a : Bool) :
    randomizedSource.oracle v {a}=(1/2:ENNReal) := by
  change Thompson.uniformActionMeasure Bool {a}=_
  rw [Thompson.uniformActionMeasure,PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  simp

theorem randomized_probabilistic_regret (H : ℕ) (hH : 1≤H) :
    randomizedSource.approximationRegret H≤
      4*(72*Real.log (H:ℝ))^((1:ℝ)/2)*(H:ℝ)^((1:ℝ)/2)+
      (1+Real.pi^2/2)*(3/4)+30*Real.log (H:ℝ) := by
  have h := randomizedSource.theorem_two_probabilistic H hH
    (by rw [globalMinTrigger_value]; norm_num) 2 1 (by norm_num) (by norm_num)
    (by norm_num) (by intro u hu; simp [randomizedSource,source])
  have hg : maxPositiveGap randomizedSource.score model.trueInput randomizedSource.alpha=1/4 := max_gap
  rw [globalMinTrigger_value,hg] at h
  simp only [minTrigger_value] at h
  norm_num [Fin.sum_univ_succ,show (⟨2,by decide⟩:Fin 3)=2 by rfl,
    show (2:Fin 3)≠1 by decide] at h
  convert h using 1; ring_nf

noncomputable def noBadSource : SourceModel model :=
  { source with
    alpha := 1/3
    alpha_mem := by norm_num
    oracle_success := by
      intro v
      have hn : 0≤scoreOptimum score v :=
        (source.score_nonneg v false).trans (score_le_optimum score v false)
      have h : (1/3)*scoreOptimum score v≤score v (choose v) := by
        nlinarith [choose_max v]
      change ENNReal.ofReal 1≤Measure.dirac (choose v) {a | (1/3)*scoreOptimum score v≤score v a}
      rw [ENNReal.ofReal_one,Measure.dirac_apply_of_mem (a:=choose v) (s:={a | (1/3)*scoreOptimum score v≤score v a}) h]
    inverse_range := by intro d hd hD; exact ⟨d/2,by positivity,by change 2*(d/2)=d; ring⟩ }

theorem no_bad_regret (H : ℕ) : noBadSource.approximationRegret H≤0 := by
  apply noBadSource.approximationRegret_nonpos_of_no_bad
  intro a
  change (1/3)*scoreOptimum score model.trueInput-score model.trueInput a≤0
  rw [true_optimum,true_score]
  cases a <;> norm_num

theorem first_action_law :
    (cucbTrajectory source.oracle model.environment).map (fun Y => (Y 0).1)=Measure.dirac false := by
  have he : (cucbTrajectory source.oracle model.environment).map (fun Y => (Y 0).1)=
      ((cucbTrajectory source.oracle model.environment).map (fun Y => Y 0)).map Prod.fst :=
    (Measure.map_map measurable_fst (by fun_prop)).symm
  rw [he,cucbTrajectory_initial_law,roundKernel_action_law]
  change Measure.dirac (choose (initialInput 3))=Measure.dirac false
  rw [choose_initial]

theorem regret_one_positive : source.approximationRegret 1=1/4 := by
  have hi := integral_map (μ:=cucbTrajectory source.oracle model.environment)
    (by fun_prop : Measurable (fun Y : ℕ → Round Bool 3 => (Y 0).1)).aemeasurable
    (Measurable.of_discrete : Measurable (score model.trueInput)).aestronglyMeasurable
  rw [first_action_law,integral_dirac] at hi
  have he : (∫Y : ℕ → Round Bool 3, score model.trueInput (Y 0).1
      ∂cucbTrajectory source.oracle model.environment)=1/8 := by
    simpa [true_score] using hi.symm
  rw [source.approximationRegret_eq_mean]
  norm_num only [Nat.cast_one]
  change (1:ℝ)*1*1*scoreOptimum score model.trueInput-
    (∫Y : ℕ → Round Bool 3, ∑t∈Finset.range 1, score model.trueInput (Y t).1
      ∂cucbTrajectory source.oracle model.environment)=1/4
  simp only [Finset.sum_range_one,one_mul]
  rw [he,true_optimum]
  norm_num

theorem refined_regret (H : ℕ) (hH : 1≤H) :
    source.approximationRegret H≤(∑i:Fin 3,source.armRefinedTerm H i)+(1+Real.pi^2/2)*(3/4) := by
  have h := source.theorem_one_refined_regret H hH
  rw [globalMinTrigger_value,max_gap] at h
  norm_num at h
  convert h using 1; ring

end BanditRLProof.CUCB.FiniteExample



