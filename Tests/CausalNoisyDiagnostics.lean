import Tests.CausalNoisyGraphCanary
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Exact diagnostics for the frozen noisy causal graph and actual learner. -/
namespace Tests.CausalNoisyGraphCanary
open BanditRLProof.Causal MeasureTheory
open scoped Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

def parentEquiv : noisyGraph.ParentConfig 2 ≃ Bool × Bool where
  toFun z := (z ⟨⟨0, by decide⟩, Finset.mem_univ _⟩,
    z ⟨⟨1, by decide⟩, Finset.mem_univ _⟩)
  invFun s := fun j => ![s.1,s.2] j.val
  left_inv z := by
    funext j
    rcases j with ⟨j,hj⟩
    fin_cases j <;> rfl
  right_inv s := by rcases s with ⟨x,w⟩; rfl

theorem parentEquiv_observation (x : Fin 3 → Bool) :
    parentEquiv (noisyGraph.parentConfig 2 (history x 2)) = (x 0,x 1) := rfl

theorem parent_mass (a : Fin 3) (z : noisyGraph.ParentConfig 2) :
    mass (noisyGraph.parentLaw (actions a) 2) z =
      (1/2) * (if a = 0 then
        if (parentEquiv z).1 = (parentEquiv z).2 then 3/4 else 1/4
        else if (parentEquiv z).2 = (a = 2) then 1 else 0) := by
  have heq (x : Fin 3 → Bool) :
      (z = noisyGraph.parentConfig 2 (history x 2)) ↔
        parentEquiv z = (x 0,x 1) := by
    rw [← parentEquiv_observation, Equiv.apply_eq_iff_eq]
  unfold mass GraphModel.parentLaw
  rw [PMF.map_apply, tsum_fintype, ← Equiv.sum_comp assignmentEquiv.symm]
  simp_rw [heq]
  obtain ⟨zw, rfl⟩ := parentEquiv.symm.surjective z
  rcases zw with ⟨x,w⟩
  fin_cases a <;> cases x <;> cases w <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, assignmentEquiv,
      actual_joint_factorization, xLaw, wLaw, yLaw, PMF.bernoulli_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Fin.ext_iff, NNReal.coe_sub,
      ENNReal.toReal_mul, ENNReal.toReal_add] <;>
    (simp (disch := first | finiteness | norm_num [ENNReal.div_le_iff, ENNReal.inv_le_one]) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le, ENNReal.toReal_inv, ENNReal.toReal_div,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]; norm_num)

noncomputable def parentLaws (a : Fin 3) := noisyGraph.parentLaw (actions a) 2
noncomputable def concentrated : PMF (Fin 3) := PMF.pure 0

@[simp] theorem concentrated_mixture : mixture concentrated parentLaws = parentLaws 0 := by
  simp [mixture, concentrated]

theorem concentrated_weights (a : Fin 3) : mass concentrated a = if a = 0 then 1 else 0 := by
  by_cases h : a = 0 <;> simp [mass, concentrated, PMF.pure_apply, h]

theorem concentrated_covers : Covers parentLaws (mixture concentrated parentLaws) := by
  intro a z _
  rw [concentrated_mixture]
  simp only [parentLaws, parent_mass]
  split_ifs <;> norm_num

theorem concentrated_secondMoment (a : Fin 3) :
    secondMoment (parentLaws a) (mixture concentrated parentLaws) =
      if a = 0 then 1 else 8/3 := by
  rw [concentrated_mixture]
  unfold secondMoment ratio
  rw [← Equiv.sum_comp parentEquiv.symm]
  fin_cases a <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, parentLaws, parent_mass, Fin.ext_iff]

theorem concentrated_cost : designCost parentLaws concentrated = 8/3 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    rw [concentrated_secondMoment]
    split_ifs <;> norm_num
  · have h := secondMoment_le_designCost parentLaws concentrated (1 : Fin 3)
    rw [concentrated_secondMoment] at h
    norm_num [Fin.ext_iff] at h ⊢
    exact h

theorem reward_parent_mass (z : noisyGraph.ParentConfig 2) :
    mass (noisyGraph.parentTable 2 z) true =
      if (parentEquiv z).1 then (if (parentEquiv z).2 then 4/5 else 2/5)
      else (if (parentEquiv z).2 then 3/5 else 1/5) := by
  obtain ⟨zw,rfl⟩ := parentEquiv.symm.surjective z
  rcases zw with ⟨x,w⟩
  change mass (yLaw x w) true =
    (if x then (if w then 4/5 else 2/5) else (if w then 3/5 else 1/5))
  cases x <;> cases w <;>
    norm_num [yLaw, mass, PMF.bernoulli_apply]

theorem concentrated_biases (a : Fin 3) :
    truncationBias (parentLaws a) (mixture concentrated parentLaws)
      (fun z => mass (noisyGraph.parentTable 2 z) true) 2 =
      if a = 0 then 0 else if a = 1 then 1/5 else 3/10 := by
  rw [concentrated_mixture]
  unfold truncationBias ratio
  rw [← Equiv.sum_comp parentEquiv.symm]
  fin_cases a <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, parentLaws, parent_mass,
      reward_parent_mass, Fin.ext_iff]

theorem uncovered_do_zero : ¬ Covers parentLaws (mixture (PMF.pure (1 : Fin 3)) parentLaws) := by
  intro hc
  have h := hc 2 (parentEquiv.symm (false,true))
  norm_num [mixture, parentLaws, parent_mass, Fin.ext_iff] at h

theorem observed_w_probability :
    (∑ z, if (parentEquiv z).2 then mass (parentLaws 0) z else 0) = 1/2 := by
  rw [← Equiv.sum_comp parentEquiv.symm]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, parentLaws, parent_mass]

/-- Conditional event probability from the actual observational joint and marginal. -/
theorem observed_conditional_reward :
    (∑ z, if (parentEquiv z).2 then
      mass ((joint (noisyGraph.doModel (actions 0)).table).map
        (fun x => (noisyGraph.parentConfig 2 (history x 2),x 2))) (z,true) else 0) /
    (∑ z, if (parentEquiv z).2 then mass (parentLaws 0) z else 0) = 3/4 := by
  rw [observed_w_probability, ← Equiv.sum_comp parentEquiv.symm]
  simp only [mass, noisyGraph.intervention_parent_mass (actions 0) 2
    (reward_not_intervened 0), ENNReal.toReal_mul]
  change (∑ z : Bool × Bool, if (parentEquiv (parentEquiv.symm z)).2 then
    mass (parentLaws 0) (parentEquiv.symm z) *
    mass (noisyGraph.parentTable 2 (parentEquiv.symm z)) true else 0) / (1/2) = 3/4
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, parentLaws, parent_mass,
    reward_parent_mass]

theorem conditional_differs_from_intervention :
    (3/4 : ℝ) ≠ noisyGraph.rewardMean id actions 2 2 := by
  norm_num [reward_means, Fin.ext_iff]

theorem log_six_bounds : (3/2 : ℝ) < Real.log 6 ∧ Real.log 6 < 8/3 := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have h6 : Real.log 6 = Real.log 4 + Real.log (3/2) := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3/2 : ℝ) ≠ 0)]
    norm_num
  have hlo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3/2)
  have hu := Real.strictMonoOn_log (by norm_num : (6 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (8 : ℝ) ∈ Set.Ioi 0) (by norm_num : (6 : ℝ) < 8)
  rw [h8] at hu
  constructor
  · rw [h6,h4]; norm_num at hlo; linarith
  · linarith

noncomputable def oneRoundThreshold : ℝ :=
  sourceThreshold (designCost parentLaws concentrated) 1 (sourceLog 1 3)

theorem oneRoundThreshold_bounds : 1 < oneRoundThreshold ∧ oneRoundThreshold < 4/3 := by
  have hL : 0 < Real.log 6 := by linarith [log_six_bounds.1]
  have hsq : oneRoundThreshold ^ 2 = (8/3) / Real.log 6 := by
    unfold oneRoundThreshold
    rw [concentrated_cost, sourceThreshold_sq _ _ _ (by norm_num) (by norm_num)
      (by norm_num [sourceLog]; exact hL.le)]
    norm_num [sourceLog]
  have hpos : 0 ≤ oneRoundThreshold := Real.sqrt_nonneg _
  have hlo : (1 : ℝ) < (8/3) / Real.log 6 := by
    apply (lt_div_iff₀ hL).2
    nlinarith [log_six_bounds.2]
  have hup : (8/3 : ℝ) / Real.log 6 < (4/3)^2 := by
    apply (div_lt_iff₀ hL).2
    nlinarith [log_six_bounds.1]
  constructor <;> nlinarith

theorem oneRound_estimates (B : ℝ) (hB : 1 ≤ B) (hB' : B < 4/3)
    (w : Fin 1 → Fin 3 × (Fin 3 → Bool)) (a : Fin 3) :
    noisyGraph.sampleEstimate id actions concentrated 2 a B w =
      if a = 0 then (if (w 0).2 2 then 1 else 0) else 0 := by
  simp only [GraphModel.sampleEstimate, Fin.sum_univ_one, Nat.cast_one, div_one]
  change weightedBit (parentLaws a) (mixture concentrated parentLaws) B
    (noisyGraph.observation id 2 (w 0)) = _
  rw [concentrated_mixture]
  have h4 : B < 4 := by linarith
  simp only [weightedBit, GraphModel.observation, ratio, parentLaws, parent_mass,
    parentEquiv_observation, id_eq]
  fin_cases a <;> rcases Bool.eq_false_or_eq_true ((w 0).2 0) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true ((w 0).2 1) with hw | hw <;>
    rcases Bool.eq_false_or_eq_true ((w 0).2 2) with hy | hy <;>
    norm_num [hx,hw,hy,Fin.ext_iff, hB, not_le.mpr hB', not_le.mpr h4]

theorem oneRound_recommendation (B : ℝ) (hB : 1 ≤ B) (hB' : B < 4/3)
    (w : Fin 1 → Fin 3 × (Fin 3 → Bool)) :
    noisyGraph.sampleRecommendation id actions concentrated 2 B w = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  apply orderedArgmax_le_of_maximal
  intro a
  rw [oneRound_estimates B hB hB', oneRound_estimates B hB hB']
  simp only [if_true]
  split_ifs <;> norm_num

theorem oneRound_regret (w : Fin 1 → Fin 3 × (Fin 3 → Bool)) :
    noisyGraph.simpleRegret id actions concentrated 2 oneRoundThreshold w = 1/5 := by
  have hu (a : Fin 3) : noisyGraph.rewardMean id actions 2 a ≤ 7/10 := by
    rw [reward_means]; split_ifs <;> norm_num
  have hm : noisyGraph.rewardMean id actions 2
      (BanditRLProof.FiniteRealArgmax.choose (noisyGraph.rewardMean id actions 2)) = 7/10 := by
    apply le_antisymm (hu _)
    have h := BanditRLProof.FiniteRealArgmax.score_le_choose (noisyGraph.rewardMean id actions 2) 2
    have htwo : noisyGraph.rewardMean id actions 2 2 = 7/10 := by
      rw [reward_means]; norm_num [Fin.ext_iff]
    rw [htwo] at h
    exact h
  unfold GraphModel.simpleRegret
  rw [hm, oneRound_recommendation _ oneRoundThreshold_bounds.1.le oneRoundThreshold_bounds.2]
  norm_num [reward_means]

theorem oneRound_expected_regret :
    (∫ w, noisyGraph.simpleRegret id actions concentrated 2 oneRoundThreshold w
      ∂noisyGraph.sampleLaw actions concentrated 1) = 1/5 := by
  simp_rw [oneRound_regret]
  simp

theorem concentrated_actual_rate (T : ℕ) (hT : 0 < T) :
    let L := sourceLog T 3
    let B := sourceThreshold (8/3) T L
    (∫ w, noisyGraph.simpleRegret id actions concentrated 2 B w
      ∂noisyGraph.sampleLaw actions concentrated T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((8/3)*L/T)+1/(T:ℝ) := by
  have h := noisyGraph.expected_simpleRegret_source_bound id actions concentrated 2
    reward_not_intervened concentrated_covers T hT
  change (let m := designCost parentLaws concentrated
          let L := sourceLog T 3
          let B := sourceThreshold m T L
          (∫ w, noisyGraph.simpleRegret id actions concentrated 2 B w
            ∂noisyGraph.sampleLaw actions concentrated T) ≤
            (2*Real.sqrt 2+7)*Real.sqrt (m*L/T)+1/(T:ℝ)) at h
  simpa only [concentrated_cost] using h

#print axioms concentrated_cost
#print axioms concentrated_biases
#print axioms uncovered_do_zero
#print axioms observed_conditional_reward
#print axioms oneRound_expected_regret
#print axioms concentrated_actual_rate

end Tests.CausalNoisyGraphCanary
