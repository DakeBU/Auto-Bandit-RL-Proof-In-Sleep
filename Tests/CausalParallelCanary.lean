import BanditRLProof.Algorithms.CausalParallelRegret

/-! Full-support and deterministic-root witnesses for the actual parallel construction. -/
namespace Tests.CausalParallelCanary
open BanditRLProof.Causal MeasureTheory
open scoped Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
noncomputable section

def fair : ParallelParameters 2 where
  q _ := 1/2
  nonneg _ := by norm_num
  le_one _ := by norm_num
  two_le := by norm_num

def deterministic : ParallelParameters 2 where
  q _ := 0
  nonneg _ := le_rfl
  le_one _ := by norm_num
  two_le := by norm_num

theorem two_node_rarity (p : ParallelParameters 2) : p.rarity = 2 := by
  have h := p.rarity_spec
  omega

theorem fair_rare_empty : fair.rareActions = ∅ := by
  ext a
  rcases a with ⟨i,b⟩
  cases b <;> norm_num [ParallelParameters.rareActions,two_node_rarity,
    ParallelParameters.valueProbability,fair]

theorem deterministic_rare_card : deterministic.rareActions.card = 2 := by
  simp only [ParallelParameters.rareActions,two_node_rarity,
    ParallelParameters.valueProbability,deterministic,Finset.card_eq_sum_ones,
    Finset.sum_filter,Fintype.sum_prod_type,Fin.sum_univ_two,Fintype.sum_bool]
  norm_num

theorem fair_weights (a : Option (Fin 2 × Bool)) : mass fair.allocation a =
    match a with | none => 1 | some _ => 0 := by
  rw [ParallelParameters.allocation_mass]
  cases a <;> simp [ParallelParameters.allocationWeight,ParallelParameters.atomicTotal,
    fair_rare_empty]

theorem deterministic_weights (a : Option (Fin 2 × Bool)) : mass deterministic.allocation a =
    match a with | none => 1/2 | some b => if b.2 then 1/4 else 0 := by
  rw [ParallelParameters.allocation_mass]
  cases a with
  | none => norm_num [ParallelParameters.allocationWeight,ParallelParameters.atomicTotal,
      deterministic_rare_card,ParallelParameters.rareWeight,two_node_rarity]
  | some a => rcases a with ⟨i,b⟩; cases b <;>
      norm_num [ParallelParameters.allocationWeight,ParallelParameters.rareActions,
        ParallelParameters.rareWeight,two_node_rarity,ParallelParameters.valueProbability,deterministic]

def stateEquiv : (Fin 2 → Bool) ≃ Bool × Bool where
  toFun x := (x 0,x 1)
  invFun s := ![s.1,s.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv s := by rcases s with ⟨x,y⟩; rfl

theorem fair_full_support (x : Fin 2 → Bool) : mass (fair.rootLaw none) x = 1/4 := by
  rw [ParallelParameters.rootLaw_mass]
  simp only [Fin.prod_univ_two,ParallelParameters.valueProbability,fair]
  rcases Bool.eq_false_or_eq_true (x 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (x 1) with h1 | h1 <;> norm_num [h0,h1]

theorem fair_secondMoment (a : Option (Fin 2 × Bool)) :
    secondMoment (fair.rootLaw a) (mixture fair.allocation fair.rootLaw) =
      match a with | none => 1 | some _ => 2 := by
  unfold secondMoment ratio
  rw [← Equiv.sum_comp stateEquiv.symm]
  simp only [mixture_mass, fair_weights]
  cases a with
  | none =>
    norm_num [Fintype.sum_prod_type,Fintype.sum_bool,mixture_mass,Fintype.sum_option,
      fair_weights,fair_full_support]
  | some a =>
    rcases a with ⟨i,b⟩
    fin_cases i <;> cases b <;>
      (simp only [Fintype.sum_prod_type,Fintype.sum_bool,mixture_mass,Fintype.sum_option,
        fair_weights,ParallelParameters.rootLaw_mass,Fin.prod_univ_two,
        ParallelParameters.valueProbability,fair,stateEquiv,Matrix.cons_val_zero,Matrix.cons_val_one,
        Fin.reduceFinMk,Fin.ext_iff]
       norm_num)

theorem fair_cost : designCost fair.rootLaw fair.allocation = 2 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    rw [fair_secondMoment]
    cases a <;> norm_num
  · have h := secondMoment_le_designCost fair.rootLaw fair.allocation (some (0,true))
    rwa [fair_secondMoment] at h

theorem deterministic_rare_secondMoment :
    secondMoment (deterministic.rootLaw (some (0,true)))
      (mixture deterministic.allocation deterministic.rootLaw) = 4 := by
  unfold secondMoment ratio
  rw [← Equiv.sum_comp stateEquiv.symm]
  simp only [mixture_mass, deterministic_weights]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,mixture_mass,Fintype.sum_option,
    Fin.sum_univ_two,deterministic_weights,ParallelParameters.rootLaw_mass,
    Fin.prod_univ_two,ParallelParameters.valueProbability,deterministic,stateEquiv,
    Matrix.cons_val_zero,Matrix.cons_val_one,Fin.reduceFinMk,Fin.ext_iff]
  norm_num

theorem deterministic_cost_tight : designCost deterministic.rootLaw deterministic.allocation =
    2*deterministic.rarity := by
  apply le_antisymm deterministic.allocation_cost_le
  have h := secondMoment_le_designCost deterministic.rootLaw deterministic.allocation (some (0,true))
  rw [deterministic_rare_secondMoment] at h
  norm_num only [two_node_rarity, Nat.cast_ofNat] at ⊢
  exact h

theorem deterministic_observation_not_covering :
    ¬ Covers deterministic.rootLaw (deterministic.rootLaw none) := by
  intro h
  have hx := h (some (0,true)) ![true,false]
  simp only [ParallelParameters.rootLaw_mass,Fin.prod_univ_two,
    ParallelParameters.valueProbability,deterministic,Matrix.cons_val_zero,Matrix.cons_val_one,Fin.reduceFinMk,
    Fin.ext_iff] at hx
  norm_num at hx

local instance : LinearOrder (Option (Fin 2 × Bool)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
local instance : MeasurableSpace (Option (Fin 2 × Bool)) := ⊤
local instance : MeasurableSingletonClass (Option (Fin 2 × Bool)) := ⟨fun _ => trivial⟩

def noisyReward (x : Fin 2 → Bool) : PMF Bool :=
  PMF.bernoulli (if x 0 || x 1 then 3/4 else 1/4) (by split_ifs <;> norm_num [div_le_iff₀])

theorem fair_actual_rate (T : ℕ) (hT : 0 < T) :
    let L := sourceLog T 5
    let B := sourceThreshold 2 T L
    (∫ w, (fair.graph noisyReward).simpleRegret id ParallelParameters.graphAction
      fair.allocation (Fin.last 2) B w
      ∂(fair.graph noisyReward).sampleLaw ParallelParameters.graphAction fair.allocation T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (4*L/T)+1/(T:ℝ) := by
  have h := fair.expected_simpleRegret_parallel noisyReward T hT
  dsimp only at h ⊢
  norm_num only [fair_cost,two_node_rarity,Fintype.card_option,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool,Nat.cast_ofNat] at h
  exact h

theorem deterministic_actual_rate (T : ℕ) (hT : 0 < T) :
    let L := sourceLog T 5
    let B := sourceThreshold 4 T L
    (∫ w, (deterministic.graph noisyReward).simpleRegret id ParallelParameters.graphAction
      deterministic.allocation (Fin.last 2) B w
      ∂(deterministic.graph noisyReward).sampleLaw ParallelParameters.graphAction deterministic.allocation T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (4*L/T)+1/(T:ℝ) := by
  have h := deterministic.expected_simpleRegret_parallel noisyReward T hT
  dsimp only at h ⊢
  norm_num only [deterministic_cost_tight,two_node_rarity,Fintype.card_option,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool,Nat.cast_ofNat] at h
  exact h

#print axioms fair_cost
#print axioms deterministic_cost_tight
#print axioms deterministic_observation_not_covering
#print axioms fair_actual_rate
#print axioms deterministic_actual_rate
#print axioms ParallelParameters.expected_simpleRegret_parallel_optimal

end
end Tests.CausalParallelCanary
