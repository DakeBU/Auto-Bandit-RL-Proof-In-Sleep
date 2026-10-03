import BanditRLProof.Algorithms.CausalHeterogeneousRegret
import BanditRLProof.Algorithms.CausalHeterogeneousLaw

/-! A three-valued parent and a two-valued noisy reward; a genuinely dependent state space. -/
namespace Tests.CausalHeterogeneousCanary
open BanditRLProof.Causal MeasureTheory
open scoped Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

abbrev Values (i : Fin 2) := Fin (if i = 0 then 3 else 2)
instance valuesSize_neZero (i : Fin 2) : NeZero (if i = 0 then 3 else 2) :=
  ⟨by split_ifs <;> decide⟩

noncomputable def noisyReward (x : Fin 3) : PMF (Fin 2) :=
  (PMF.bernoulli (if x = 2 then 3/4 else 1/4) (by split_ifs <;> norm_num [div_le_iff₀])).map
    (fun b => if b then 1 else 0)

noncomputable def tables : NodeTables Values := by
  refine Fin.cases (fun _ => PMF.uniformOfFintype (Fin 3)) ?_
  exact Fin.cases (fun h => noisyReward (h ⟨0, by decide⟩)) (fun k => Fin.elim0 k)

noncomputable def graph : NodeGraphModel Values where
  parents _ := Finset.univ
  table := tables
  local_table := by
    intro i h h' heq
    have hh : h = h' := funext fun j => heq j (Finset.mem_univ _)
    rw [hh]

def actions (a : Fin 3) : (i : Fin 2) → Option (Values i) := by
  refine Fin.cases (if a = 0 then none else some (if a = 1 then 0 else 2)) ?_
  exact Fin.cases none (fun k => Fin.elim0 k)

def rewardBit (x : Values 1) : Bool := decide (x = 1)

theorem reward_untouched (a : Fin 3) : actions a 1 = none := rfl

@[simp] theorem actions_zero (a : Fin 3) : actions a 0 =
    (if a = 0 then none else some (if a = 1 then 0 else 2)) := rfl

@[simp] theorem tables_zero (h : NodeHistory Values 0) :
    tables 0 h = PMF.uniformOfFintype (Fin 3) := rfl

@[simp] theorem tables_one (h : NodeHistory Values 1) :
    tables 1 h = noisyReward (h ⟨0, by decide⟩) := rfl

def assignmentEquiv : ((i : Fin 2) → Values i) ≃ Fin 3 × Fin 2 where
  toFun x := (x 0,x 1)
  invFun xy := by
    refine Fin.cases xy.1 ?_
    exact Fin.cases xy.2 (fun k => Fin.elim0 k)
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv xy := by rcases xy with ⟨x,y⟩; rfl

@[simp] theorem assignment_zero (xy : Fin 3 × Fin 2) :
    assignmentEquiv.symm xy 0 = xy.1 := rfl

@[simp] theorem assignment_one (xy : Fin 3 × Fin 2) :
    assignmentEquiv.symm xy 1 = xy.2 := rfl

theorem actual_joint (a : Fin 3) (x : (i : Fin 2) → Values i) :
    nodeJoint (nodeIntervene graph.table (actions a)) x =
      (if a = 0 then 1/3 else if x 0 = (if a = 1 then 0 else 2) then 1 else 0) *
        noisyReward (x 0) (x 1) := by
  rw [nodeIntervention_factorization]
  fin_cases a <;> norm_num [Fin.prod_univ_two, graph, reward_untouched, nodeHistory,
    PMF.uniformOfFintype_apply]
  · change PMF.uniformOfFintype (Fin 3) (x 0) * noisyReward (x 0) (x 1) = _
    norm_num [PMF.uniformOfFintype_apply]
  · rfl
  · rfl

theorem reward_means (a : Fin 3) : graph.rewardMean actions 1 rewardBit a =
    if a = 0 then 5/12 else if a = 1 then 1/4 else 3/4 := by
  rw [NodeGraphModel.rewardMean, PMF.integral_eq_sum, ← Equiv.sum_comp assignmentEquiv.symm]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
    actual_joint, assignment_zero, assignment_one]
  dsimp [rewardBit, Values, noisyReward]
  fin_cases a <;>
    norm_num [rewardBit, noisyReward, PMF.map_apply,
      tsum_fintype, Fintype.sum_bool, PMF.bernoulli_apply, smul_eq_mul,
      ENNReal.toReal_mul, Fin.ext_iff, Values]

theorem uniform_actual_rate (T : ℕ) (hT : 0 < T) :
    let eta := PMF.uniformOfFintype (Fin 3)
    let m := designCost (fun a => graph.parentLaw (actions a) 1) eta
    let L := sourceLog T 3
    let B := sourceThreshold m T L
    (∫ w, graph.simpleRegret actions eta 1 rewardBit B w ∂graph.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (3*L/T)+1/(T:ℝ) := by
  simpa only [Fintype.card_fin] using graph.expected_simpleRegret_uniform actions
    1 rewardBit reward_untouched T hT

#print axioms actual_joint
#print axioms reward_means
#print axioms uniform_actual_rate
#print axioms NodeGraphModel.expected_simpleRegret_source_bound
#print axioms NodeGraphModel.expected_simpleRegret_explicit_rate

end Tests.CausalHeterogeneousCanary
