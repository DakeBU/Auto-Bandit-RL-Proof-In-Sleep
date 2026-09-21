import BanditRLProof.Algorithms.CausalAllocationRegret

/-! Frozen noisy X -> W, X -> Y, W -> Y graph. This file begins the concrete
canary; exact tuned one-round regret and design arithmetic remain obligations. -/
namespace Tests.CausalNoisyGraphCanary
open BanditRLProof.Causal MeasureTheory
open scoped Classical
set_option maxHeartbeats 800000

noncomputable def xLaw : PMF Bool := PMF.bernoulli (1/2) (by norm_num)

noncomputable def wLaw (x : Bool) : PMF Bool :=
  PMF.bernoulli (if x then 3/4 else 1/4) (by cases x <;> norm_num [div_le_iff₀])

noncomputable def yLaw (x w : Bool) : PMF Bool :=
  PMF.bernoulli (if x then (if w then 4/5 else 2/5) else (if w then 3/5 else 1/5))
    (by cases x <;> cases w <;> norm_num [div_le_iff₀])

noncomputable def noisyTables : Tables Bool 3 := fun i h =>
  if hi : i = 0 then xLaw
  else if hi1 : i = 1 then wLaw (h ⟨0, by omega⟩)
  else yLaw (h ⟨0, by omega⟩) (h ⟨1, by omega⟩)

noncomputable def noisyGraph : GraphModel Bool 3 where
  parents _ := Finset.univ
  table := noisyTables
  local_table := by
    intro i h h' heq
    have hh : h = h' := funext fun j => heq j (Finset.mem_univ _)
    rw [hh]

/-- The empty intervention is first in the fixed tie order. -/
def actions (a : Fin 3) (i : Fin 3) : Option Bool :=
  if i = 1 then (if a = 0 then none else some (a = 2)) else none

theorem reward_not_intervened (a : Fin 3) : actions a 2 = none := by
  simp [actions]

theorem actual_joint_factorization (a : Fin 3) (x : Fin 3 → Bool) :
    joint (noisyGraph.doModel (actions a)).table x =
      xLaw (x 0) *
        (if a = 0 then wLaw (x 0) (x 1) else if x 1 = (a = 2) then 1 else 0) *
        yLaw (x 0) (x 1) (x 2) := by
  rw [doModel_factorization]
  fin_cases a <;> simp [Fin.prod_univ_succ, actions, noisyGraph, noisyTables, history]
  <;> ring

def assignmentEquiv : (Fin 3 → Bool) ≃ Bool × Bool × Bool where
  toFun x := (x 0, x 1, x 2)
  invFun s := ![s.1,s.2.1,s.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv s := by rcases s with ⟨x,w,y⟩; rfl

theorem reward_means (a : Fin 3) : noisyGraph.rewardMean id actions 2 a =
    if a = 0 then 1/2 else if a = 1 then 3/10 else 7/10 := by
  rw [noisyGraph.rewardMean_eq_integral id actions 2 a (reward_not_intervened a),
    PMF.integral_eq_sum]
  rw [← Equiv.sum_comp assignmentEquiv.symm]
  fin_cases a <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, assignmentEquiv,
      actual_joint_factorization, xLaw, wLaw, yLaw, PMF.bernoulli_apply,
      smul_eq_mul, ENNReal.toReal_mul, Matrix.cons_val, Fin.reduceFinMk,
      NNReal.coe_sub] <;>
    norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff, NNReal.coe_sub,
      ENNReal.toReal_mul] <;>
    rw [show (1 - 3/4 : NNReal) = 1/4 by
          apply Subtype.ext
          norm_num [NNReal.coe_sub_def],
        show (1 - 1/4 : NNReal) = 3/4 by
          apply Subtype.ext
          norm_num [NNReal.coe_sub_def]]
  norm_num

theorem uniform_actual_rate (T : ℕ) (hT : 0 < T) :
    let eta := PMF.uniformOfFintype (Fin 3)
    let m := designCost (fun a => noisyGraph.parentLaw (actions a) 2) eta
    let L := sourceLog T 3
    let B := sourceThreshold m T L
    (∫ w, noisyGraph.simpleRegret id actions eta 2 B w ∂noisyGraph.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (3*L/T)+1/(T:ℝ) := by
  simpa only [Fintype.card_fin] using
    noisyGraph.expected_simpleRegret_uniform id actions 2 reward_not_intervened T hT

#print axioms actual_joint_factorization
#print axioms reward_means
#print axioms uniform_actual_rate
#print axioms GraphModel.expected_simpleRegret_source_bound
#print axioms GraphModel.expected_simpleRegret_explicit_rate

end Tests.CausalNoisyGraphCanary
