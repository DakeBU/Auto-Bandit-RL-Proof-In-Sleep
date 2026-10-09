import AdaptiveTranscript

open QuantumBlockEncoding ResetBlockProcess
open BanditRLProof.AdaptiveTranscript
open scoped Matrix.Norms.L2Operator

private noncomputable def xOracle : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Fin.sum_univ_two]⟩

private def firstPlan : Plan 2 3 (Fin 2) :=
  ⟨0, [.forward, .forward, .inverse], by decide⟩

private def afterOne : Plan 2 3 (Fin 2) := ⟨1, [.inverse], by decide⟩

-- The classical outcome changes both the arm and the charged word length.
private def adaptivePolicy (h : List (Fin 2)) : Plan 2 3 (Fin 2) :=
  if h = [(1 : Fin 2)] then afterOne else firstPlan

private noncomputable def zeroState : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 0 1

private theorem zeroState_norm : ‖zeroState‖ = 1 := by simp [zeroState]

private theorem output_three :
    BasisHellinger.wordOutput firstPlan.word (xOracle : Matrix (Fin 2) (Fin 2) ℂ) zeroState =
      PiLp.single 2 1 (1 : ℂ) := by
  have heval : QuantumQueryWord.eval firstPlan.word (xOracle : Matrix (Fin 2) (Fin 2) ℂ) =
      (xOracle : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [firstPlan, QuantumQueryWord.eval, QuantumQueryWord.Instruction.eval, one_mul]
    rw [Unitary.star_mul_self_of_mem xOracle.property, one_mul]
  unfold BasisHellinger.wordOutput
  rw [heval]
  ext j
  simp only [Matrix.ofLp_toEuclideanCLM]
  fin_cases j <;>
    norm_num [xOracle, zeroState, Matrix.mulVec, dotProduct, Fin.sum_univ_two, PiLp.single_apply]

private theorem block_first : blockPMF firstPlan (fun _ => xOracle) zeroState zeroState_norm =
    PMF.pure (1 : Fin 2) := by
  ext j
  rw [blockPMF_apply, output_three]
  fin_cases j <;> simp [BasisHellinger.basisProbability, PMF.pure_apply]

private theorem block_after : blockPMF afterOne (fun _ => xOracle) zeroState zeroState_norm =
    PMF.pure (1 : Fin 2) := by
  have heq : BasisHellinger.wordOutput afterOne.word (xOracle : Matrix (Fin 2) (Fin 2) ℂ) zeroState =
      BasisHellinger.wordOutput firstPlan.word (xOracle : Matrix (Fin 2) (Fin 2) ℂ) zeroState := by
    have heval : QuantumQueryWord.eval afterOne.word (xOracle : Matrix (Fin 2) (Fin 2) ℂ) =
        QuantumQueryWord.eval firstPlan.word (xOracle : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [afterOne, firstPlan, QuantumQueryWord.eval, QuantumQueryWord.Instruction.eval, one_mul]
      rw [Unitary.star_mul_self_of_mem xOracle.property, one_mul]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [xOracle, Matrix.star_eq_conjTranspose]
    unfold BasisHellinger.wordOutput
    rw [heval]
  ext j
  rw [blockPMF_apply, heq, output_three]
  fin_cases j <;> simp [BasisHellinger.basisProbability, PMF.pure_apply]

-- Reset, adapt to outcome 1, then query the other arm's inverse: total 3+1.
example : traceLaw adaptivePolicy (fun _ => xOracle) zeroState zeroState_norm 2 =
    PMF.pure (((PUnit.unit, (1 : Fin 2)), (1 : Fin 2)) : Trace (Fin 2) 2) := by
  simp [traceLaw, adaptivePolicy, history, block_first, block_after, PMF.pure_map]
  rfl

example : history (n := 2) (((PUnit.unit, (1 : Fin 2)), (1 : Fin 2)) : Trace (Fin 2) 2) = [1, 1] := rfl

example : historyQueryCost adaptivePolicy [(1 : Fin 2), 1] = 4 := by
  norm_num [historyQueryCost, adaptivePolicy, firstPlan, afterOne, QuantumQueryWord.queryCount,
    QuantumQueryWord.Instruction.queryCost, Finset.sum_range_succ]

example (η : ℝ) : weightedCost adaptivePolicy (fun _ => η) (n := 2)
    (((PUnit.unit, (1 : Fin 2)), (1 : Fin 2)) : Trace (Fin 2) 2) = 4 * η ^ 2 := by
  norm_num [weightedCost, history, adaptivePolicy, firstPlan, afterOne,
    QuantumQueryWord.queryCount, QuantumQueryWord.Instruction.queryCost]
  ring

example (n : ℕ) : (traceLaw adaptivePolicy (fun _ => xOracle) zeroState zeroState_norm n).map history =
    historyLaw adaptivePolicy (fun _ => xOracle) zeroState zeroState_norm n :=
  traceLaw_history_eq _ _ _ _ _

#print axioms finite_kernel_chain
#print axioms adaptive_hellinger_le
#print axioms traceLaw_apply
#print axioms traceLaw_history_eq
#print axioms weightedCost_uniform
#print axioms adaptive_hellinger_budget
