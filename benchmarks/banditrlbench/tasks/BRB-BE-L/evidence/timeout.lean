import BanditRLProof.RL.FiniteHorizonPolicy
import Lean.Util.FoldConsts
theorem BenchExpansion.BRB_BE_L {State Action : Type}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    (mdp : BanditRLProof.FiniteHorizonRL.MDP State Action)
    (policy : BanditRLProof.FiniteHorizonRL.MarkovPolicy mdp)
    (v : ℕ → State → ℝ)
    (hterminal : v mdp.horizon = fun _ => 0)
    (hstep : ∀ (t : ℕ) (ht : t < mdp.horizon),
      v t = policy.bellman ⟨t, ht⟩ (v (t + 1)))
    (stage : ℕ) (hstage : stage ≤ mdp.horizon) :
    v stage = policy.valueAt stage hstage := (
by
  exact Nat.decreasingInduction
    (n := mdp.horizon)
    (motive := fun t ht => v t = policy.valueAt t ht)
    (fun t ht ih => by
      change v t = policy.valueAt t _
      rw [hstep t ht, policy.valueAt_bellman t ht, ih])
    (by
      change v mdp.horizon = policy.valueAt mdp.horizon _
      rw [hterminal, policy.valueAt_horizon]) hstage

)
#print axioms BenchExpansion.BRB_BE_L
run_cmd do
  let info ← Lean.getConstInfo `BenchExpansion.BRB_BE_L
  let ty := info.type.getUsedConstantsAsSet.toList.map (·.toString)
  let vl := info.value?.map (fun v => v.getUsedConstantsAsSet.toList.map (·.toString)) |>.getD []
  let j := Lean.Json.mkObj [("type_constants", Lean.toJson ty), ("value_constants", Lean.toJson vl)]
  Lean.logInfo m!"BRB_DEPENDENCIES {j.compress}"
