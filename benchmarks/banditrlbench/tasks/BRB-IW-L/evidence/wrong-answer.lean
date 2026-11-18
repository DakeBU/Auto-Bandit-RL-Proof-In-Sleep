import BanditRLProof.Exp3ImportanceWeighted
import Lean.Util.FoldConsts
theorem BenchExpansion.BRB_IW_L {Action : Type} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action → ℝ)
    (action : Action) (haction : action ∈ arms)
    (hnorm : arms.sum prob = 1) (hprob : prob action ≠ 0) :
    arms.sum (fun chosen => prob chosen *
      (BanditRLProof.Exp3.importanceWeightedLoss prob loss chosen action - loss action)^2)
      = (loss action)^2 * (1 / prob action - 1) := (
by
  exact True.intro

)
#print axioms BenchExpansion.BRB_IW_L
run_cmd do
  let info ← Lean.getConstInfo `BenchExpansion.BRB_IW_L
  let ty := info.type.getUsedConstantsAsSet.toList.map (·.toString)
  let vl := info.value?.map (fun v => v.getUsedConstantsAsSet.toList.map (·.toString)) |>.getD []
  let j := Lean.Json.mkObj [("type_constants", Lean.toJson ty), ("value_constants", Lean.toJson vl)]
  Lean.logInfo m!"BRB_DEPENDENCIES {j.compress}"
