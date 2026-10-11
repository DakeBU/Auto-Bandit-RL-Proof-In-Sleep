import BanditRLProof.OnlineCumulativePotential
import Lean.Util.FoldConsts
open Lean Elab Command
#check BanditRL.OnlineCumulativePotential.finite_regret_identity
#print BanditRL.OnlineCumulativePotential.finite_regret_identity
#print axioms BanditRL.OnlineCumulativePotential.finite_regret_identity
run_cmd do
  let env ← getEnv
  let name := `BanditRL.OnlineCumulativePotential.finite_regret_identity
  let some info := env.find? name | throwError "Missing compiled target"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let some value := info.value? (allowOpaque := true) | throwError "Missing proof value"
  let obj := Json.mkObj [
    ("declaration", toJson name.toString),
    ("TYPE", toJson (deps info.type)),
    ("VALUE", toJson (deps value))]
  liftIO <| IO.FS.writeFile "tmp/online-ch2-b4-finite-identity-core-20261011/compiled-constant-occurrences-v1.json" (obj.pretty ++ "\n")
