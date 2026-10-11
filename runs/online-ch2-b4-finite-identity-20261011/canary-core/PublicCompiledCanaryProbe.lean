import Tests.OnlineCumulativePotentialCanary
import Lean.Util.FoldConsts
open Lean Elab Command
#check BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap
#print BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap
#print axioms BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap
#check BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice
#print BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice
#print axioms BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice
run_cmd do
  let env ← getEnv
  let names := #[`BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap,
    `BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice]
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.find? name | throwError "Missing compiled target"
    let some value := info.value? (allowOpaque := true) | throwError "Missing proof"
    rows := rows.push <| Json.mkObj [("declaration", toJson name.toString),
      ("TYPE", toJson (deps info.type)), ("VALUE", toJson (deps value))]
  liftIO <| IO.FS.writeFile "tmp/online-ch2-b4-finite-identity-canary-core-20261011/compiled-constant-occurrences-v1.json" ((toJson rows).pretty ++ "\n")
