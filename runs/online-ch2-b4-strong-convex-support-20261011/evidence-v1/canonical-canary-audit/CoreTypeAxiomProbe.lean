import Tests.OnlineStrongConvexSupportCanary
import Lean.Util.FoldConsts
open Lean Elab Command
#check BanditRL.OnlineConvex.stronglyConvex_support_growth
#print axioms BanditRL.OnlineConvex.stronglyConvex_support_growth
run_cmd do
  let env ← getEnv
  let some info := env.find? `BanditRL.OnlineConvex.stronglyConvex_support_growth | throwError "Missing actual imported core"
  let constants := (info.type.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let row := Json.mkObj [("declaration",toJson "BanditRL.OnlineConvex.stronglyConvex_support_growth"),("TYPE",toJson constants)]
  liftIO <| IO.FS.writeFile "tmp/online-b4-support-canonical-canary-audit-20261011/core-type-constants-v1.json" (row.pretty ++ "\n")
