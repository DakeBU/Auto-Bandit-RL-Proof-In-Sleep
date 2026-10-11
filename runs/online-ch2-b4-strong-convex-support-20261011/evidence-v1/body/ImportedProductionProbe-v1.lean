import BanditRLProof.OnlineStrongConvexSupport

#print axioms BanditRL.OnlineConvex.stronglyConvex_support_growth
run_cmd do
  let env ← Lean.getEnv
  let some ci := env.find? `BanditRL.OnlineConvex.stronglyConvex_support_growth
    | throwError "missing theorem"
  let names (e : Lean.Expr) := e.getUsedConstantsAsSet.toArray.map (fun n => Lean.Json.str n.toString)
  let value ← match ci with
    | .thmInfo i => pure i.value
    | _ => throwError "not theorem"
  let report := Lean.Json.mkObj [
    ("declaration", Lean.Json.str ci.name.toString),
    ("TYPE", Lean.Json.arr (names ci.type)),
    ("VALUE", Lean.Json.arr (names value))]
  Lean.logInfo ("ACTUAL_DEPENDENCIES_JSON=" ++ report.compress)
