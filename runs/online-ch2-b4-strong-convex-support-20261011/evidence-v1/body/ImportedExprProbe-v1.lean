import BanditRLProof.OnlineStrongConvexSupport

run_cmd do
  let env ← Lean.getEnv
  let some ci := env.find? `BanditRL.OnlineConvex.stronglyConvex_support_growth
    | throwError "missing theorem"
  let value ← match ci with
    | .thmInfo i => pure i.value
    | _ => throwError "not theorem"
  Lean.logInfo ("ACTUAL_EXPR_JSON=" ++ (Lean.Json.mkObj [
    ("TYPE_REPR", Lean.Json.str (reprStr ci.type)),
    ("VALUE_REPR", Lean.Json.str (reprStr value))]).compress)
