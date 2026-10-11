import BanditRLProof.OnlineStrongConvexSupport

run_cmd do
  let env ← Lean.getEnv
  let some ci := env.find? `BanditRL.OnlineConvex.stronglyConvex_support_growth
    | throwError "missing theorem"
  let value ← match ci with
    | .thmInfo i => pure i.value
    | _ => throwError "not theorem"
  let rec canon : Lean.Expr → Lean.Expr
    | .forallE _ t b i => .forallE .anonymous (canon t) (canon b) i
    | .lam _ t b i => .lam .anonymous (canon t) (canon b) i
    | .letE _ t v b n => .letE .anonymous (canon t) (canon v) (canon b) n
    | .app f a => .app (canon f) (canon a)
    | .mdata _ e => canon e
    | .proj s i e => .proj s i (canon e)
    | e => e
  Lean.logInfo ("ACTUAL_EXPR_JSON=" ++ (Lean.Json.mkObj [
    ("TYPE_REPR", Lean.Json.str (reprStr ci.type)),
    ("VALUE_REPR", Lean.Json.str (reprStr value)),
    ("TYPE_ALPHA_REPR", Lean.Json.str (reprStr (canon ci.type))),
    ("VALUE_ALPHA_REPR", Lean.Json.str (reprStr (canon value)))]).compress)
