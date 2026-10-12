import StrongConvexAttainmentCanaries
import Lean.Util.FoldConsts

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let positive := `BanditRL.Tests.OnlineStrongConvexAttainmentCanary.halfline_quadratic_unique_attainment
  let parent := `BanditRL.OnlineConvex.stronglyConvex_existsUnique_minimizer
  let some info := env.find? positive | throwError "Missing positive canary"
  let some value := info.value? (allowOpaque := true) | throwError "Missing positive VALUE"
  let rec locate (e : Expr) : Array Expr := Id.run do
    let mut calls : Array Expr := #[]
    if e.getAppFn.isConstOf parent && e.getAppArgs.size == 12 then
      calls := calls.push e
    match e with
    | .app f a => calls := calls ++ locate f ++ locate a
    | .lam _ t b _ | .forallE _ t b _ => calls := calls ++ locate t ++ locate b
    | .letE _ t v b _ => calls := calls ++ locate t ++ locate v ++ locate b
    | .mdata _ b | .proj _ _ b => calls := calls ++ locate b
    | _ => pure ()
    return calls
  let calls := locate value
  unless calls.size == 1 do throwError "Expected exactly one full arity-12 parent application"
  let mut origins : Array Json := #[]
  for (name,expected) in #[(positive,`StrongConvexAttainmentCanaries),
      (parent,`StrongConvexAttainmentCandidate)] do
    let some index := env.getModuleIdxFor? name | throwError "Missing declaration module origin"
    let actual := env.header.moduleNames[index.toNat]!
    unless actual == expected do throwError "Wrong declaration module origin"
    let file ← liftIO <| findOLean actual
    origins := origins.push <| Json.mkObj [("declaration",toJson name.toString),
      ("module",toJson actual.toString),("olean",toJson file.toString)]
  let args := calls[0]!.getAppArgs
  liftIO do
    IO.println "DIAGNOSTIC_ONLY_NOT_FULL_AUDIT_ACCEPTANCE"
    IO.println ((toJson origins).pretty)
    for (index,label) in (#[(3,"dimension"),(6,"curvature")] : Array (Nat × String)) do
      let operand := args[index]!
      IO.println s!"OPERAND {index} {label} RAW_EXPR\n{(repr operand).pretty}"
      IO.println s!"OPERAND {index} GET_APP_FN\n{(repr operand.getAppFn).pretty}"
      IO.println s!"OPERAND {index} GET_APP_ARGS\n{(repr operand.getAppArgs).pretty}"
