import WeierstrassExtendedCanary
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.Tests.OnlineWeierstrassExtendedCanary.bottom_singleton_attains
run_cmd do
  let env ← getEnv
  let name := `BanditRL.Tests.OnlineWeierstrassExtendedCanary.bottom_singleton_attains
  let parent := `BanditRL.OnlineConvex.source_weierstrass_extended
  let some ci := env.find? name | throwError "Missing declaration"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing VALUE"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let bn := fun (ctx : Array Name) (e : Expr) => match e with
    | .bvar i => ctx[ctx.size-1-i]?.getD .anonymous
    | _ => .anonymous
  let rec first (ctx : Array Name) : Expr → Except String Unit
    | .letE n _ _ b _ => first (ctx.push n) b
    | .mdata _ b => first ctx b
    | e => do
      unless e.getAppFn.isConstOf `And.intro && e.getAppArgs.size == 4 && bn ctx e.getAppArgs[2]! == `hmin do
        throw "First conjunct is not actual A3-produced minimum"
  match first #[] value with
  | .ok _ => pure ()
  | .error s => throwError "{s}"
  let rec walk (ctx : Array Name) (e : Expr) : Except String (Array Json) := do
    let mut rows := #[]
    let args := e.getAppArgs
    if e.getAppFn.isConstOf parent && args.size == 8 then
      unless args[0]!.isConstOf `Real do throw "Wrong ambient"
      unless args[3]!.isConstOf `BanditRL.Tests.OnlineWeierstrassExtendedCanary.objective do throw "Wrong objective"
      unless args[4]!.isConstOf `BanditRL.Tests.OnlineWeierstrassExtendedCanary.feasible do throw "Wrong feasible set"
      for (i,n) in (#[(5,`hlsc),(6,`hcompact),(7,`hdom)] : Array (Nat × Name)) do
        unless bn ctx args[i]! == n do throw "Wrong internal premise"
      rows := rows.push <| Json.mkObj [("arity",toJson args.size),
        ("operands",toJson (args.map fun a => Json.mkObj [("binder",toJson (bn ctx a).toString),("expression",toJson (repr a).pretty)]))]
    match e with
    | .app f a => rows := rows ++ (← walk ctx f) ++ (← walk ctx a)
    | .lam n t b _ | .forallE n t b _ => rows := rows ++ (← walk ctx t) ++ (← walk (ctx.push n) b)
    | .letE n t v b _ => rows := rows ++ (← walk ctx t) ++ (← walk ctx v) ++ (← walk (ctx.push n) b)
    | .mdata _ b | .proj _ _ b => rows := rows ++ (← walk ctx b)
    | _ => pure ()
    return rows
  let rows ← match walk #[] value with
    | .ok rows => pure rows
    | .error s => throwError "{s}"
  unless rows.size == 1 do throwError "Expected exactly one full A3 application"
  let mut declarationOrigins : Array Json := #[]
  for (n,expected) in #[(name,`WeierstrassExtendedCanary),(parent,`WeierstrassExtendedCandidate)] do
    let some idx := env.getModuleIdxFor? n | throwError "Missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == expected do throwError "Wrong module origin"
    let file ← liftIO <| findOLean mod
    declarationOrigins := declarationOrigins.push <| Json.mkObj [("declaration",toJson n.toString),("module",toJson mod.toString),("olean",toJson file.toString)]
  let rec canon : Expr → Expr
    | .forallE _ t b i => .forallE .anonymous (canon t) (canon b) i
    | .lam _ t b i => .lam .anonymous (canon t) (canon b) i
    | .letE _ t v b n => .letE .anonymous (canon t) (canon v) (canon b) n
    | .app f a => .app (canon f) (canon a)
    | .mdata _ b => canon b
    | .proj n i b => .proj n i (canon b)
    | e => e
  let mut origins : Array Json := #[]
  for n in env.header.moduleNames do
    let file ← liftIO <| findOLean n
    origins := origins.push <| Json.mkObj [("module",toJson n.toString),("olean",toJson file.toString)]
  let report := Json.mkObj [("declaration",toJson name.toString),("TYPE",toJson (deps ci.type)),("VALUE",toJson (deps value)),
    ("first_conjunction_actual_A3",toJson true),("provider_operands",toJson rows),("declaration_origins",toJson declarationOrigins)]
  liftIO do
    let base := "tmp/online-b4-next-weierstrass-canary-body-20261012/"
    let f ← IO.FS.Handle.mk (base ++ "imported-audit-v1.json") .writeNew
    f.putStr (report.pretty ++ "\n")
    let o ← IO.FS.Handle.mk (base ++ "imported-origins-v1.json") .writeNew
    o.putStr ((toJson origins).pretty ++ "\n")
    for (label,e) in #[("TYPE",ci.type),("VALUE",value)] do
      let s ← IO.FS.Handle.mk (base ++ label ++ "-normalized-v1.txt") .writeNew
      s.putStr ((repr (canon e)).pretty ++ "\n")
