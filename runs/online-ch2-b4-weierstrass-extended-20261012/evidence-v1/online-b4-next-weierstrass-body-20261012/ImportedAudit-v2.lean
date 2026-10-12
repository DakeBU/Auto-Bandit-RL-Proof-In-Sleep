import WeierstrassExtendedCandidate
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.OnlineConvex.source_weierstrass_extended
run_cmd do
  let env ← getEnv
  let name := `BanditRL.OnlineConvex.source_weierstrass_extended
  let provider := `LowerSemicontinuousOn.exists_isMinOn
  let some ci := env.find? name | throwError "Missing declaration"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing value"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let bn := fun (ctx : Array Name) (e : Expr) => match e with
    | .bvar i => ctx[ctx.size-1-i]?.getD .anonymous
    | _ => .anonymous
  let rec usedBinders (ctx : Array Name) : Expr → Array String
    | .bvar i => #[(ctx[ctx.size-1-i]?.getD .anonymous).toString]
    | .app f a => usedBinders ctx f ++ usedBinders ctx a
    | .lam n t b _ | .forallE n t b _ => usedBinders ctx t ++ usedBinders (ctx.push n) b
    | .letE n t v b _ => usedBinders ctx t ++ usedBinders ctx v ++ usedBinders (ctx.push n) b
    | .mdata _ b | .proj _ _ b => usedBinders ctx b
    | _ => #[]
  let rec walk (ctx : Array Name) (e : Expr) : Array Json := Id.run do
    let mut rows := #[]
    if e.getAppFn.isConstOf provider then
      let args := e.getAppArgs
      rows := rows.push <| Json.mkObj [("arity",toJson args.size),
        ("operands",toJson (args.map fun a => Json.mkObj [
          ("binder",toJson (bn ctx a).toString),("used_binders",toJson (usedBinders ctx a)),("head_constant",toJson a.getAppFn.constName!.toString),("expression",toJson (repr a).pretty)]))]
    match e with
    | .app f a => rows := rows ++ walk ctx f ++ walk ctx a
    | .lam n t b _ | .forallE n t b _ => rows := rows ++ walk ctx t ++ walk (ctx.push n) b
    | .letE n t v b _ => rows := rows ++ walk ctx t ++ walk ctx v ++ walk (ctx.push n) b
    | .mdata _ b | .proj _ _ b => rows := rows ++ walk ctx b
    | _ => pure ()
    return rows
  let rows := walk #[] value
  unless rows.size > 0 do throwError "Missing genuine provider"
  let some ix := env.getModuleIdxFor? name | throwError "No source module"
  unless env.header.moduleNames[ix.toNat]! == `WeierstrassExtendedCandidate do
    throwError "Wrong scratch origin"
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
    let p ← liftIO <| findOLean n
    origins := origins.push <| Json.mkObj [("module",toJson n.toString),("olean",toJson p.toString)]
  let report := Json.mkObj [("declaration",toJson name.toString),("TYPE",toJson (deps ci.type)),
    ("VALUE",toJson (deps value)),("provider_applications_including_partial",toJson rows),
    ("normalization",toJson "Binder names anonymous; mdata removed; all other Expr nodes retained. No proof irrelevance or equality substitution.")]
  liftIO do
    let base := "tmp/online-b4-next-weierstrass-body-20261012/"
    let f ← IO.FS.Handle.mk (base ++ "imported-audit-v2.json") .writeNew
    f.putStr (report.pretty ++ "\n")
    let o ← IO.FS.Handle.mk (base ++ "imported-origins-v2.json") .writeNew
    o.putStr ((toJson origins).pretty ++ "\n")
    for (label,e) in #[("TYPE",ci.type),("VALUE",value)] do
      let s ← IO.FS.Handle.mk (base ++ label ++ "-normalized-v1.txt") .writeNew
      s.putStr ((repr (canon e)).pretty ++ "\n")
