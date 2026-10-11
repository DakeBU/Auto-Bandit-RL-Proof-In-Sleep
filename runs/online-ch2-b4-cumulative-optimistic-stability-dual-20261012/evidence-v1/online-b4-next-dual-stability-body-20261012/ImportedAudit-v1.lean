import CumulativeOptimisticStabilityDualCandidate
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.OnlineConvex.cumulative_optimistic_stability_dual_bound
run_cmd do
  let env ← getEnv
  let name := `BanditRL.OnlineConvex.cumulative_optimistic_stability_dual_bound
  let parent := `BanditRL.OnlineConvex.cumulative_optimistic_stability
  let some ci := env.find? name | throwError "Missing declaration"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing VALUE"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let rec canon : Expr → Expr
    | .forallE _ t b i => .forallE .anonymous (canon t) (canon b) i
    | .lam _ t b i => .lam .anonymous (canon t) (canon b) i
    | .letE _ t v b n => .letE .anonymous (canon t) (canon v) (canon b) n
    | .app f a => .app (canon f) (canon a)
    | .mdata _ b => canon b
    | .proj n i b => .proj n i (canon b)
    | e => e
  let rec walk (ctx : Array Name) (e : Expr) : Except String (Array Json) := do
    let mut rows := #[]
    let fn := e.getAppFn
    let args := e.getAppArgs
    let bn := fun (a : Expr) => match a with
      | .bvar i => ctx[ctx.size-1-i]?.getD .anonymous
      | _ => .anonymous
    if fn.isConstOf parent && args.size == 21 then
      for (i,n) in #[(3,`V),(4,`hV),(5,`psi),(6,`hint),(7,`loss),(8,`n),(9,`lam),
          (10,`hbot),(11,`hdom),(12,`hlamNonneg),(13,`hstrong),(14,`p),(15,`hp),
          (16,`hprediction),(17,`g),(18,`hdifference),(19,`q),(20,`hq)] do
        unless bn args[i]! == n do throw s!"Wrong parent operand {i}: {bn args[i]!}, expected {n}"
      rows := rows.push <| Json.mkObj [("provider",toJson parent.toString),
        ("arity",toJson args.size),("operands",toJson (args.map (fun a => (bn a).toString))),
        ("passed",toJson true)]
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
  unless rows.size == 1 do throwError "Expected one actual sharp stability application"
  unless value.getUsedConstantsAsSet.contains `ContinuousLinearMap.le_opNorm do
    throwError "Missing operator norm inequality"
  let mut origins : Array Json := #[]
  for (n,expected) in #[(name,`CumulativeOptimisticStabilityDualCandidate),
      (parent,`CumulativeOptimisticStabilityCandidate)] do
    let some idx := env.getModuleIdxFor? n | throwError "Missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == expected do throwError "Wrong module origin"
    let file ← liftIO <| findOLean mod
    origins := origins.push <| Json.mkObj [("declaration",toJson n.toString),
      ("module",toJson mod.toString),("resolved_olean",toJson file.toString)]
  let mut allOrigins : Array Json := #[]
  for n in env.header.moduleNames do
    let p ← liftIO <| findOLean n
    allOrigins := allOrigins.push <| Json.mkObj [("module",toJson n.toString),("olean",toJson p.toString)]
  let report := Json.mkObj [("declaration",toJson name.toString),
    ("TYPE",toJson (deps ci.type)),("VALUE",toJson (deps value)),
    ("provider_operands",toJson rows),("module_origins",toJson origins),
    ("norm_inequality_constant_present",toJson true),
    ("method",toJson "Imported actual expressions; exact de Bruijn parent operand checks. Normalization removes binder names and mdata only; no proof irrelevance or equality substitution. Norm-inequality occurrence is checked separately, not an operand audit.")]
  liftIO do
    let base := "tmp/online-b4-next-dual-stability-body-20261012/"
    let f ← IO.FS.Handle.mk (base ++ "imported-audit-v1.json") .writeNew
    f.putStr (report.pretty ++ "\n")
    let o ← IO.FS.Handle.mk (base ++ "imported-origins-v1.json") .writeNew
    o.putStr ((toJson allOrigins).pretty ++ "\n")
    for (label,e) in #[("TYPE",ci.type),("VALUE",value)] do
      let stream ← IO.FS.Handle.mk (base ++ label ++ "-normalized-v1.txt") .writeNew
      stream.putStr ((repr (canon e)).pretty ++ "\n")
