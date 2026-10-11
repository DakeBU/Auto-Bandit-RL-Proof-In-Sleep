import CumulativeOptimisticStabilityDualCanary
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary.Tight.tight_dual_stability_at_nonminimizer
#print axioms BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary.ZeroCurvature.zero_curvature_division_is_false
run_cmd do
  let env ← getEnv
  let name := `BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary.Tight.tight_dual_stability_at_nonminimizer
  let parent := `BanditRL.OnlineConvex.cumulative_optimistic_stability_dual_bound
  let ns := `BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary.Tight
  let some ci := env.find? name | throwError "Missing declaration"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing VALUE"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let bn := fun (ctx : Array Name) (e : Expr) => match e with
    | .bvar i => ctx[ctx.size-1-i]?.getD .anonymous
    | _ => .anonymous
  let isRealNumeral := fun (e : Expr) (n : Nat) =>
    e.getAppFn.isConstOf `OfNat.ofNat && e.getAppArgs.size == 3 && e.getAppArgs[1]! == mkRawNatLit n
  let rec first (ctx : Array Name) : Expr → Except String Unit
    | .letE n _ _ b _ => first (ctx.push n) b
    | .mdata _ b => first ctx b
    | e => do
      unless e.getAppFn.isConstOf `And.intro && e.getAppArgs.size == 4 &&
          bn ctx e.getAppArgs[2]! == `bound do throw "First conjunct does not use actual bound"
  match first #[] value with
  | .ok _ => pure ()
  | .error s => throwError "{s}"
  let rec walk (ctx : Array Name) (e : Expr) : Except String (Array Json) := do
    let mut rows := #[]
    let args := e.getAppArgs
    if e.getAppFn.isConstOf parent && args.size == 21 then
      unless args[0]!.isConstOf `Real do throw "Wrong ambient type"
      for (i,n) in #[(3,`feasible),(5,`regularizer),(6,`hint),(7,`losses),(17,`support)] do
        unless args[i]!.isConstOf (ns ++ n) do throw s!"Wrong concrete operand {i}"
      for (i,n) in #[(4,`hV),(12,`hlam),(10,`hbot),(11,`hdom),(13,`hstrong),(15,`h0),(16,`hprediction),(18,`hdifference),(20,`hm2)] do
        unless bn ctx args[i]! == n do throw s!"Wrong internal proof operand {i}"
      unless isRealNumeral args[8]! 0 && args[8]!.getAppArgs[0]!.isConstOf `Nat && isRealNumeral args[9]! 1 && isRealNumeral args[14]! 0 do
        throw "Wrong n/lambda/p"
      let qa := args[19]!.getAppArgs
      unless args[19]!.getAppFn.isConstOf `Neg.neg && qa.size == 3 && isRealNumeral qa[2]! 2 do
        throw "Wrong q"
      rows := rows.push <| Json.mkObj [("provider",toJson parent.toString),("arity",toJson 21),
        ("concrete_operands",toJson ["feasible","regularizer","hint","losses","n=0","lambda=1","p=0","support","q=-2"]),
        ("internal_proofs",toJson ["hbot","hdom","hstrong","h0","hprediction","hdifference","hm2"]),("passed",toJson true)]
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
  unless rows.size == 1 do throwError "Expected exactly one full parent application"
  let mut origins : Array Json := #[]
  for (n,expected) in #[(name,`CumulativeOptimisticStabilityDualCanary),(parent,`CumulativeOptimisticStabilityDualCandidate)] do
    let some idx := env.getModuleIdxFor? n | throwError "Missing origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == expected do throwError "Wrong origin"
    let file ← liftIO <| findOLean mod
    origins := origins.push <| Json.mkObj [("declaration",toJson n.toString),
      ("module",toJson mod.toString),("resolved_olean",toJson file.toString)]
  let zeroName := `BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary.ZeroCurvature.zero_curvature_division_is_false
  let some zeroInfo := env.find? zeroName | throwError "Missing zero-curvature declaration"
  let some zeroValue := zeroInfo.value? (allowOpaque := true) | throwError "Missing zero VALUE"
  unless !zeroValue.getUsedConstantsAsSet.contains parent do throwError "Invalid dual call in zero-curvature case"
  let rec conjuncts (ctx : Array Name) : Expr → Except String (Array Name)
    | .letE n _ _ b _ => conjuncts (ctx.push n) b
    | .mdata _ b => conjuncts ctx b
    | e => do
      let a := e.getAppArgs
      if e.getAppFn.isConstOf `And.intro && a.size == 4 then
        return #[bn ctx a[2]!] ++ (← conjuncts ctx a[3]!)
      else return #[bn ctx e]
  let zeroProofs ← match conjuncts #[] zeroValue with
    | .ok xs => pure xs
    | .error s => throwError "{s}"
  unless zeroProofs.size == 14 do throwError "Wrong zero-curvature conjunction count"
  for (i,n) in #[(1,`hbot),(2,`hdom),(3,`hstrong),(4,`hprediction),(5,`hdifference),
      (6,`h0),(7,`hm1),(8,`hnorm),(9,`hzero),(10,`hminus)] do
    unless zeroProofs[i]! == n do throwError "Wrong internal zero-case proof operand {i}"
  let rec canon : Expr → Expr
    | .forallE _ t b i => .forallE .anonymous (canon t) (canon b) i
    | .lam _ t b i => .lam .anonymous (canon t) (canon b) i
    | .letE _ t v b n => .letE .anonymous (canon t) (canon v) (canon b) n
    | .app f a => .app (canon f) (canon a)
    | .mdata _ b => canon b
    | .proj n i b => .proj n i (canon b)
    | e => e
  let mut allOrigins : Array Json := #[]
  for n in env.header.moduleNames do
    let p ← liftIO <| findOLean n
    allOrigins := allOrigins.push <| Json.mkObj [("module",toJson n.toString),("olean",toJson p.toString)]
  let report := Json.mkObj [("declaration",toJson name.toString),("TYPE",toJson (deps ci.type)),
    ("VALUE",toJson (deps value)),("first_conjunction_actual_bound",toJson true),
    ("provider_operands",toJson rows),("module_origins",toJson origins),
    ("zero_case",Json.mkObj [("declaration",toJson zeroName.toString),("TYPE",toJson (deps zeroInfo.type)),
      ("VALUE",toJson (deps zeroValue)),("conjunct_count",toJson zeroProofs.size),
      ("internal_conjunct_proofs",toJson (zeroProofs.map Name.toString)),("no_invalid_dual_call",toJson true)]),
    ("method",toJson "Imported raw Expr operands, exact concrete constants and numerals, local premise binders and final And.intro first proof. No proof irrelevance or source rewriting.")]
  liftIO do
    let file ← IO.FS.Handle.mk "tmp/online-b4-next-dual-stability-canary-body-20261012/imported-audit-v1.json" .writeNew
    file.putStr (report.pretty ++ "\n")
    let base := "tmp/online-b4-next-dual-stability-canary-body-20261012/"
    let o ← IO.FS.Handle.mk (base ++ "imported-origins-v1.json") .writeNew
    o.putStr ((toJson allOrigins).pretty ++ "\n")
    for (label,e) in #[("tight-TYPE",ci.type),("tight-VALUE",value),
        ("zero-TYPE",zeroInfo.type),("zero-VALUE",zeroValue)] do
      let stream ← IO.FS.Handle.mk (base ++ label ++ "-normalized-v1.txt") .writeNew
      stream.putStr ((repr (canon e)).pretty ++ "\n")
