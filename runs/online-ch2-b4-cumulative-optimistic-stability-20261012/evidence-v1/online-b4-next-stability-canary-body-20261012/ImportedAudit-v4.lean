import CumulativeOptimisticStabilityCanary
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary.tight_stability_at_nonminimizer
run_cmd do
  let env ← getEnv
  let name := `BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary.tight_stability_at_nonminimizer
  let parent := `BanditRL.OnlineConvex.cumulative_optimistic_stability
  let ns := `BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary
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
      for (i,n) in #[(3,`feasible),(5,`regularizer),(6,`hint),(7,`losses),(17,`support)] do
        unless args[i]!.isConstOf (ns ++ n) do throw s!"Wrong concrete operand {i}"
      for (i,n) in #[(10,`hbot),(11,`hdom),(13,`hstrong),(15,`h0),(16,`hprediction),(18,`hdifference),(20,`hm1)] do
        unless bn ctx args[i]! == n do throw s!"Wrong internal proof operand {i}"
      unless isRealNumeral args[8]! 0 && args[8]!.getAppArgs[0]!.isConstOf `Nat && isRealNumeral args[9]! 1 && isRealNumeral args[14]! 0 do
        throw "Wrong n/lambda/p"
      let qa := args[19]!.getAppArgs
      unless args[19]!.getAppFn.isConstOf `Neg.neg && qa.size == 3 && isRealNumeral qa[2]! 1 do
        throw "Wrong q"
      rows := rows.push <| Json.mkObj [("provider",toJson parent.toString),("arity",toJson 21),
        ("concrete_operands",toJson ["feasible","regularizer","hint","losses","n=0","lambda=1","p=0","support","q=-1"]),
        ("internal_proofs",toJson ["hbot","hdom","hstrong","h0","hprediction","hdifference","hm1"]),("passed",toJson true)]
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
  for (n,expected) in #[(name,`CumulativeOptimisticStabilityCanary),(parent,`CumulativeOptimisticStabilityCandidate)] do
    let some idx := env.getModuleIdxFor? n | throwError "Missing origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == expected do throwError "Wrong origin"
    let file ← liftIO <| findOLean mod
    origins := origins.push <| Json.mkObj [("declaration",toJson n.toString),
      ("module",toJson mod.toString),("resolved_olean",toJson file.toString)]
  let report := Json.mkObj [("declaration",toJson name.toString),("TYPE",toJson (deps ci.type)),
    ("VALUE",toJson (deps value)),("first_conjunction_actual_bound",toJson true),
    ("provider_operands",toJson rows),("module_origins",toJson origins),
    ("method",toJson "Imported raw Expr operands, exact concrete constants and numerals, local premise binders and final And.intro first proof. No proof irrelevance or source rewriting.")]
  liftIO do
    let file ← IO.FS.Handle.mk "tmp/online-b4-next-stability-canary-body-20261012/imported-audit-v4.json" .writeNew
    file.putStr (report.pretty ++ "\n")
