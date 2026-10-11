import CumulativeOptimisticStabilityCandidate
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.OnlineConvex.cumulative_optimistic_stability
run_cmd do
  let env ← getEnv
  let name := `BanditRL.OnlineConvex.cumulative_optimistic_stability
  let growth := `BanditRL.OnlineConvex.stronglyConvex_support_growth
  let proper := `BanditRL.OnlineConvex.sourceProper_of_domain
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
  let rec strip : Expr → Expr
    | .forallE _ _ b _ | .lam _ _ b _ | .mdata _ b => strip b
    | e => e
  let .letE _ _ expectedG _ _ := strip ci.type | throwError "TYPE lacks actual G"
  let .letE _ _ actualG _ _ := strip value | throwError "VALUE lacks actual G"
  unless canon expectedG == canon actualG do throwError "TYPE/VALUE G differ"
  let rec walk (ctx : Array Name) (e : Expr) : Except String (Array Json) := do
    let mut rows := #[]
    let fn := e.getAppFn
    let args := e.getAppArgs
    let bn := fun (a : Expr) => match a with
      | .bvar i => ctx[ctx.size-1-i]?.getD .anonymous
      | _ => .anonymous
    let require := fun (i : Nat) (n : Name) =>
      if bn args[i]! == n then Except.ok () else Except.error s!"Operand {i} expected {n}, actual {bn args[i]!}"
    if fn.isConstOf growth && args.size == 17 then
      for (i,n) in #[(3,`G),(4,`V),(5,`lam),(6,`hproper),(7,`hV),(8,`hGdom),
          (9,`hlam),(10,`hstrong),(11,`p),(12,`hp),(13,`g),(14,`hsupport),(15,`q),(16,`hq)] do require i n
      rows := rows.push <| Json.mkObj [("provider",toJson growth.toString),("arity",toJson 17),
        ("operands",toJson (args.map (fun a => (bn a).toString))),("passed",toJson true)]
    if fn.isConstOf proper && args.size == 6 then
      for (i,n) in #[(1,`G),(2,`V),(4,`hGbot),(5,`hGdom)] do require i n
      let witness := args[3]!.getAppArgs
      unless args[3]!.getAppFn.isConstOf `Exists.intro && witness.size == 4 &&
          bn witness[2]! == `p && bn witness[3]! == `hp do throw "Wrong nonempty witness"
      rows := rows.push <| Json.mkObj [("provider",toJson proper.toString),("arity",toJson 6),
        ("operands",toJson ["G","V","Exists.intro p hp","hGbot","hGdom"]),("passed",toJson true)]
    if (bn fn == `hprediction || bn fn == `hdifference) && args.size == 2 then
      require 0 `z
      require 1 `hz
      rows := rows.push <| Json.mkObj [("premise",toJson (bn fn).toString),
        ("operands",toJson ["z","hz"]),("within_derived_hsupport",toJson (ctx.contains `hprior)),("passed",toJson true)]
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
  unless rows.size == 4 do throwError "Expected four actual provider/premise applications, got {rows.size}"
  let mut origins : Array Json := #[]
  for (n,expected) in #[(name,`CumulativeOptimisticStabilityCandidate),
      (growth,`BanditRLProof.OnlineStrongConvexSupport),(proper,`BanditRLProof.OnlinePrescientBregmanSource)] do
    let some idx := env.getModuleIdxFor? n | throwError "Missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == expected do throwError "Wrong module origin"
    let file ← liftIO <| findOLean mod
    origins := origins.push <| Json.mkObj [("declaration",toJson n.toString),
      ("module",toJson mod.toString),("resolved_olean",toJson file.toString)]
  let report := Json.mkObj [("declaration",toJson name.toString),
    ("TYPE",toJson (deps ci.type)),("VALUE",toJson (deps value)),
    ("actual_G_TYPE_VALUE_alpha_equal",toJson true),("provider_operands",toJson rows),
    ("module_origins",toJson origins),
    ("method",toJson "Imported actual expressions. Binder-name and mdata normalization only for G equality; exact de Bruijn operand checks. No proof irrelevance or equality substitution.")]
  liftIO do
    let file ← IO.FS.Handle.mk "tmp/online-b4-next-stability-body-20261012/imported-audit-v1.json" .writeNew
    file.putStr (report.pretty ++ "\n")
