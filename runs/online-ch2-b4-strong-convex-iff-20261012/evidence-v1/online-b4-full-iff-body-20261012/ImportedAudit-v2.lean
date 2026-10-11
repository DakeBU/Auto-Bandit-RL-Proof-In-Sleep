import FullIffCandidate
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.OnlineConvex.stronglyConvex_iff_sourceSubgradient_growth
run_cmd do
  let env ← getEnv
  let name := `BanditRL.OnlineConvex.stronglyConvex_iff_sourceSubgradient_growth
  let forward := `BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth
  let finite := `BanditRL.OnlineConvex.subgradient_point_finite
  let some ci := env.find? name | throwError "Missing imported declaration"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing imported VALUE"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let rec small (ctx : Array Name) : Nat → Expr → String
    | 0, _ => "..."
    | _, .bvar i => s!"bvar[{i}]={ctx[ctx.size-1-i]?.getD .anonymous}"
    | _, .const n _ => n.toString
    | n+1, .app f a => "(" ++ small ctx n f ++ " " ++ small ctx n a ++ ")"
    | _, .lam n _ _ _ => "lambda " ++ n.toString
    | _, .forallE n _ _ _ => "forall " ++ n.toString
    | _, .letE n _ _ _ _ => "let " ++ n.toString
    | n+1, .mdata _ b => small ctx n b
    | n+1, .proj projName i b => s!"proj {projName}.{i} " ++ small ctx n b
    | _, e => reprStr e
  let rec walk (ctx : Array Name) (e : Expr) : Array Json := Id.run do
    let mut out := #[]
    let fn := e.getAppFn
    let args := e.getAppArgs
    if (fn.isConstOf forward && args.size == 19) ||
        (fn.isConstOf finite && args.size >= 7) then
      out := out.push <| Json.mkObj [("provider",toJson fn.constName!.toString),
        ("arity",toJson args.size),("context",toJson (ctx.map Name.toString)),
        ("args",toJson (args.map (small ctx 7)))]
    match e with
    | .app f a => out := out ++ walk ctx f ++ walk ctx a
    | .lam n t b _ | .forallE n t b _ => out := out ++ walk ctx t ++ walk (ctx.push n) b
    | .letE n t v b _ => out := out ++ walk ctx t ++ walk ctx v ++ walk (ctx.push n) b
    | .mdata _ b | .proj _ _ b => out := out ++ walk ctx b
    | _ => pure ()
    return out
  let mut origins : Array Json := #[]
  for (n,expected) in #[(name,`FullIffCandidate),(forward,`BanditRLProof.OnlineStrongConvexSourceSubgradient),
      (finite,`BanditRLProof.OnlineSubgradientBasic)] do
    let some idx := env.getModuleIdxFor? n | throwError "Missing actual module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == expected do throwError "Wrong module origin"
    let file ← liftIO <| findOLean mod
    origins := origins.push <| Json.mkObj [("declaration",toJson n.toString),
      ("module",toJson mod.toString),("resolved_olean",toJson file.toString)]
  let report := Json.mkObj [("declaration",toJson name.toString),
    ("TYPE",toJson (deps ci.type)),("VALUE",toJson (deps value)),
    ("provider_occurrences",toJson (walk #[] value)),("module_origins",toJson origins),
    ("method",toJson "Actual imported expressions; finite depth operand render with de Bruijn indices and binder context. No proof irrelevance, expression rewriting or huge Expr stream.")]
  liftIO do
    let file ← IO.FS.Handle.mk "tmp/online-b4-full-iff-body-20261012/imported-audit-v2.json" .writeNew
    file.putStr (report.pretty ++ "\n")
