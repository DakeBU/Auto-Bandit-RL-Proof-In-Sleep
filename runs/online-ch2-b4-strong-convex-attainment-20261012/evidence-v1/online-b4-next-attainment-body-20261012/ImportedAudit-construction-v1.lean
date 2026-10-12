import StrongConvexAttainmentCandidate
import Lean.Util.FoldConsts
open Lean Elab Command

#print axioms BanditRL.OnlineConvex.stronglyConvex_existsUnique_minimizer

run_cmd do
  let env ← getEnv
  let name := `BanditRL.OnlineConvex.stronglyConvex_existsUnique_minimizer
  let a3 := `BanditRL.OnlineConvex.source_weierstrass_extended
  let growth := `BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth
  let minimum := `BanditRL.OnlineConvex.stronglyConvex_minimum_growth
  let finite := `BanditRL.OnlineConvex.subgradient_point_finite
  let some ci := env.find? name | throwError "Missing actual candidate declaration"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing actual VALUE"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let rec telescope : Expr → Array Name
    | .forallE n _ b _ => #[n] ++ telescope b
    | .mdata _ b => telescope b
    | _ => #[]
  let header := telescope ci.type
  unless header.size == 12 && header.extract 3 12 ==
      #[`d, `e, `f, `lam, `hf, `hclosed, `hlam, `hstrong, `hsub] do
    throwError "Public telescope differs: hidden or changed assumption"
  let bn := fun (ctx : Array Name) (e : Expr) => match e with
    | .bvar i => ctx[ctx.size - 1 - i]?.getD .anonymous
    | _ => .anonymous
  let rec uses (ctx : Array Name) (wanted : Name) : Expr → Bool
    | .bvar i => ctx[ctx.size - 1 - i]?.getD .anonymous == wanted
    | .app f a => uses ctx wanted f || uses ctx wanted a
    | .lam n t b _ | .forallE n t b _ => uses ctx wanted t || uses (ctx.push n) wanted b
    | .letE n t v b _ => uses ctx wanted t || uses ctx wanted v || uses (ctx.push n) wanted b
    | .mdata _ b | .proj _ _ b => uses ctx wanted b
    | _ => false
  let rec walk (ctx : Array Name) (e : Expr) : Except String (Array Json × Array String) := do
    let mut rows : Array Json := #[]
    let mut raw : Array String := #[]
    let fn := e.getAppFn
    let args := e.getAppArgs
    let mut provider : Name := .anonymous
    let mut expected : Array (Nat × Name) := #[]
    if fn.isConstOf a3 && args.size == 8 then
      provider := a3
      expected := #[(0,`E),(3,`f),(4,`S),(5,`hlsc),(6,`hcompact),(7,`hmeet)]
    if fn.isConstOf growth && args.size == 19 then
      provider := growth
      expected := #[(0,`E),(3,`d),(4,`e),(5,`f),(6,`D),(7,`lam),
        (8,`hf),(9,`hD),(12,`hstrong),(13,`y),(14,`hy),(15,`g),(16,`hg),(17,`x),(18,`hxD)]
    if fn.isConstOf minimum && args.size == 16 then
      provider := minimum
      expected := #[(0,`E),(3,`f),(4,`D),(5,`lam),(6,`hf),(7,`hD),
        (10,`hstrong),(11,`p),(12,`hpD),(13,`hminD),(14,`q)]
    if fn.isConstOf finite && args.size == 8 then
      provider := finite
      expected := #[(4,`hfcoord),(6,`g),(7,`hg)]
      unless uses ctx `f args[3]! && uses ctx `e args[3]! do
        throw "Coordinate objective fails f/e structural occurrence check"
      unless uses ctx `e args[5]! && uses ctx `y args[5]! do
        throw "Coordinate base fails e/y structural occurrence check"
    if provider != .anonymous then
      for (i,n) in expected do
        unless bn ctx args[i]! == n do
          throw s!"Wrong operand {provider} index{i}: {bn ctx args[i]!}, expected {n}"
      rows := rows.push <| Json.mkObj [("provider",toJson provider.toString),
        ("arity",toJson args.size),("operand_binders",toJson (args.map (fun a => (bn ctx a).toString))),
        ("operand_constants",toJson (args.map deps))]
      for i in [:args.size] do
        raw := raw.push s!"PROVIDER {provider} ARG {i}\n{(repr args[i]!).pretty}\n"
    match e with
    | .app f a =>
      let (r,s) ← walk ctx f; rows := rows ++ r; raw := raw ++ s
      let (r,s) ← walk ctx a; rows := rows ++ r; raw := raw ++ s
    | .lam n t b _ | .forallE n t b _ =>
      let (r,s) ← walk ctx t; rows := rows ++ r; raw := raw ++ s
      let (r,s) ← walk (ctx.push n) b; rows := rows ++ r; raw := raw ++ s
    | .letE n t v b _ =>
      if [ `FiniteDimensional, `T2Space, `IsCompact, `Convex, `IsMinOn ].any
          (fun c => t.getUsedConstantsAsSet.contains c) || n == `S || n == `D then
        raw := raw.push s!"DERIVED LET {n}\nTYPE {(repr t).pretty}\nVALUE {(repr v).pretty}\n"
      let (r,s) ← walk ctx t; rows := rows ++ r; raw := raw ++ s
      let (r,s) ← walk ctx v; rows := rows ++ r; raw := raw ++ s
      let (r,s) ← walk (ctx.push n) b; rows := rows ++ r; raw := raw ++ s
    | .mdata _ b | .proj _ _ b =>
      let (r,s) ← walk ctx b; rows := rows ++ r; raw := raw ++ s
    | _ => pure ()
    return (rows,raw)
  let (rows,raw) ← match walk #[] value with
    | .ok r => pure r
    | .error s => throwError "{s}"
  for p in #[a3,growth,minimum,finite] do
    let selected := rows.filter (fun r => (r.getObjValAs? String "provider").toOption == some p.toString)
    unless selected.size == 1 do throwError "Expected exactly one full application of {p}"
  let mut declarationOrigins : Array Json := #[]
  for (n,expected) in #[(name,`StrongConvexAttainmentCandidate),(a3,`WeierstrassExtendedCandidate),
      (growth,`BanditRLProof.OnlineStrongConvexSourceSubgradient),
      (minimum,`BanditRLProof.OnlineStrongConvexMinimum),(finite,`BanditRLProof.OnlineSubgradientBasic)] do
    let some idx := env.getModuleIdxFor? n | throwError "Missing module origin {n}"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == expected do throwError "Wrong module origin {n}"
    let file ← liftIO <| findOLean mod
    declarationOrigins := declarationOrigins.push <| Json.mkObj [("declaration",toJson n.toString),
      ("module",toJson mod.toString),("olean",toJson file.toString)]
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
  let report := Json.mkObj [("declaration",toJson name.toString),("TYPE",toJson (deps ci.type)),
    ("VALUE",toJson (deps value)),("header_telescope",toJson (header.map Name.toString)),
    ("provider_operands",toJson rows),("declaration_origins",toJson declarationOrigins),
    ("structural_limits",toJson "Binder-name operand checks require actual compiled candidate review. Coordinate finite objective/base checked for f/e and e/y occurrence only, not complete expected-lambda equality. All implicit instance expressions and derived finite-dimensional/compactness terms exported separately, without independent expected-instance equality assertions. No source/BODY acceptance inferred.")]
  liftIO do
    let base := "tmp/online-b4-next-attainment-body-20261012/"
    let f ← IO.FS.Handle.mk (base ++ "imported-audit-construction-v1.json") .writeNew
    f.putStr (report.pretty ++ "\n")
    let o ← IO.FS.Handle.mk (base ++ "imported-origins-construction-v1.json") .writeNew
    o.putStr ((toJson origins).pretty ++ "\n")
    let a ← IO.FS.Handle.mk (base ++ "provider-operands-construction-v1.txt") .writeNew
    a.putStr (String.intercalate "\n" raw.toList)
    for (label,e) in #[("TYPE",ci.type),("VALUE",value)] do
      let s ← IO.FS.Handle.mk (base ++ label ++ "-normalized-construction-v1.txt") .writeNew
      s.putStr ((repr (canon e)).pretty ++ "\n")
