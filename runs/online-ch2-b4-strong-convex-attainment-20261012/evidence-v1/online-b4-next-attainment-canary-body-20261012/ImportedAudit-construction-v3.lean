import StrongConvexAttainmentCanaries
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.Tests.OnlineStrongConvexAttainmentCanary.halfline_quadratic_unique_attainment
#print axioms BanditRL.Tests.OnlineStrongConvexAttainmentCanary.zero_curvature_affine_has_no_minimum
run_cmd do
  let env ← getEnv
  let positive := `BanditRL.Tests.OnlineStrongConvexAttainmentCanary.halfline_quadratic_unique_attainment
  let negative := `BanditRL.Tests.OnlineStrongConvexAttainmentCanary.zero_curvature_affine_has_no_minimum
  let parent := `BanditRL.OnlineConvex.stronglyConvex_existsUnique_minimizer
  let some pos := env.find? positive | throwError "Missing positive canary"
  let some neg := env.find? negative | throwError "Missing zero canary"
  let some pv := pos.value? (allowOpaque := true) | throwError "Missing positive VALUE"
  let some nv := neg.value? (allowOpaque := true) | throwError "Missing negative VALUE"
  unless !pos.type.isForall && !neg.type.isForall do throwError "Closed canary acquired premise"
  unless !nv.getUsedConstantsAsSet.contains parent do throwError "Invalid attainment call in zero case"
  let bn := fun (ctx : Array Name) (e : Expr) => match e with
    | .bvar i => ctx[ctx.size - 1 - i]?.getD .anonymous
    | _ => .anonymous
  let rec first (ctx : Array Name) : Expr → Except String Unit
    | .letE n _ _ b _ => first (ctx.push n) b
    | .mdata _ b => first ctx b
    | e => do
      unless e.getAppFn.isConstOf `And.intro && e.getAppArgs.size == 4 &&
          bn ctx e.getAppArgs[2]! == `hattainment do
        throw "First conjunction is not actual attained-minimum result"
  match first #[] pv with
  | .ok _ => pure ()
  | .error s => throwError "{s}"
  let rec walk (ctx : Array Name) (e : Expr) : Except String (Array Json × Array String) := do
    let mut rows : Array Json := #[]
    let mut raw : Array String := #[]
    let args := e.getAppArgs
    if e.getAppFn.isConstOf parent && args.size == 12 then
      unless args[0]!.isConstOf `BanditRL.Tests.OnlineStrongConvexAttainmentCanary.E do throw "Wrong actual ambient"
      let expectedDimension := mkApp3 (mkConst `OfNat.ofNat [Level.zero])
        (mkConst `Nat) (mkRawNatLit 1) (mkApp (mkConst `instOfNatNat) (mkRawNatLit 1))
      unless args[3]! == expectedDimension do throw "Wrong exact typed dimension"
      unless args[4]!.isConstOf `BanditRL.Tests.OnlineStrongConvexAttainmentCanary.coordinates do throw "Wrong coordinates"
      unless args[5]!.isConstOf `BanditRL.Tests.OnlineStrongConvexAttainmentCanary.quadratic do throw "Wrong objective"
      let lam := args[6]!
      let expectedCurvature := mkApp3 (mkConst `OfNat.ofNat [Level.zero])
        (mkConst `Real) (mkRawNatLit 1)
        (mkApp2 (mkConst `One.toOfNat1 [Level.zero]) (mkConst `Real) (mkConst `Real.instOne))
      unless lam == expectedCurvature do throw "Wrong exact typed positive curvature"
      for (i,n) in (#[(7,`hproper),(8,`hclosed),(10,`hstrong),(11,`hsub)] : Array (Nat × Name)) do
        unless bn ctx args[i]! == n do throw s!"Wrong internal premise{i}"
      rows := rows.push <| Json.mkObj [("provider",toJson parent.toString),("arity",toJson args.size),
        ("operand_binders",toJson (args.map (fun a => (bn ctx a).toString)))]
      for i in [:args.size] do raw := raw.push s!"ACTUAL ARG {i}\n{(repr args[i]!).pretty}\n"
    match e with
    | .app f a =>
      let (r,s) ← walk ctx f; rows := rows ++ r; raw := raw ++ s
      let (r,s) ← walk ctx a; rows := rows ++ r; raw := raw ++ s
    | .lam n t b _ | .forallE n t b _ =>
      let (r,s) ← walk ctx t; rows := rows ++ r; raw := raw ++ s
      let (r,s) ← walk (ctx.push n) b; rows := rows ++ r; raw := raw ++ s
    | .letE n t v b _ =>
      if n == `hsub || n == `hsupport then raw := raw.push s!"SUPPORT LET {n}\nTYPE {(repr t).pretty}\nVALUE {(repr v).pretty}\n"
      let (r,s) ← walk ctx t; rows := rows ++ r; raw := raw ++ s
      let (r,s) ← walk ctx v; rows := rows ++ r; raw := raw ++ s
      let (r,s) ← walk (ctx.push n) b; rows := rows ++ r; raw := raw ++ s
    | .mdata _ b | .proj _ _ b =>
      let (r,s) ← walk ctx b; rows := rows ++ r; raw := raw ++ s
    | _ => pure ()
    return (rows,raw)
  let (providerRows,raw) ← match walk #[] pv with
    | .ok r => pure r
    | .error s => throwError "{s}"
  unless providerRows.size == 1 do throwError "Expected one full positive parent application"
  let mut declarationOrigins : Array Json := #[]
  for (n,expected) in #[(positive,`StrongConvexAttainmentCanaries),(negative,`StrongConvexAttainmentCanaries),(parent,`StrongConvexAttainmentCandidate)] do
    let some idx := env.getModuleIdxFor? n | throwError "Missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == expected do throwError "Wrong actual module binding"
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
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let rows := #[(positive,pos.type,pv),(negative,neg.type,nv)] |>.map fun (n,t,v) =>
    Json.mkObj [("declaration",toJson n.toString),("TYPE",toJson (deps t)),("VALUE",toJson (deps v))]
  let report := Json.mkObj [("rows",toJson rows),("provider_operands",toJson providerRows),
    ("first_conjunction_actual_parent",toJson true),("zero_case_no_parent_call",toJson true),
    ("declaration_origins",toJson declarationOrigins),
    ("limitations",toJson "Implicit normed-space instances and positivity proof exported, not independently expected-Expr equality asserted. hsub/hsupport let values exported but witness point0/g-2 not independently structurally equated here. Compiled BODY and independent SOURCE review must establish complete witness flow; matching calls are not acceptance.")]
  liftIO do
    let base := "tmp/online-b4-next-attainment-canary-body-20261012/"
    let r ← IO.FS.Handle.mk (base ++ "imported-audit-v1.json") .writeNew
    r.putStr (report.pretty ++ "\n")
    let o ← IO.FS.Handle.mk (base ++ "imported-origins-v1.json") .writeNew
    o.putStr ((toJson origins).pretty ++ "\n")
    let a ← IO.FS.Handle.mk (base ++ "provider-operands-v1.txt") .writeNew
    a.putStr (String.intercalate "\n" raw.toList)
    for (label,t,v) in #[("positive",pos.type,pv),("zero",neg.type,nv)] do
      for (kind,e) in #[("TYPE",t),("VALUE",v)] do
        let s ← IO.FS.Handle.mk (base ++ label ++ "-" ++ kind ++ "-normalized-v1.txt") .writeNew
        s.putStr ((repr (canon e)).pretty ++ "\n")
