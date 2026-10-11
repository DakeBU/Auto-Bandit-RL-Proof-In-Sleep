import FullIffCanaries
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.Tests.OnlineStrongConvexSubgradientIffCanary.box_converse_originalNorm
#print axioms BanditRL.Tests.OnlineStrongConvexSubgradientIffCanary.absent_support_vacuity
run_cmd do
  let env ← getEnv
  let ns := `BanditRL.Tests.OnlineStrongConvexSubgradientIffCanary
  let iffName := `BanditRL.OnlineConvex.stronglyConvex_iff_sourceSubgradient_growth
  let names := #[ns ++ `box_converse_originalNorm,ns ++ `absent_support_vacuity]
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let rec exposeId : Expr → Expr
    | .mdata _ b => exposeId b
    | e => if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then exposeId e.getAppArgs[1]! else e
  let rec peel (ctx : Array (Name × Expr)) (e : Expr) : Array (Name × Expr) × Expr :=
    match exposeId e with
    | .letE n _ v b _ => peel (ctx.push (n,v)) b
    | e => (ctx,e)
  let some ci := env.find? names[0]! | throwError "Missing first canary"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing first VALUE"
  let (ctx,outer) := peel #[] value
  let binderName := fun (e : Expr) => match e with
    | .bvar i => (ctx[ctx.size-1-i]?.map Prod.fst).getD .anonymous
    | _ => .anonymous
  unless outer.getAppFn.isConstOf ``And.intro && outer.getAppArgs.size == 4 do throwError "No first conjunction"
  unless binderName outer.getAppArgs[2]! == `hbound do throwError "First conjunct is not actual hbound"
  let some boundIndex := ctx.findIdx? (fun (n,_) => n == `hbound) | throwError "No bound provider binding"
  let bound := exposeId ctx[boundIndex]!.2
  unless bound.getAppFn.isConstOf ``Iff.mpr && bound.getAppArgs.size == 4 do
    throwError "First provider not Iff.mpr arity4; head={bound.getAppFn.constName?},args={bound.getAppArgs.size}"
  let ba := bound.getAppArgs
  let iffProof := ba[2]!
  unless iffProof.getAppFn.isConstOf iffName && iffProof.getAppArgs.size == 12 do throwError "Wrong iff theorem/application arity"
  let ia := iffProof.getAppArgs
  for (i,n) in #[(4,ns ++ `scaledCoordinates),(5,ns ++ `objective),(6,ns ++ `feasible)] do
    unless ia[i]!.isConstOf n do throwError "Wrong iff concrete operand {i}"
  let numeral := fun (e : Expr) (n : Nat) => e == mkNatLit n ||
    (e.getAppFn.isConstOf ``OfNat.ofNat && e.getAppArgs.size == 3 && e.getAppArgs[1]! == mkRawNatLit n)
  unless numeral ia[3]! 2 && numeral ia[7]! 1 do throwError "Wrong dimension or curvature"
  let localName := fun (e : Expr) => match e with
    | .bvar i => (ctx[boundIndex-1-i]?.map Prod.fst).getD .anonymous
    | _ => .anonymous
  unless localName ia[8]! == `hproper && localName ia[9]! == `hconv && localName ba[3]! == `hgrowth do
    throwError "Properness/convexity/every-g growth are not actual proved local operands"
  let some growthIndex := ctx.findIdx? (fun (n,_) => n == `hgrowth) | throwError "Missing actual growth proof"
  let growthDeps := deps ctx[growthIndex]!.2
  let some subIndex := ctx.findIdx? (fun (n,_) => n == `hsub) | throwError "Missing actual global support proof"
  let subDeps := deps ctx[subIndex]!.2
  for forbidden in #[iffName.toString,"BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth",
      "BanditRL.OnlineConvex.stronglyConvex_support_growth"] do
    unless !growthDeps.contains forbidden && !subDeps.contains forbidden do throwError "Circular growth/support proof"
  unless ia[11]!.isLambda do throwError "All-point support operand is not actual internally constructed lambda"
  let mut rows : Array Json := #[]
  for n in names do
    let some c := env.find? n | throwError "Missing theorem"
    let some v := c.value? (allowOpaque := true) | throwError "Missing proof"
    let some idx := env.getModuleIdxFor? n | throwError "Missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == `FullIffCanaries do throwError "Wrong canary module binding"
    let path ← liftIO <| findOLean mod
    rows := rows.push <| Json.mkObj [("name",toJson n.toString),("TYPE",toJson (deps c.type)),
      ("VALUE",toJson (deps v)),("module",toJson mod.toString),("resolved_olean",toJson path.toString)]
  let some idx := env.getModuleIdxFor? iffName | throwError "Missing iff origin"
  let iffMod := env.header.moduleNames[idx.toNat]!
  unless iffMod == `FullIffCandidate do throwError "Wrong actual iff module binding"
  let iffPath ← liftIO <| findOLean iffMod
  let output := Json.mkObj [("declarations",toJson rows),("first_conjunct_provider",toJson "Iff.mpr actual frozen iff theorem"),
    ("iff_arity",toJson ia.size),("iff_module",toJson iffMod.toString),("iff_resolved_olean",toJson iffPath.toString),
    ("exact_operands",toJson "d2, scaledCoordinates, objective, feasible, lambda1, actual hproper/hconv, actual all-point support lambda, actual hgrowth"),
    ("growth_and_support_exclude_forward_or_iff_calls",toJson true),
    ("growth_constants",toJson growthDeps),("support_constants",toJson subDeps),
    ("all_point_support_expression_small",toJson (reprStr ia[11]!))]
  liftIO do
    let file ← IO.FS.Handle.mk "tmp/online-b4-full-iff-canary-body-20261012/imported-provider-v1.json" .writeNew
    file.putStr (output.pretty ++ "\n")
