import Tests.OnlineProximalComparisonCanary
import Lean
import Lean.Util.FoldConsts
open Lean

partial def numericTail (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => numericTail (body.instantiate1 value)
  | .mdata _ body => numericTail body
  | _ =>
    if e.getAppFn.isConstOf ``And.intro && e.getAppArgs.size == 4 then
      numericTail e.getAppArgs[3]!
    else e

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then
    throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineProximalComparisonCanary }] {} (loadExts := true)
  let mut rows : Array Json := #[]
  for name in #[`BanditRL.OnlineProximalCanary.nonsmooth_shifted_quadratic,
      `BanditRL.OnlineProximalCanary.nonconvex_regularizer] do
    let some info := env.find? name | throw <| IO.userError s!"missing {name}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing value {name}"
    let tail := numericTail value
    let deps := tail.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let fn := match tail.getAppFn with | .const n _ => n.toString | _ => "nonconstant-head"
    rows := rows.push <| Json.mkObj [
      ("declaration", toJson name.toString),
      ("selected_tail_head", toJson fn),
      ("selected_tail_direct_constants", toJson <| deps.map Name.toString),
      ("public_helper_in_selected_tail", toJson <| deps.contains `BanditRL.OnlineProximal.convex_minimizer_comparison)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source", toJson "actual-compiled-environment"),
    ("selection", toJson "Inline top-level lets by substitution, remove metadata, descend the rightmost And.intro constructor. No theorem unfolding or proof-irrelevance normalization; inspect actual final numeric proof expression, not whole-conjunction dependency."),
    ("rows", Json.arr rows)]).pretty ++ "\n")
  return 0
