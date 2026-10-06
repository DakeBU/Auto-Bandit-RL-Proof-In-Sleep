import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineConvex.SourceFiniteMax,
 `BanditRL.OnlineConvex.SourceActiveSubgradientUnion,
 `BanditRL.OnlineConvex.active_subgradient_support_max,
 `BanditRL.OnlineConvex.finiteMax_attained,
 `BanditRL.OnlineConvex.finiteMax_point_finite,
 `BanditRL.OnlineConvex.subgradient_iff_real_support,
 `BanditRL.OnlineConvex.convex_sourceSubdifferential,
 `BanditRL.OnlineConvex.continuousAt_mem_domain_interior,
 `BanditRL.OnlineConvex.finiteMax_ne_bot,
 `BanditRL.OnlineConvex.convexHull_active_support_max,
 `BanditRL.OnlineConvex.isClosed_sourceSubdifferential,
 `BanditRL.OnlineConvex.isCompact_sourceSubdifferential,
 `BanditRL.OnlineConvex.isCompact_convexJoin,
 `BanditRL.OnlineConvex.isCompact_convexHull_finite_convex_union,
 `BanditRL.OnlineConvex.isCompact_active_subgradient_hull,
 `BanditRL.OnlineConvex.continuousAt_finite_toReal,
 `BanditRL.OnlineConvex.max_support_displacement_compare,
 `BanditRL.OnlineConvex.max_subgradient_direction_witness,
 `BanditRL.OnlineConvex.theorem_2_26]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  for n in targets do
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing proof {n}"
    let td := deps info.type
    let vd := deps value
    nodes := nodes.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson <| moduleName env n),
      ("kind", toJson <| match info with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other"), ("has_value", toJson true),
      ("type_dependencies", toJson <| td.map Name.toString),
      ("value_dependencies", toJson <| vd.map Name.toString)]
    for target in td do
      edges := edges.push <| Json.mkObj [
        ("source", toJson n.toString), ("target", toJson target.toString),
        ("kind", toJson "type"), ("also_in_value", toJson <| vd.contains target),
        ("target_module", toJson <| moduleName env target)]
    for target in vd do
      if !td.contains target then
        edges := edges.push <| Json.mkObj [
          ("source", toJson n.toString), ("target", toJson target.toString),
          ("kind", toJson "value"), ("also_in_value", toJson false),
          ("target_module", toJson <| moduleName env target)]
  let graph := Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "BanditRLProof"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "nineteen retained finite-maximum production nodes: two definitions/seventeen proofs; direct type/value occurrence only; canaries not yet exported")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
