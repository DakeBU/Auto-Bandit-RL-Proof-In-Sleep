import Tests.OnlineLipschitzSubgradientCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineConvex.SourceLipschitzOn,
 `BanditRL.OnlineConvex.theorem_2_30,
 `LipschitzProbe.abs_proper,
 `LipschitzProbe.abs_domain,
 `LipschitzProbe.abs_convex,
 `LipschitzProbe.abs_lipschitz,
 `LipschitzProbe.abs_all_supports_and_nonzero,
 `LipschitzProbe.linear_proper,
 `LipschitzProbe.linear_convex,
 `LipschitzProbe.linear_three_reverse,
 `LipschitzProbe.zero_proper,
 `LipschitzProbe.zero_convex,
 `LipschitzProbe.zero_constant,
 `LipschitzProbe.singleton_empty_interior_and_boundary,
 `LipschitzProbe.halfline_proper,
 `LipschitzProbe.halfline_convex,
 `LipschitzProbe.halfline_lipschitz,
 `LipschitzProbe.halfline_interior_not_whole_domain,
 `LipschitzProbe.zero_dimension,
 `LipschitzSourceAudit.negative_constant_zero_dimension,
 `LipschitzProbe.absLoss,
 `LipschitzProbe.linearLoss,
 `LipschitzProbe.zeroLoss,
 `LipschitzProbe.halflineLoss,
 `LipschitzProbe.nineLoss,
 `LipschitzSourceAudit.zeroLoss,
 `LipschitzProbe.Z,
 `LipschitzSourceAudit.Z]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof }, { module := `Tests.OnlineLipschitzSubgradientCanary }] {} (loadExts := true)
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
      ("scope", toJson "selected actual Lipschitz nodes; direct type/value occurrences only, not full registry graph")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
