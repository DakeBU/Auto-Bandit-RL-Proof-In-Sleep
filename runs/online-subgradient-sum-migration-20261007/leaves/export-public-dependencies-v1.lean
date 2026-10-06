import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
  `BanditRL.OnlineConvex.upperAdd_eq_add_of_ne_bot,
  `BanditRL.OnlineConvex.ereal_finset_sum_ne_bot,
  `BanditRL.OnlineConvex.convex_finset_sum,
  `BanditRL.OnlineConvex.finite_sum_point,
  `BanditRL.OnlineConvex.sum_finite_implies_components_finite,
  `BanditRL.OnlineConvex.interior_domain_sum,
  `BanditRL.OnlineConvex.binary_subgradient_decomposition,
  `BanditRL.OnlineConvex.theorem_2_23_inclusion,
  `BanditRL.OnlineConvex.theorem_2_23_equality,
  `BanditRL.OnlineConvex.SourceSubgradientSum,
  `SumEqualityProbe.square_proper,
  `SumEqualityProbe.square_domain,
  `SumEqualityProbe.square_convex,
  `SumEqualityProbe.square_closed,
  `SumEqualityProbe.interval_proper,
  `SumEqualityProbe.interval_convex,
  `SumEqualityProbe.interval_closed,
  `SumEqualityProbe.family_proper,
  `SumEqualityProbe.family_convex,
  `SumEqualityProbe.family_closed,
  `SumEqualityProbe.family_mixed_qualification,
  `SumEqualityProbe.nonzero_aggregate_support,
  `SumEqualityProbe.actual_three_component_decomposition,
  `SumEqualityProbe.last_domain_boundary,
  `SumEqualityProbe.outside_domain_both_empty,
  `SumEqualityProbe.singleton_family_empty_interior,
  `SumRuleProbe.quadratic_plus_constraint_support,
  `SumRuleProbe.concave_quadratic_no_support,
  `SumRuleProbe.nonconvex_vacuous_inclusion,
  `SumRuleProbe.empty_family_zero_support,
  `SumEqualityProbe.square,
  `SumEqualityProbe.interval,
  `SumEqualityProbe.family]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof }, { module := `Tests.OnlineSubgradientSumCanary }] {} (loadExts := true)
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
      ("scope", toJson "nine retained sum-rule proofs, one complete Minkowski definition, twenty whole canary proofs and three canary definitions; direct type/value boundary only")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
