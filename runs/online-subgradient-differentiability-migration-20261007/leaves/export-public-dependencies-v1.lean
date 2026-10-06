import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
  `BanditRL.OnlineConvex.subgradient_norm_le_lipschitz_ball,
  `BanditRL.OnlineConvex.subgradients_locally_bounded,
  `BanditRL.OnlineConvex.subgradient_limit_of_continuousAt,
  `BanditRL.OnlineConvex.singleton_subgradient_tendsto,
  `BanditRL.OnlineConvex.singleton_subdifferential_interior,
  `BanditRL.OnlineConvex.singleton_subdifferential_hasGradientAt,
  `BanditRL.OnlineConvex.sourceDifferentiableAt_regular,
  `BanditRL.OnlineConvex.subgradient_eq_gradient_at_interior,
  `BanditRL.OnlineConvex.theorem_2_22_gradient,
  `BanditRL.OnlineConvex.theorem_2_22_forward,
  `BanditRL.OnlineConvex.theorem_2_22,
  `ForwardSubgradientProbe.constrained_interval_singleton,
  `ForwardSubgradientProbe.quadratic_singleton_nonzero,
  `DifferentiabilityProbe.constrained_interval_differentiable,
  `DifferentiabilityProbe.quadratic_derivative_nonzero,
  `DifferentiabilityProbe.interval_boundary_supports,
  `DifferentiabilityProbe.interval_boundary_not_differentiable,
  `Tests.OnlineDifferentiabilityBoundary.singleton_toReal_differentiable,
  `Tests.OnlineDifferentiabilityBoundary.singleton_not_sourceDifferentiable,
  `Tests.OnlineDifferentiabilityBoundary.singleton_global_supports,
  `BanditRL.OnlineConvex.SourceDifferentiableAt]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof }, { module := `Tests.OnlineSubgradientDifferentiabilityCanary }, { module := `Tests.OnlineDifferentiabilityBoundaryCanary }] {} (loadExts := true)
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
      ("scope", toJson "eleven retained producer proofs, one complete definition and nine old/new canary proofs; selected direct type/value boundary only; not full registry graph")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
