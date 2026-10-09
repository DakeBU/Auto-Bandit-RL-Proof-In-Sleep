import Tests.OnlineUnboundedOSDCanary
import Lean
import Lean.Util.FoldConsts
open Lean

def targets : Array Name := #[
`BanditRL.OnlineUnboundedOSD.powerSteps,
`BanditRL.OnlineUnboundedOSD.phi,
`BanditRL.OnlineUnboundedOSD.switchSlope,
`BanditRL.OnlineUnboundedOSD.switchLoss,
`BanditRL.OnlineUnboundedOSD.currentSubgradient_affine,
`BanditRL.OnlineUnboundedOSD.step_affine_fullSpace,
`BanditRL.OnlineUnboundedOSD.iterate_affine_prefix,
`BanditRL.OnlineUnboundedOSD.powerSteps_pos,
`BanditRL.OnlineUnboundedOSD.switching_loss_regular,
`BanditRL.OnlineUnboundedOSD.switching_scalar_regret_identity,
`BanditRL.OnlineUnboundedOSD.phi_range,
`BanditRL.OnlineUnboundedOSD.phi_limit,
`BanditRL.OnlineUnboundedOSD.switching_scalar_lower_bound,
`BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound,
`BanditRL.OnlineUnboundedOSD.theorem_5_4,
`BanditRL.OnlineUnboundedOSDCanary.scalar_actual_two_rounds,
`BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineUnboundedOSDCanary }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  let mut selected := targets
  let mut i := 0
  while i < selected.size do
    let n := selected[i]!
    i := i + 1
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing proof {n}"
    for dep in deps value do
      if dep.toString.startsWith "_private.Tests.OnlineUnboundedOSDCanary." && !selected.contains dep then
        selected := selected.push dep
  for n in selected do
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
      ("dependency_semantics", toJson "coalesced-direct-TYPE_VALUE-constant-presence-not-occurrence-count"),
      ("scope", toJson "Four exact source definitions, eleven frozen production proofs and two complete7/9conjunct Test canaries plus referenced compiler-generated Test auxiliaries. Selected direct TYPE_VALUE constant presences; not occurrence counts, full transitive graph, shared registry or chapter/source theorem denominator.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
