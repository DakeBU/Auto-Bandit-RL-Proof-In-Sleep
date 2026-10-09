import BanditRLProof.OnlinePrescientLinear
import Tests.OnlinePrescientLinearCanary
import Lean
import Lean.Util.FoldConsts
open Lean

def targets : Array Name := #[
`BanditRL.OnlinePrescientLinear.advance_sharp_bound,
`BanditRL.OnlinePrescientLinear.advance_proximal_minimizer,
`BanditRL.OnlinePrescientLinear.prediction_mem,
`BanditRL.OnlinePrescientLinear.prediction_prefix,
`BanditRL.OnlinePrescientLinear.regret_eq_loss_difference,
`BanditRL.OnlinePrescientLinear.regret_sharp_bound,
`BanditRL.OnlinePrescientLinear.regret_source_bound,
`Tests.OnlinePrescientLinear.active_projection_values,
`Tests.OnlinePrescientLinear.constrained_gradient_sign_counterexample,
`Tests.OnlinePrescientLinear.unbounded_exact_identity,
`Tests.OnlinePrescientLinear.current_and_future_information,
`Tests.OnlinePrescientLinear.outside_initial_center_and_empty_horizon,
`BanditRL.OnlinePrescientLinear.advance,
`BanditRL.OnlinePrescientLinear.iterate,
`BanditRL.OnlinePrescientLinear.prediction,
`BanditRL.OnlinePrescientLinear.regret,
`Tests.OnlinePrescientLinear.interval,
`Tests.OnlinePrescientLinear.whole,
`Tests.OnlinePrescientLinear.signals,
`BanditRL.OnlineGradientDescent.project,
`BanditRL.OnlineGradientDescent.project_spec,
`BanditRL.OnlineGradientDescent.project_eq_of_variational,
`BanditRL.OnlineGradientDescentSource.gradient_linear]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof.OnlinePrescientLinear }, { module := `Tests.OnlinePrescientLinearCanary }] {} (loadExts := true)
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
      if dep.toString.startsWith "_private.Tests.OnlinePrescientLinearCanary." && !selected.contains dep then
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
      ("scope", toJson "Seven frozen production terminals, five exact canaries, actual definitions/projection/gradient parents and recursively selected private scalar Test helpers. Direct TYPE_VALUE constant presence only; private helper traversal does not make this the full transitive or shared registry graph. Counts are not printed results or chapter acceptance.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
