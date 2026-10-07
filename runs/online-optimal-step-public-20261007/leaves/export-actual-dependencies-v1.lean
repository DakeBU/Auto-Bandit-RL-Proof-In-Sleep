import Tests.OnlineOptimalStepCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineOptimalStep.gap_identity,
 `BanditRL.OnlineOptimalStep.lower_bound,
 `BanditRL.OnlineOptimalStep.optimal_positive,
 `BanditRL.OnlineOptimalStep.optimal_value,
 `BanditRL.OnlineOptimalStep.optimal_unique,
 `BanditRL.OnlineOptimalStep.source_argmin,
 `BanditRL.OnlineOptimalStep.distance_energy_argmin,
 `BanditRL.OnlineOptimalStep.diameter_argmin,
 `BanditRL.OnlineOptimalStep.zero_distance_decreases,
 `BanditRL.OnlineOptimalStep.zero_energy_decreases,
 `BanditRL.OnlineOptimalStep.zero_coefficients,
 `BanditRL.OnlineOptimalStep.upperBound,
 `BanditRL.OnlineOptimalStep.optimalStep,
 `OptimalStepProbe.positive_optimizer,
 `OptimalStepProbe.chosen,
 `OptimalStepProbe.attained,
 `OptimalStepProbe.public_argmin,
 `OptimalStepProbe.universal,
 `OptimalStepProbe.unique,
 `OptimalStepProbe.wrong_eta_strict,
 `OptimalStepProbe.tuned,
 `OptimalStepProbe.horizon_one,
 `OptimalStepProbe.zero_distance_no_min,
 `OptimalStepProbe.zero_energy_no_min,
 `OptimalStepProbe.all_zero,
 `OptimalStepProbe.zero_distance_optimizer_inadmissible,
 `OptimalStepProbe.division_zero_inadmissible,
 `OptimalStepProbe.zero_horizon_boundary,
 `OptimalStepProbe.actual_gradient,
 `OptimalStepProbe.actual_projection,
 `OptimalStepProbe.first_output,
 `OptimalStepProbe.after_one,
 `OptimalStepProbe.first_feedback,
 `OptimalStepProbe.second_feedback,
 `OptimalStepProbe.energy_formula,
 `OptimalStepProbe.same_loss_different_energy,
 `OptimalStepProbe.loss,
 `OptimalStepProbe.X,
 `OptimalStepProbe.feedback,
 `OptimalStepProbe.energy,
 `OptimalStepProbe.V]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineOptimalStepCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineOptimalStepCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Existing11 scalar proof bodies/2 definitions and whole canary; compiled TEST environment selected41 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
