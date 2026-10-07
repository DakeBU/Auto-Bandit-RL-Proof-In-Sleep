import Tests.OnlineUnitScalingCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineUnitScaling.unit_exponents,
 `BanditRL.OnlineUnitScaling.regret_unit_exponents,
 `BanditRL.OnlineUnitScaling.inverse_loss,
 `BanditRL.OnlineUnitScaling.proper_scaled_loss,
 `BanditRL.OnlineUnitScaling.subgradient_scaled,
 `BanditRL.OnlineUnitScaling.subdifferentiable_scaled,
 `BanditRL.OnlineUnitScaling.hasGradientAt_scaled,
 `BanditRL.OnlineUnitScaling.gradient_scaled,
 `BanditRL.OnlineUnitScaling.step_scaling,
 `BanditRL.OnlineUnitScaling.wrong_step_scaling,
 `BanditRL.OnlineUnitScaling.scaled_eta_positive,
 `BanditRL.OnlineUnitScaling.history_scaling,
 `BanditRL.OnlineUnitScaling.output_scaling,
 `BanditRL.OnlineUnitScaling.selected_scaling,
 `BanditRL.OnlineUnitScaling.legal_feedback_scaling,
 `BanditRL.OnlineUnitScaling.loss_value_scaling,
 `BanditRL.OnlineUnitScaling.regret_scaling,
 `BanditRL.OnlineUnitScaling.wrong_step_output,
 `BanditRL.OnlineUnitScaling.distance_square_scaling,
 `BanditRL.OnlineUnitScaling.energy_scaling,
 `BanditRL.OnlineUnitScaling.upper_bound_scaling,
 `BanditRL.OnlineUnitScaling.regret_fixed_scaled,
 `BanditRL.OnlineUnitScaling.scaledLoss,
 `BanditRL.OnlineUnitScaling.scaledEta,
 `BanditRL.OnlineUnitScaling.scaledPolicy,
 `BanditRL.OnlineUnitScaling.V,
 `UnitScalingProbe.dimensions_eta,
 `UnitScalingProbe.dimensions_regret,
 `UnitScalingProbe.real_linear_gradient,
 `UnitScalingProbe.real_scaled_gradient,
 `UnitScalingProbe.support,
 `UnitScalingProbe.loss_on,
 `UnitScalingProbe.selected_one,
 `UnitScalingProbe.legal,
 `UnitScalingProbe.correct_eta,
 `UnitScalingProbe.positive_eta,
 `UnitScalingProbe.old_one,
 `UnitScalingProbe.correct_path,
 `UnitScalingProbe.wrong_path,
 `UnitScalingProbe.physical_path_difference,
 `UnitScalingProbe.transformed_selected,
 `UnitScalingProbe.transformed_legal,
 `UnitScalingProbe.old_regret,
 `UnitScalingProbe.correct_regret,
 `UnitScalingProbe.positive_old_energy,
 `UnitScalingProbe.positive_terminal,
 `UnitScalingProbe.scaled_energy,
 `UnitScalingProbe.scaled_distance,
 `UnitScalingProbe.actual_sharp_bound,
 `UnitScalingProbe.sharp_rhs,
 `UnitScalingProbe.coarse_bound_invariant,
 `UnitScalingProbe.inverse_inadmissible_zero,
 `UnitScalingProbe.identity_scale,
 `UnitScalingProbe.source_horizon_boundary,
 `UnitScalingProbe.empty_regret,
 `UnitScalingProbe.zero_horizon_actual_sharp,
 `UnitScalingProbe.loss,
 `UnitScalingProbe.policy,
 `UnitScalingProbe.eta,
 `UnitScalingProbe.old,
 `UnitScalingProbe.good,
 `UnitScalingProbe.bad]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineUnitScalingCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineUnitScalingCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Existing22 unit-scaling proof bodies/3 definitions/1 abbreviation and whole canary; compiled TEST environment selected62 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
