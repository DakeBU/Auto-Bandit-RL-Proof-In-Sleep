import Tests.OnlineGuessingSubgradientCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineGuessingSubgradient.loss_subdifferential_translate,
 `BanditRL.OnlineGuessingSubgradient.loss_subgradient_positive,
 `BanditRL.OnlineGuessingSubgradient.loss_subgradient_zero,
 `BanditRL.OnlineGuessingSubgradient.loss_subgradient_negative,
 `BanditRL.OnlineGuessingSubgradient.example_2_32_subdifferential,
 `BanditRL.OnlineGuessingSubgradient.loss_on_unitInterval,
 `BanditRL.OnlineGuessingSubgradient.loss_subgradient_bound,
 `BanditRL.OnlineGuessingSubgradient.current_subgradient_bound,
 `BanditRL.OnlineGuessingSubgradient.loss_step_clamp,
 `BanditRL.OnlineGuessingSubgradient.guessing_prefix,
 `BanditRL.OnlineGuessingSubgradient.example_2_32,
 `BanditRL.OnlineGuessingSubgradient.example_2_32_average_eventually,
 `BanditRL.OnlineGuessingSubgradient.loss,
 `GuessingOSDProbe.shifted_positive,
 `GuessingOSDProbe.shifted_negative,
 `GuessingOSDProbe.shifted_equal,
 `GuessingOSDProbe.nonzero_tie_support,
 `GuessingOSDProbe.invalid_tie_support,
 `GuessingOSDProbe.canonical_tie_in_full_interval,
 `GuessingOSDProbe.chosen_above,
 `GuessingOSDProbe.chosen_below,
 `GuessingOSDProbe.labels_feasible,
 `GuessingOSDProbe.output_zero,
 `GuessingOSDProbe.output_one,
 `GuessingOSDProbe.output_two,
 `GuessingOSDProbe.output_three,
 `GuessingOSDProbe.output_four,
 `GuessingOSDProbe.four_round_real_regret,
 `GuessingOSDProbe.four_round_fixed_with_terminal,
 `GuessingOSDProbe.four_round_energy,
 `GuessingOSDProbe.four_round_positive_terminal,
 `GuessingOSDProbe.four_round_bound_rhs_exact,
 `GuessingOSDProbe.horizon_four_tuned_same_eta,
 `GuessingOSDProbe.all_comparators_four,
 `GuessingOSDProbe.chosen_clipping,
 `GuessingOSDProbe.actual_raw_overshoot_and_clamp,
 `GuessingOSDProbe.invalid_future_does_not_change_output,
 `GuessingOSDProbe.no_future_feasibility_assumed,
 `GuessingOSDProbe.zero_horizon_regret,
 `GuessingOSDProbe.eventual_one_sided_horizon_family,
 `GuessingOSDProbe.labels,
 `GuessingOSDProbe.losses,
 `GuessingOSDProbe.eta,
 `GuessingOSDProbe.output,
 `GuessingOSDProbe.futureLabels,
 `GuessingOSDProbe.futureEta,
 `GuessingOSDProbe.interval]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingSubgradientCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingSubgradientCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Existing twelve canonical guessing proof bodies/one loss definition and whole actual canary; compiled TEST module, selected47 actual nodes/direct type-value references, not full registry or combined-root gate; ZERO new mathematics")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
