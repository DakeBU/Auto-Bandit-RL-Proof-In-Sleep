import Tests.OnlineGuessingSubgradientPolicyCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineGuessingSubgradientPolicy.selected_bound,
 `BanditRL.OnlineGuessingSubgradientPolicy.step_clamp,
 `BanditRL.OnlineGuessingSubgradientPolicy.example_2_32,
 `BanditRL.OnlineGuessingSubgradientPolicy.example_2_32_average_eventually,
 `GuessingPolicyProbe.policy_on_absolute,
 `GuessingPolicyProbe.policy_legal,
 `GuessingPolicyProbe.selected_rule,
 `GuessingPolicyProbe.labelsA_feasible,
 `GuessingPolicyProbe.labelsB_feasible,
 `GuessingPolicyProbe.a_zero,
 `GuessingPolicyProbe.b_zero,
 `GuessingPolicyProbe.ga_zero,
 `GuessingPolicyProbe.gb_zero,
 `GuessingPolicyProbe.a_one,
 `GuessingPolicyProbe.b_one,
 `GuessingPolicyProbe.ga_one,
 `GuessingPolicyProbe.gb_one,
 `GuessingPolicyProbe.a_two,
 `GuessingPolicyProbe.b_two,
 `GuessingPolicyProbe.ga_two,
 `GuessingPolicyProbe.gb_two,
 `GuessingPolicyProbe.a_three,
 `GuessingPolicyProbe.b_three,
 `GuessingPolicyProbe.ga_three,
 `GuessingPolicyProbe.gb_three,
 `GuessingPolicyProbe.a_four,
 `GuessingPolicyProbe.b_four,
 `GuessingPolicyProbe.history_changes_kink_choice,
 `GuessingPolicyProbe.a_real_regret,
 `GuessingPolicyProbe.b_real_regret,
 `GuessingPolicyProbe.a_energy,
 `GuessingPolicyProbe.positive_terminal,
 `GuessingPolicyProbe.a_actual_fixed,
 `GuessingPolicyProbe.fixed_rhs_is_one,
 `GuessingPolicyProbe.a_selected_bound,
 `GuessingPolicyProbe.a_tuned_all_comparators,
 `GuessingPolicyProbe.not_global_oracle,
 `GuessingPolicyProbe.invalid_future_causal,
 `GuessingPolicyProbe.zero_rate_infeasible_initial,
 `GuessingPolicyProbe.a_horizon_family_average,
 `GuessingPolicyProbe.policy,
 `GuessingPolicyProbe.labelsA,
 `GuessingPolicyProbe.labelsB,
 `GuessingPolicyProbe.eta,
 `GuessingPolicyProbe.futureLabels,
 `GuessingPolicyProbe.futureEta,
 `GuessingPolicyProbe.V,
 `GuessingPolicyProbe.a,
 `GuessingPolicyProbe.b,
 `GuessingPolicyProbe.ga,
 `GuessingPolicyProbe.gb]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingSubgradientPolicyCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingSubgradientPolicyCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Current new4 public proof bodies and whole actual guessing-history canary; compiled Test module environment, direct type/value occurrences only; not full registry or combined-root gate")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
