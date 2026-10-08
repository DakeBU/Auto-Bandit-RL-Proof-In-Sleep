import Tests.OnlineGuessingAECausalCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.ae_predictable_exists_bounded_history_policy,
`BanditRL.OnlineLearning.ae_predictable_private_seed_independent,
`BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess,
`Tests.OnlineGuessingAECausal.badPrediction,
`Tests.OnlineGuessingAECausal.bad_eq_causal_ae,
`Tests.OnlineGuessingAECausal.causal_version_measurable,
`Tests.OnlineGuessingAECausal.bad_ae_predictable,
`Tests.OnlineGuessingAECausal.bad_ae_unit,
`Tests.OnlineGuessingAECausal.bad_is_not_pointwise_predictable,
`Tests.OnlineGuessingAECausal.bad_is_not_everywhere_unit,
`Tests.OnlineGuessingAECausal.actual_all_time_bounded_policy,
`Tests.OnlineGuessingAECausal.actual_current_independence,
`Tests.OnlineGuessingAECausal.actual_original_excess_identity,
`Tests.OnlineGuessingAECausal.actual_mean_square,
`Tests.OnlineGuessingAECausal.actual_nonzero_excess,
`Tests.OnlineGuessingAECausal.actual_two_round_excess,
`Tests.OnlineGuessingAECausal.actual_empty_excess,
`Tests.OnlineGuessingAECausal.actual_positive_target_variance,
`BanditRL.OnlineLearning.privateSeedPastInformation,
`BanditRL.OnlineLearning.private_seed_past_independent,
`BanditRL.OnlineLearning.predictable_private_seed_independent,
`BanditRL.OnlineLearning.expectedFixedMinimum,
`BanditRL.OnlineLearning.expectedFixedRegret,
`BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance,
`BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition,
`Tests.OnlineGuessingRandomizedIID.seededLaw,
`Tests.OnlineGuessingRandomizedIID.seed,
`Tests.OnlineGuessingRandomizedIID.target,
`Tests.OnlineGuessingRandomizedIID.seededLaw_probability,
`Tests.OnlineGuessingRandomizedIID.seed_measurable,
`Tests.OnlineGuessingRandomizedIID.target_measurable,
`Tests.OnlineGuessingRandomizedIID.seed_has_coinLaw,
`Tests.OnlineGuessingRandomizedIID.target_has_coinLaw,
`Tests.OnlineGuessingRandomizedIID.target_sameLaw,
`Tests.OnlineGuessingRandomizedIID.target_support,
`Tests.OnlineGuessingRandomizedIID.target_independent,
`Tests.OnlineGuessingRandomizedIID.seed_independent_whole_process,
`Tests.OnlineGuessingRandomizedIID.target_mean,
`Tests.OnlineGuessingRandomizedIID.target_variance]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingAECausalCanary }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  let anonymous := env.constants.toList.toArray.filterMap fun (n, _) =>
    if n.toString.startsWith "Tests.OnlineGuessingAECausal.instMeasurable" &&
        moduleName env n == "Tests.OnlineGuessingAECausalCanary" then some n else none
  for n in targets ++ anonymous do
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingAECausalCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Three exact AE causal public proof bodies, actual AE-only non-pointwise canaries and reused independent private seed/infinite IID laws. Direct TYPE/VALUE constants only, not chapter/source coverage.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
