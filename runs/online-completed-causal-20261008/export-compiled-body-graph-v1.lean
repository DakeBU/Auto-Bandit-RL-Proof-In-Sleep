import Tests.OnlineGuessingCompletedCausalCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.completed_measurable_real_exists_version,
`BanditRL.OnlineLearning.completed_predictable_exists_bounded_history_policy,
`BanditRL.OnlineLearning.completed_predictable_private_seed_independent,
`BanditRL.OnlineLearning.completed_predictable_private_seed_expectedFixed_excess,
`Tests.OnlineGuessingCompletedCausal.bad_completed_measurable,
`Tests.OnlineGuessingCompletedCausal.bad_completed_but_not_ordinary_at_zero,
`Tests.OnlineGuessingCompletedCausal.actual_completed_real_version,
`Tests.OnlineGuessingCompletedCausal.actual_all_time_bounded_policy,
`Tests.OnlineGuessingCompletedCausal.actual_current_independence,
`Tests.OnlineGuessingCompletedCausal.actual_original_excess_identity,
`Tests.OnlineGuessingCompletedCausal.actual_nonzero_excess,
`Tests.OnlineGuessingCompletedCausal.actual_two_round_excess,
`Tests.OnlineGuessingCompletedCausal.actual_empty_excess,
`Tests.OnlineGuessingCompletedCausal.actual_positive_target_variance,
`Tests.OnlineGuessingCompletedCausal.bad_still_not_everywhere_unit,
`BanditRL.OnlineLearning.ae_predictable_exists_bounded_history_policy,
`BanditRL.OnlineLearning.ae_predictable_private_seed_independent,
`BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess,
`BanditRL.OnlineLearning.privateSeedPastInformation,
`BanditRL.OnlineLearning.private_seed_past_independent,
`BanditRL.OnlineLearning.predictable_private_seed_independent,
`BanditRL.OnlineLearning.expectedFixedMinimum,
`BanditRL.OnlineLearning.expectedFixedRegret,
`BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance,
`BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition,
`MeasurableSpace.measurable_mapNatBool,
`MeasurableSpace.injective_mapNatBool,
`Measurable.measurableEmbedding,
`MeasurableEmbedding.measurable_invFun,
`MeasurableEmbedding.leftInverse_invFun,
`MeasureTheory.ae_all_iff,
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
`Tests.OnlineGuessingRandomizedIID.target_variance,
`Tests.OnlineGuessingAECausal.badPrediction,
`Tests.OnlineGuessingAECausal.bad_eq_causal_ae,
`Tests.OnlineGuessingAECausal.causal_version_measurable,
`Tests.OnlineGuessingAECausal.bad_ae_unit,
`Tests.OnlineGuessingAECausal.bad_is_not_pointwise_predictable,
`Tests.OnlineGuessingAECausal.bad_is_not_everywhere_unit,
`Tests.OnlineGuessingAECausal.actual_mean_square]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingCompletedCausalCanary }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  let anonymous := env.constants.toList.toArray.filterMap fun (n, _) =>
    if n.toString.startsWith "Tests.OnlineGuessingCompletedCausal.instMeasurable" &&
        moduleName env n == "Tests.OnlineGuessingCompletedCausalCanary" then some n else none
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingCompletedCausalCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "coalesced-direct-TYPE_VALUE-constant-presence-not-occurrence-count"),
      ("scope", toJson "Four exact completed-causal proof bodies, eleven genuine augmented-but-not-ordinary canaries and selected actual parents. Direct coalesced TYPE_VALUE constant presence only, not a full dependency graph or chapter/source coverage.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
