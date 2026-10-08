import Tests.OnlineLearningCoreAuditCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.lemma_1_2,
`BanditRL.OnlineLearning.expected_square_decomposition,
`BanditRL.OnlineLearning.independent_prediction_square,
`BanditRL.OnlineLearning.meanPredict_independent,
`BanditRL.OnlineLearning.meanPredict_measurable,
`BanditRL.OnlineLearning.meanPredict_memLp,
`BanditRL.OnlineLearning.iid_meanPredict_excess,
`BanditRL.OnlineLearning.iid_meanPredict_excess_nonneg,
`BanditRL.OnlineLearning.source_mean_optimal,
`BanditRL.OnlineLearning.history_policy_independent,
`BanditRL.OnlineLearning.history_policy_loss_ge_variance,
`BanditRL.OnlineLearning.normalized_excess,
`Tests.OnlineLearningCoreAudit.clip,
`Tests.OnlineLearningCoreAudit.clip_measurable,
`Tests.OnlineLearningCoreAudit.clip_unit,
`Tests.OnlineLearningCoreAudit.clip_fixed,
`Tests.OnlineLearningCoreAudit.boundedObservation,
`Tests.OnlineLearningCoreAudit.bounded_measurable,
`Tests.OnlineLearningCoreAudit.bounded_support,
`Tests.OnlineLearningCoreAudit.bounded_eq_original_ae,
`Tests.OnlineLearningCoreAudit.clipping_is_not_pointwise_identity,
`Tests.OnlineLearningCoreAudit.bounded_independent,
`Tests.OnlineLearningCoreAudit.bounded_sameLaw,
`Tests.OnlineLearningCoreAudit.bounded_mean,
`Tests.OnlineLearningCoreAudit.bounded_variance,
`Tests.OnlineLearningCoreAudit.bounded_memLp,
`Tests.OnlineLearningCoreAudit.outside_comparator_loss,
`Tests.OnlineLearningCoreAudit.independent_coordinate_loss,
`Tests.OnlineLearningCoreAudit.actual_mean_independent,
`Tests.OnlineLearningCoreAudit.actual_mean_measurable,
`Tests.OnlineLearningCoreAudit.actual_mean_memLp,
`Tests.OnlineLearningCoreAudit.actual_mean_excess_identity,
`Tests.OnlineLearningCoreAudit.actual_mean_excess_nonnegative,
`Tests.OnlineLearningCoreAudit.actual_mean_two_round_excess,
`Tests.OnlineLearningCoreAudit.actual_mean_optimal,
`Tests.OnlineLearningCoreAudit.boundedLast,
`Tests.OnlineLearningCoreAudit.boundedLast_measurable,
`Tests.OnlineLearningCoreAudit.boundedLast_unit,
`Tests.OnlineLearningCoreAudit.boundedLast_legal_identity,
`Tests.OnlineLearningCoreAudit.actual_history_independent,
`Tests.OnlineLearningCoreAudit.actual_history_lower,
`Tests.OnlineLearningCoreAudit.actual_history_one_loss,
`Tests.OnlineLearningCoreAudit.heterogeneous,
`Tests.OnlineLearningCoreAudit.heterogeneous_measurable,
`Tests.OnlineLearningCoreAudit.heterogeneous_unit,
`Tests.OnlineLearningCoreAudit.heterogeneous_independent,
`Tests.OnlineLearningCoreAudit.heterogeneous_not_sameLaw,
`Tests.OnlineLearningCoreAudit.nonidentical_current_variance_lower,
`Tests.OnlineLearningCoreAudit.positive_scalar_normalization,
`Tests.OnlineLearningCoreAudit.zero_horizon_discrepancy,
`FoundationsProbe.prefix_minimizers,
`FoundationsProbe.instantiated_compare,
`FoundationsProbe.strict_values,
`FoundationsProbe.zero_horizon,
`FoundationsProbe.one_horizon,
`FoundationsProbe.without_optimality,
`FoundationsProbe.without_feasibility,
`Tests.OnlineGuessingIIDBenchmark.coinLaw,
`Tests.OnlineGuessingIIDBenchmark.iidLaw,
`Tests.OnlineGuessingIIDBenchmark.observation,
`Tests.OnlineGuessingIIDBenchmark.iidLaw_probability,
`Tests.OnlineGuessingIIDBenchmark.observation_independent,
`Tests.OnlineGuessingIIDBenchmark.observation_support,
`Tests.OnlineGuessingIIDBenchmark.observation_sameLaw,
`Tests.OnlineGuessingIIDBenchmark.observation_mean,
`Tests.OnlineGuessingIIDBenchmark.observation_variance,
`Tests.OnlineGuessingIIDBenchmark.support_is_not_pointwise,
`Tests.OnlineGuessingIIDBenchmark.lastPolicy_not_globally_bounded,
`BanditRL.OnlineLearning.meanPredict,
`BanditRL.OnlineLearning.empiricalMean]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineLearningCoreAuditCanary }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  let anonymous := env.constants.toList.toArray.filterMap fun (n, _) =>
    if n.toString.startsWith "Tests.OnlineLearningCoreAudit.instMeasurable" &&
        moduleName env n == "Tests.OnlineLearningCoreAuditCanary" then some n else none
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineLearningCoreAuditCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Twelve unchanged old public proof values, original seven Foundations canaries and actual clipped infinite-IID/current-variance canaries. Direct TYPE/VALUE constant occurrences only; five source audits, no new production proofs or whole-source coverage.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
