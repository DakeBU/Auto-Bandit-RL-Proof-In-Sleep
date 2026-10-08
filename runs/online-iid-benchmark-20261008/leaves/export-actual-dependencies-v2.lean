import Tests.OnlineGuessingIIDBenchmarkCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.expected_fixed_prefix_decomposition,
`BanditRL.OnlineLearning.expected_fixed_prefix_minimum,
`BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance,
`BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition,
`BanditRL.OnlineLearning.history_policy_expectedFixed_excess,
`BanditRL.OnlineLearning.meanPredict_expectedFixed_excess,
`BanditRL.OnlineLearning.constant_mean_expectedFixed_excess_zero,
`BanditRL.OnlineLearning.history_policy_normalized_expectedFixed_excess,
`Tests.OnlineGuessingIIDBenchmark.coinLaw_support,
`Tests.OnlineGuessingIIDBenchmark.coinLaw_integral,
`Tests.OnlineGuessingIIDBenchmark.observation_measurable,
`Tests.OnlineGuessingIIDBenchmark.observation_has_coinLaw,
`Tests.OnlineGuessingIIDBenchmark.observation_sameLaw,
`Tests.OnlineGuessingIIDBenchmark.observation_support,
`Tests.OnlineGuessingIIDBenchmark.observation_independent,
`Tests.OnlineGuessingIIDBenchmark.observation_mean,
`Tests.OnlineGuessingIIDBenchmark.observation_variance,
`Tests.OnlineGuessingIIDBenchmark.support_is_not_pointwise,
`Tests.OnlineGuessingIIDBenchmark.empty_minimum,
`Tests.OnlineGuessingIIDBenchmark.two_round_fixed_minimum,
`Tests.OnlineGuessingIIDBenchmark.actual_mean_attainment,
`Tests.OnlineGuessingIIDBenchmark.actual_meanPredict_nonnegative,
`Tests.OnlineGuessingIIDBenchmark.meanPredict_two_round_excess,
`Tests.OnlineGuessingIIDBenchmark.constant_known_mean_zero,
`Tests.OnlineGuessingIIDBenchmark.lastPolicy_measurable,
`Tests.OnlineGuessingIIDBenchmark.lastPolicy_legal,
`Tests.OnlineGuessingIIDBenchmark.lastPolicy_not_globally_bounded,
`Tests.OnlineGuessingIIDBenchmark.actual_history_independent,
`Tests.OnlineGuessingIIDBenchmark.actual_history_nonnegative,
`Tests.OnlineGuessingIIDBenchmark.actual_history_normalization,
`Tests.OnlineGuessingIIDBenchmark.repeated_target_fixed_minimum,
`Tests.OnlineGuessingIIDBenchmark.infeasible_fixed_comparator_two,
`Tests.OnlineGuessingIIDBenchmark.independent_difference_square,
`Tests.OnlineGuessingIIDBenchmark.hindsight_minimum_two,
`Tests.OnlineGuessingIIDBenchmark.min_and_expectation_do_not_commute,
`Tests.OnlineGuessingIIDBenchmark.current_target_cheating_negative,
`BanditRL.OnlineLearning.expected_square_decomposition,
`BanditRL.OnlineLearning.independent_prediction_square,
`BanditRL.OnlineLearning.history_policy_independent,
`BanditRL.OnlineLearning.meanPredict_independent,
`BanditRL.OnlineLearning.meanPredict_measurable,
`BanditRL.OnlineLearning.meanPredict_mem,
`BanditRL.OnlineLearning.expectedFixedMinimum,
`BanditRL.OnlineLearning.expectedFixedRegret,
`BanditRL.OnlineLearning.empiricalMean,
`BanditRL.OnlineLearning.meanPredict,
`Tests.OnlineGuessingIIDBenchmark.coinLaw,
`Tests.OnlineGuessingIIDBenchmark.iidLaw,
`Tests.OnlineGuessingIIDBenchmark.observation,
`Tests.OnlineGuessingIIDBenchmark.lastPolicy,
`Tests.OnlineGuessingIIDBenchmark.hindsightMinimum,
`Tests.OnlineGuessingIIDBenchmark.coinLaw_probability,
`Tests.OnlineGuessingIIDBenchmark.iidLaw_probability]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingIIDBenchmarkCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingIIDBenchmarkCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Eight frozen expected-fixed/causal IID proofs, six actual reused proofs, four complete scoped definitions, twenty-eight named canary proofs, five complete real-coordinate IID/history/hindsight fixture definitions, two actual probability instances. Selected53 compiled nodes; direct TYPE/VALUE occurrences, not source coverage or full shared registry.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
