import Tests.OnlineGuessingIIDSuccessCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.centered_total_sublinear_iff_average,
`BanditRL.OnlineLearning.randomized_history_policy_success_iff,
`BanditRL.OnlineLearning.meanPredict_expectedFixed_upper,
`BanditRL.OnlineLearning.meanPredict_iid_success,
`Tests.OnlineGuessingIIDSuccess.actual_meanPredict_success,
`Tests.OnlineGuessingIIDSuccess.actual_meanPredict_upper,
`Tests.OnlineGuessingIIDSuccess.actual_meanPredict_two_round_positive,
`Tests.OnlineGuessingIIDSuccess.actual_positive_variance,
`Tests.OnlineGuessingIIDSuccess.persistentPolicy,
`Tests.OnlineGuessingIIDSuccess.persistentPolicy_measurable,
`Tests.OnlineGuessingIIDSuccess.persistentPolicy_legal,
`Tests.OnlineGuessingIIDSuccess.persistentPrediction,
`Tests.OnlineGuessingIIDSuccess.persistent_excess,
`Tests.OnlineGuessingIIDSuccess.persistent_normalized_limit,
`Tests.OnlineGuessingIIDSuccess.persistent_not_sublinear,
`Tests.OnlineGuessingIIDSuccess.persistent_policy_not_successful,
`Tests.OnlineGuessingIIDSuccess.zero_horizon_difference,
`Tests.OnlineGuessingIIDSuccess.nonzero_initial_total_sublinear,
`Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_upper,
`Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_negative_two,
`BanditRL.OnlineLearning.expectedFixedMinimum,
`BanditRL.OnlineLearning.expectedFixedRegret,
`BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance,
`BanditRL.OnlineLearning.expected_fixed_prefix_decomposition,
`BanditRL.OnlineLearning.meanPredict_expectedFixed_excess,
`BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess,
`BanditRL.OnlineLearning.theorem_1_3,
`BanditRL.OnlineLearning.empiricalMean_minimizes,
`BanditRL.OnlineLearning.meanPredict,
`BanditRL.OnlineLearning.empiricalMean,
`Tests.OnlineGuessingIIDBenchmark.coinLaw,
`Tests.OnlineGuessingIIDBenchmark.iidLaw,
`Tests.OnlineGuessingIIDBenchmark.observation,
`Tests.OnlineGuessingIIDBenchmark.iidLaw_probability,
`Tests.OnlineGuessingIIDBenchmark.observation_independent,
`Tests.OnlineGuessingIIDBenchmark.observation_support,
`Tests.OnlineGuessingIIDBenchmark.observation_sameLaw,
`Tests.OnlineGuessingIIDBenchmark.meanPredict_two_round_excess,
`Tests.OnlineGuessingRandomizedIID.seededLaw,
`Tests.OnlineGuessingRandomizedIID.seed,
`Tests.OnlineGuessingRandomizedIID.target,
`Tests.OnlineGuessingRandomizedIID.seedBit,
`Tests.OnlineGuessingRandomizedIID.seededLaw_probability,
`Tests.OnlineGuessingRandomizedIID.seed_independent_whole_process,
`Tests.OnlineGuessingRandomizedIID.target_independent]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingIIDSuccessCanary }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  let anonymous := env.constants.toList.toArray.filterMap fun (n, _) =>
    if n.toString.startsWith "Tests.OnlineGuessingIIDSuccess.instMeasurable" &&
        moduleName env n == "Tests.OnlineGuessingIIDSuccessCanary" then some n else none
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingIIDSuccessCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Four frozen public proof values;14 actual canary proofs/2 fixturedefinitions; actual reused infinite-IID/private-tape laws and independence/probability declarations. Direct TYPE/VALUE occurrences only, not source coverage.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
