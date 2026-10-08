import Tests.OnlineGuessingRandomizedIIDCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.independent_private_seed_pair,
`BanditRL.OnlineLearning.private_seed_past_independent,
`BanditRL.OnlineLearning.privateSeedPastInformation_monotone,
`BanditRL.OnlineLearning.predictable_private_seed_independent,
`BanditRL.OnlineLearning.randomized_history_policy_independent,
`BanditRL.OnlineLearning.predictable_private_seed_expectedFixed_excess,
`BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess,
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
`Tests.OnlineGuessingRandomizedIID.seedBit_measurable,
`Tests.OnlineGuessingRandomizedIID.seedBit_feasible,
`Tests.OnlineGuessingRandomizedIID.seededPolicy_measurable,
`Tests.OnlineGuessingRandomizedIID.seededPolicy_legal,
`Tests.OnlineGuessingRandomizedIID.policy_not_off_cube_bounded,
`Tests.OnlineGuessingRandomizedIID.actual_information_monotone,
`Tests.OnlineGuessingRandomizedIID.actual_seed_history_independent,
`Tests.OnlineGuessingRandomizedIID.actual_policy_current_independent,
`Tests.OnlineGuessingRandomizedIID.actual_randomized_excess_nonnegative,
`Tests.OnlineGuessingRandomizedIID.actual_general_information_excess_nonnegative,
`Tests.OnlineGuessingRandomizedIID.actual_empty_excess,
`Tests.OnlineGuessingRandomizedIID.actual_two_round_excess,
`Tests.OnlineGuessingRandomizedIID.current_target_not_private_information,
`Tests.OnlineGuessingRandomizedIID.xor_targets_independent,
`Tests.OnlineGuessingRandomizedIID.xor_tape_individually_independent_X,
`Tests.OnlineGuessingRandomizedIID.xor_tape_individually_independent_Y,
`Tests.OnlineGuessingRandomizedIID.xor_seed_past_not_independent_current,
`Tests.OnlineGuessingRandomizedIID.xor_seed_not_independent_whole_pair,
`Tests.OnlineGuessingRandomizedIID.pairwise_seed_independence_is_insufficient,
`BanditRL.OnlineLearning.privateSeedPastInformation,
`Tests.OnlineGuessingRandomizedIID.seededLaw,
`Tests.OnlineGuessingRandomizedIID.seed,
`Tests.OnlineGuessingRandomizedIID.target,
`Tests.OnlineGuessingRandomizedIID.seedBit,
`Tests.OnlineGuessingRandomizedIID.seededPolicy,
`Tests.OnlineGuessingRandomizedIID.fourLaw,
`Tests.OnlineGuessingRandomizedIID.xorX,
`Tests.OnlineGuessingRandomizedIID.xorY,
`Tests.OnlineGuessingRandomizedIID.xorTape,
`Tests.OnlineGuessingRandomizedIID.seededLaw_probability,
`Tests.OnlineGuessingRandomizedIID.fourLaw_probability,
`BanditRL.OnlineLearning.expectedFixedMinimum,
`BanditRL.OnlineLearning.expectedFixedRegret,
`BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance,
`BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition,
`BanditRL.OnlineLearning.independent_prediction_square]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingRandomizedIIDCanary }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  let anonymous := env.constants.toList.toArray.filterMap fun (n, _) =>
    if n.toString.startsWith "Tests.OnlineGuessingRandomizedIID.instMeasurable" &&
        moduleName env n == "Tests.OnlineGuessingRandomizedIIDCanary" then some n else none
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingRandomizedIIDCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Seven frozen public producer/interface proofs, actual named private-seed/infinite-IID/XOR canaries, complete information/fixture definitions, named probability instances and actual anonymous measurable instances, plus five shared reused nodes. Actual direct TYPE/VALUE occurrences, not source coverage or a whole registry.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
