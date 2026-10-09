import BanditRLProof
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.GuessingLower.binaryStream,
`BanditRL.OnlineLearning.GuessingLower.binaryValues,
`BanditRL.OnlineLearning.GuessingLower.causalPredict,
`BanditRL.OnlineLearning.GuessingLower.pathRegret,
`BanditRL.OnlineLearning.GuessingLower.randomized_log_lower,
`BanditRL.OnlineLearning.KernelDecisionHistory,
`BanditRL.OnlineLearning.KernelDecisionSampler,
`BanditRL.OnlineLearning.LimitNoRegret,
`BanditRL.OnlineLearning.NoRegret,
`BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess,
`BanditRL.OnlineLearning.causal_kernel_realization_and_expectedFixed_excess,
`BanditRL.OnlineLearning.centered_total_sublinear_iff_average,
`BanditRL.OnlineLearning.comparatorRegret,
`BanditRL.OnlineLearning.comparatorRegret_eq_sum,
`BanditRL.OnlineLearning.comparatorRegret_le_squaredBestRegret,
`BanditRL.OnlineLearning.completed_predictable_private_seed_expectedFixed_excess,
`BanditRL.OnlineLearning.completed_predictable_private_seed_independent,
`BanditRL.OnlineLearning.constant_mean_expectedFixed_excess_zero,
`BanditRL.OnlineLearning.dyadicObservation,
`BanditRL.OnlineLearning.dyadic_meanPredict_obstruction,
`BanditRL.OnlineLearning.empiricalMean,
`BanditRL.OnlineLearning.empiricalMean_decomposition,
`BanditRL.OnlineLearning.empiricalMean_mem,
`BanditRL.OnlineLearning.empiricalMean_minimizes,
`BanditRL.OnlineLearning.empiricalMean_unique,
`BanditRL.OnlineLearning.empiricalMean_update,
`BanditRL.OnlineLearning.expectedFixedMinimum,
`BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance,
`BanditRL.OnlineLearning.expectedFixedRegret,
`BanditRL.OnlineLearning.expected_fixed_prefix_decomposition,
`BanditRL.OnlineLearning.expected_fixed_prefix_minimum,
`BanditRL.OnlineLearning.ftlMeanStep,
`BanditRL.OnlineLearning.ftlPredict,
`BanditRL.OnlineLearning.ftlPredict_half,
`BanditRL.OnlineLearning.ftlPredict_mem,
`BanditRL.OnlineLearning.ftlPredict_prefix,
`BanditRL.OnlineLearning.ftlState,
`BanditRL.OnlineLearning.ftlState_eq_predict,
`BanditRL.OnlineLearning.ftlState_first,
`BanditRL.OnlineLearning.ftlState_half,
`BanditRL.OnlineLearning.ftlState_mem,
`BanditRL.OnlineLearning.ftlState_prefix,
`BanditRL.OnlineLearning.guessing_prefix_minimum,
`BanditRL.OnlineLearning.history_policy_normalized_expectedFixed_excess,
`BanditRL.OnlineLearning.kernelCausalPolicy,
`BanditRL.OnlineLearning.kernelGeneratedActions,
`BanditRL.OnlineLearning.kernelGeneratedHistory,
`BanditRL.OnlineLearning.kernelGeneratedPrediction,
`BanditRL.OnlineLearning.lemma_1_2,
`BanditRL.OnlineLearning.limitNoRegret_iff_noRegret_of_converges,
`BanditRL.OnlineLearning.limitNoRegret_implies_noRegret,
`BanditRL.OnlineLearning.meanPredict,
`BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero,
`BanditRL.OnlineLearning.meanPredict_bestRegret_bound,
`BanditRL.OnlineLearning.meanPredict_bestRegret_refined,
`BanditRL.OnlineLearning.meanPredict_iid_success,
`BanditRL.OnlineLearning.meanPredict_initial_stability,
`BanditRL.OnlineLearning.meanPredict_limitNoRegret_iff_mean_converges,
`BanditRL.OnlineLearning.meanPredict_mem,
`BanditRL.OnlineLearning.meanPredict_noRegret,
`BanditRL.OnlineLearning.meanPredict_prefix,
`BanditRL.OnlineLearning.meanPredict_regret_refined,
`BanditRL.OnlineLearning.meanPredict_stability,
`BanditRL.OnlineLearning.normalized_excess,
`BanditRL.OnlineLearning.privateSeedPastInformation,
`BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess,
`BanditRL.OnlineLearning.randomized_history_policy_independent,
`BanditRL.OnlineLearning.randomized_history_policy_success_iff,
`BanditRL.OnlineLearning.squaredBestRegret,
`BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret,
`BanditRL.OnlineLearning.squaredLoss_minimum_eq,
`BanditRL.OnlineLearning.theorem_1_3,
`harmonic_le_one_add_log]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "BanditRLProof"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "coalesced-direct-TYPE_VALUE-constant-presence-not-occurrence-count"),
      ("scope", toJson "Fifty exact reused public Chapter1 proof targets plus selected support definitions. Compiled current readiness only, not source/chapter acceptance. Selected coalesced direct TYPE_VALUE constant presence, not full transitive proof graph or new theorem count.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
