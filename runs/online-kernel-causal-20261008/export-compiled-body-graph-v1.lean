import Tests.OnlineGuessingKernelCausalCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.kernel_sampler_family_exists,
`BanditRL.OnlineLearning.kernel_sampler_causal_process,
`BanditRL.OnlineLearning.kernel_sampler_joint_law,
`BanditRL.OnlineLearning.kernel_sampler_conditional_law,
`BanditRL.OnlineLearning.causal_kernel_realization_and_expectedFixed_excess,
`Tests.OnlineGuessingKernelCausal.switchSet_measurable,
`Tests.OnlineGuessingKernelCausal.public_family_realizes,
`Tests.OnlineGuessingKernelCausal.public_causal_process,
`Tests.OnlineGuessingKernelCausal.public_joint_law,
`Tests.OnlineGuessingKernelCausal.public_conditional_law,
`Tests.OnlineGuessingKernelCausal.actual_process_excess,
`Tests.OnlineGuessingKernelCausal.history_feedback_distribution,
`Tests.OnlineGuessingKernelCausal.every_history_stochastic,
`Tests.OnlineGuessingKernelCausal.actual_prediction_binary,
`Tests.OnlineGuessingKernelCausal.target_positive_variance,
`Tests.OnlineGuessingKernelCausal.every_horizon_excess,
`Tests.OnlineGuessingKernelCausal.zero_horizon_excess,
`Tests.OnlineGuessingKernelCausal.positive_two_round_excess,
`BanditRL.OnlineLearning.KernelDecisionHistory,
`BanditRL.OnlineLearning.KernelDecisionSampler,
`BanditRL.OnlineLearning.kernelGeneratedActions,
`BanditRL.OnlineLearning.kernelCausalPolicy,
`BanditRL.OnlineLearning.kernelGeneratedHistory,
`BanditRL.OnlineLearning.kernelGeneratedPrediction,
`BanditRL.OnlineLearning.kernelUniformTapeLaw,
`BanditRL.OnlineLearning.kernelGameLaw,
`Tests.OnlineGuessingKernelCausal.lowLaw,
`Tests.OnlineGuessingKernelCausal.highLaw,
`Tests.OnlineGuessingKernelCausal.lowLaw_probability,
`Tests.OnlineGuessingKernelCausal.highLaw_probability,
`Tests.OnlineGuessingKernelCausal.switchSet,
`Tests.OnlineGuessingKernelCausal.decisionKernel,
`Tests.OnlineGuessingKernelCausal.decisionKernel_markov,
`Tests.OnlineGuessingKernelCausal.oneHistory,
`Tests.OnlineGuessingKernelCausal.selectedSampler,
`Tests.OnlineGuessingKernelCausal.observationLaw,
`Tests.OnlineGuessingKernelCausal.prediction,
`Tests.OnlineGuessingKernelCausal.target,
`Tests.OnlineGuessingKernelCausal.gameLaw,
`BanditRL.OnlineLearning.independent_private_seed_pair,
`BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess,
`BanditRL.OnlineLearning.expectedFixedMinimum,
`BanditRL.OnlineLearning.expectedFixedRegret,
`BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance,
`BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition,
`ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval,
`ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd,
`ProbabilityTheory.iIndepFun_infinitePi,
`ProbabilityTheory.indepFun_prod,
`ProbabilityTheory.iIndepFun.indepFun_finset,
`MeasureTheory.Measure.infinitePi_map_eval,
`MeasureTheory.Measure.compProd_apply]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingKernelCausalCanary }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  let anonymous := env.constants.toList.toArray.filterMap fun (n, _) =>
    if n.toString.startsWith "Tests.OnlineGuessingKernelCausal.instMeasurable" &&
        moduleName env n == "Tests.OnlineGuessingKernelCausalCanary" then some n else none
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingKernelCausalCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "coalesced-direct-TYPE_VALUE-constant-presence-not-occurrence-count"),
      ("scope", toJson "Five frozen actual causal-kernel proof bodies, stochastic history-feedback canaries and exact parents. Selected direct coalesced TYPE_VALUE constants only; not full transitive graph or source/chapter coverage.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
