import Tests.OnlineGuessingLogLowerCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.GuessingLower.probability_mem,
`BanditRL.OnlineLearning.GuessingLower.branch_mass,
`BanditRL.OnlineLearning.GuessingLower.pathWeight_nonneg,
`BanditRL.OnlineLearning.GuessingLower.sum_vectors_succ,
`BanditRL.OnlineLearning.GuessingLower.prefix_mass_one,
`BanditRL.OnlineLearning.GuessingLower.prefix_distribution,
`BanditRL.OnlineLearning.GuessingLower.prefixMeasure_probability,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_integral,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_congr,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_const,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_add,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_sub,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_const_mul,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_div,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_succ,
`BanditRL.OnlineLearning.GuessingLower.heads_succ,
`BanditRL.OnlineLearning.GuessingLower.heads_sq_succ,
`BanditRL.OnlineLearning.GuessingLower.expected_heads,
`BanditRL.OnlineLearning.GuessingLower.expected_heads_sq,
`BanditRL.OnlineLearning.GuessingLower.expected_next_variance,
`BanditRL.OnlineLearning.GuessingLower.causalPredict_prefix,
`BanditRL.OnlineLearning.GuessingLower.binary_mean_minimizer,
`BanditRL.OnlineLearning.GuessingLower.conditional_square_lower,
`BanditRL.OnlineLearning.GuessingLower.binaryStream_cons_prefix,
`BanditRL.OnlineLearning.GuessingLower.binaryStream_cons_last,
`BanditRL.OnlineLearning.GuessingLower.binaryValues_cons_prefix,
`BanditRL.OnlineLearning.GuessingLower.causalPredict_history,
`BanditRL.OnlineLearning.GuessingLower.causalPredict_cons_last,
`BanditRL.OnlineLearning.GuessingLower.pathRegret_eq_losses,
`BanditRL.OnlineLearning.GuessingLower.pathLearnerLoss_cons,
`BanditRL.OnlineLearning.GuessingLower.binaryValues_sum,
`BanditRL.OnlineLearning.GuessingLower.binaryValues_sq,
`BanditRL.OnlineLearning.GuessingLower.pathBestLoss_count,
`BanditRL.OnlineLearning.GuessingLower.expected_pathBestLoss,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation_mono,
`BanditRL.OnlineLearning.GuessingLower.expected_pathLearnerLoss_succ,
`BanditRL.OnlineLearning.GuessingLower.expected_pathLearnerLoss_step,
`BanditRL.OnlineLearning.GuessingLower.variance_sum,
`BanditRL.OnlineLearning.GuessingLower.expected_pathLearnerLoss_lower,
`BanditRL.OnlineLearning.GuessingLower.expected_pathRegret_lower,
`BanditRL.OnlineLearning.GuessingLower.pathWeight_pos,
`BanditRL.OnlineLearning.GuessingLower.square_loss_mem,
`BanditRL.OnlineLearning.GuessingLower.square_loss_sum_mem,
`BanditRL.OnlineLearning.GuessingLower.pathRegret_abs_le,
`BanditRL.OnlineLearning.GuessingLower.pathRegret_measurable,
`BanditRL.OnlineLearning.GuessingLower.pathRegret_integrable,
`BanditRL.OnlineLearning.GuessingLower.randomized_harmonic_lower,
`BanditRL.OnlineLearning.GuessingLower.randomized_log_lower,
`GuessingLogLowerProbe.unbalanced_probability,
`GuessingLogLowerProbe.correlated_two_step_masses,
`GuessingLogLowerProbe.zero_and_two_normalization,
`GuessingLogLowerProbe.correlated_moments,
`GuessingLogLowerProbe.averaged_variance,
`GuessingLogLowerProbe.same_past_different_current,
`GuessingLogLowerProbe.actual_last_prediction,
`GuessingLogLowerProbe.nondegenerate_actual_regret,
`GuessingLogLowerProbe.actual_optimal_loss,
`GuessingLogLowerProbe.one_step_harmonic_endpoint,
`GuessingLogLowerProbe.coin_distribution,
`GuessingLogLowerProbe.seeded_policy_bounds,
`GuessingLogLowerProbe.genuine_coin_policy,
`GuessingLogLowerProbe.seeded_fixed_sequence_endpoint,
`GuessingLogLowerProbe.seeded_log_endpoint,
`GuessingLogLowerProbe.deterministic_fixed_sequence_endpoint,
`BanditRL.OnlineLearning.GuessingLower.polyaNext,
`BanditRL.OnlineLearning.GuessingLower.pathWeight,
`BanditRL.OnlineLearning.GuessingLower.binaryStream,
`BanditRL.OnlineLearning.GuessingLower.binaryValues,
`BanditRL.OnlineLearning.GuessingLower.causalPredict,
`BanditRL.OnlineLearning.GuessingLower.pathRegret,
`BanditRL.OnlineLearning.GuessingLower.pathExpectation,
`BanditRL.OnlineLearning.GuessingLower.prefixMeasure,
`BanditRL.OnlineLearning.GuessingLower.pathLearnerLoss,
`BanditRL.OnlineLearning.GuessingLower.pathBestLoss,
`GuessingLogLowerProbe.coinMeasure,
`GuessingLogLowerProbe.seededPolicy]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineGuessingLogLowerCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineGuessingLogLowerCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Actual48 public proof bodies/10 model-component definitions and16 named validation proofs/2 fixtures. Selected76 compiled nodes with direct type/VALUE references. Private decomposition and imported dependencies appear as references; not a full registry or source-inventory count.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
