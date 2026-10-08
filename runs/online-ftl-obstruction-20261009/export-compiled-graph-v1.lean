import Tests.OnlineFTLOscillationCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.meanPredict_limitNoRegret_iff_mean_converges,
`BanditRL.OnlineLearning.dyadicObservation_unit,
`BanditRL.OnlineLearning.dyadic_empiricalMean_subsequences,
`BanditRL.OnlineLearning.dyadic_meanPredict_obstruction,
`Tests.OnlineFTLOscillation.dyadic_unit_and_prefix,
`Tests.OnlineFTLOscillation.actual_causal_predictions,
`Tests.OnlineFTLOscillation.actual_signed_regrets,
`Tests.OnlineFTLOscillation.all_comparator_iff_instantiated,
`Tests.OnlineFTLOscillation.no_feasible_mean_limit,
`Tests.OnlineFTLOscillation.two_actual_mean_subsequences,
`Tests.OnlineFTLOscillation.obstruction_instantiated,
`Tests.OnlineFTLOscillation.upper_noRegret_on_actual_stream,
`Tests.OnlineFTLOscillation.actual_best_average_zero,
`Tests.OnlineFTLOscillation.fixed_zero_has_no_ordinary_limit,
`Tests.OnlineFTLOscillation.literal_limit_noRegret_fails,
`BanditRL.OnlineLearning.empiricalMean,
`BanditRL.OnlineLearning.meanPredict,
`BanditRL.OnlineLearning.dyadicObservation,
`BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff,
`BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges,
`BanditRL.OnlineLearning.meanPredict_noRegret,
`BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero,
`BanditRL.OnlineLearning.empiricalMean_mem,
`BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineFTLOscillationCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineFTLOscillationCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "coalesced-direct-TYPE_VALUE-constant-presence-not-occurrence-count"),
      ("scope", toJson "Four frozen actual FTL obstruction/iff bodies, eleven dyadic public canaries and exact parents. Selected direct coalesced TYPE_VALUE constants only; not full transitive graph or source/chapter coverage.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
