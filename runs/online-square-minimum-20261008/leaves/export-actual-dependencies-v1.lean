import Tests.OnlineSquareMinimumCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.guessing_prefix_minimum,
`BanditRL.OnlineLearning.squaredLoss_minimum_eq,
`BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret,
`BanditRL.OnlineLearning.comparatorRegret_le_squaredBestRegret,
`BanditRL.OnlineLearning.meanPredict_bestRegret_bound,
`BanditRL.OnlineLearning.meanPredict_bestRegret_refined,
`Tests.OnlineSquareMinimum.alternating_mem,
`Tests.OnlineSquareMinimum.quarters_mem,
`Tests.OnlineSquareMinimum.empty_minimum,
`Tests.OnlineSquareMinimum.empty_regret,
`Tests.OnlineSquareMinimum.alternating_mean,
`Tests.OnlineSquareMinimum.alternating_minimum,
`Tests.OnlineSquareMinimum.alternating_unique,
`Tests.OnlineSquareMinimum.actual_prediction_values,
`Tests.OnlineSquareMinimum.actual_regret_one,
`Tests.OnlineSquareMinimum.actual_regret_two,
`Tests.OnlineSquareMinimum.signed_alternating,
`Tests.OnlineSquareMinimum.comparator_zero_order,
`Tests.OnlineSquareMinimum.comparator_one_order,
`Tests.OnlineSquareMinimum.quarters_mean,
`Tests.OnlineSquareMinimum.quarters_minimum,
`Tests.OnlineSquareMinimum.actual_bound,
`Tests.OnlineSquareMinimum.actual_refined,
`Tests.OnlineSquareMinimum.actual_refined_one,
`Tests.OnlineSquareMinimum.actual_causality,
`Tests.OnlineSquareMinimum.actual_identity,
`BanditRL.OnlineLearning.empiricalMean_mem,
`BanditRL.OnlineLearning.empiricalMean_minimizes,
`BanditRL.OnlineLearning.empiricalMean_unique,
`BanditRL.OnlineLearning.theorem_1_3,
`BanditRL.OnlineLearning.meanPredict_regret_refined,
`BanditRL.OnlineLearning.meanPredict_prefix,
`BanditRL.OnlineLearning.squaredBestRegret,
`BanditRL.OnlineLearning.empiricalMean,
`BanditRL.OnlineLearning.meanPredict,
`BanditRL.OnlineLearning.comparatorRegret,
`Tests.OnlineSquareMinimum.alternating,
`Tests.OnlineSquareMinimum.quarters]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineSquareMinimumCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineSquareMinimumCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Six new square-minimum proofs, six actually reused mean/FTL/causality proofs, four complete scoped definitions, twenty named canaries and two time-only fixtures. Selected38 compiled nodes; direct TYPE and VALUE constant occurrences, not a source inventory or full shared registry.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
