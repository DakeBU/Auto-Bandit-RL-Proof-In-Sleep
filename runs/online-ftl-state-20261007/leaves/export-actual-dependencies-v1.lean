import Tests.OnlineLearningFTLStateCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.empiricalMean_decomposition,
`BanditRL.OnlineLearning.empiricalMean_minimizes,
`BanditRL.OnlineLearning.empiricalMean_mem,
`BanditRL.OnlineLearning.empiricalMean_unique,
`BanditRL.OnlineLearning.empiricalMean_succ,
`BanditRL.OnlineLearning.ftlPredict_prefix,
`BanditRL.OnlineLearning.ftlPredict_mem,
`BanditRL.OnlineLearning.ftlPredict_half,
`BanditRL.OnlineLearning.ftlState_first,
`BanditRL.OnlineLearning.ftlState_eq_predict,
`BanditRL.OnlineLearning.ftlState_prefix,
`BanditRL.OnlineLearning.ftlState_mem,
`BanditRL.OnlineLearning.ftlState_half,
`FTLStateProbe.initial_and_first,
`FTLStateProbe.varying_updates,
`FTLStateProbe.current_target_after_prediction,
`FTLStateProbe.feasibility_and_outside,
`FTLStateProbe.half_state_regret,
`FTLStateProbe.general_initial_not_quarter,
`BanditRL.OnlineLearning.empiricalMean,
`BanditRL.OnlineLearning.ftlPredict,
`BanditRL.OnlineLearning.ftlMeanStep,
`BanditRL.OnlineLearning.ftlState,
`FTLStateProbe.probeTargets]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineLearningFTLStateCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineLearningFTLStateCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Existing4Meanproof1def plus actual9newpublicproof3defs and6namedvalidationproof1testdef. Selected24 compiled nodes with direct type/VALUE constant occurrences; not whole registry, source inventory or teaching graph.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
