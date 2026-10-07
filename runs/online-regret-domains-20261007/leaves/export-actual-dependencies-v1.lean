import Tests.OnlineLearningRegretDomainsCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.comparatorRegret_eq_sum,
`BanditRL.OnlineLearning.noRegret_of_vanishing_bound,
`RegretDomainsProbe.domain_gap_sum,
`RegretDomainsProbe.restriction_commutes,
`RegretDomainsProbe.proper_inclusion,
`RegretDomainsProbe.loss_prefix,
`RegretDomainsProbe.zero_horizon,
`RegretDomainsProbe.outside_prediction_and_negative_regret,
`RegretDomainsProbe.same_prediction_two_comparators,
`RegretDomainsProbe.negative_game_noRegret,
`BanditRL.OnlineLearning.comparatorRegret,
`BanditRL.OnlineLearning.NoRegret,
`RegretDomainsProbe.embed,
`RegretDomainsProbe.sourceV,
`RegretDomainsProbe.outputW,
`RegretDomainsProbe.domainLoss,
`RegretDomainsProbe.output,
`RegretDomainsProbe.referenceOne,
`RegretDomainsProbe.referenceZero,
`RegretDomainsProbe.liftedComparators]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineLearningRegretDomainsCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineLearningRegretDomainsCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Existing2shared Regret proofs/2definitions plus8named validation proofs/8fixturedefinitions. Selected20compiled nodes with direct type/VALUE references; zero new production nodes; not the full shared registry or source inventory.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
