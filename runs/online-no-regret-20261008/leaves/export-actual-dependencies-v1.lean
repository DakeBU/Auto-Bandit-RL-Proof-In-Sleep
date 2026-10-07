import Tests.OnlineNoRegretSemanticsCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
`BanditRL.OnlineLearning.noRegret_limit_nonpos,
`BanditRL.OnlineLearning.limitNoRegret_implies_noRegret,
`BanditRL.OnlineLearning.limitNoRegret_iff_noRegret_of_converges,
`BanditRL.OnlineLearning.NoRegretCounterexample.regret_eq,
`BanditRL.OnlineLearning.NoRegretCounterexample.noRegret,
`BanditRL.OnlineLearning.NoRegretCounterexample.normalized_even,
`BanditRL.OnlineLearning.NoRegretCounterexample.normalized_odd,
`BanditRL.OnlineLearning.NoRegretCounterexample.no_limit,
`BanditRL.OnlineLearning.NoRegretCounterexample.strict_separation,
`NoRegretSemanticsProbe.linear_regret,
`NoRegretSemanticsProbe.linear_normalized,
`NoRegretSemanticsProbe.linear_converges,
`NoRegretSemanticsProbe.linear_literal,
`NoRegretSemanticsProbe.linear_upper,
`NoRegretSemanticsProbe.negative_limit_allowed,
`NoRegretSemanticsProbe.iff_on_linear,
`NoRegretSemanticsProbe.actual_mean_upper,
`NoRegretSemanticsProbe.actual_mean_negative_T2,
`NoRegretSemanticsProbe.obstruction_feasible,
`NoRegretSemanticsProbe.actual_signed_losses,
`NoRegretSemanticsProbe.zero_horizon,
`NoRegretSemanticsProbe.even_T2,
`NoRegretSemanticsProbe.odd_T3,
`NoRegretSemanticsProbe.same_process_strict,
`BanditRL.OnlineLearning.meanPredict_noRegret,
`BanditRL.OnlineLearning.noRegret_of_vanishing_bound,
`BanditRL.OnlineLearning.comparatorRegret_eq_sum,
`BanditRL.OnlineLearning.LimitNoRegret,
`BanditRL.OnlineLearning.NoRegretCounterexample.potential,
`BanditRL.OnlineLearning.NoRegretCounterexample.loss,
`BanditRL.OnlineLearning.comparatorRegret,
`BanditRL.OnlineLearning.NoRegret,
`BanditRL.OnlineLearning.meanPredict,
`NoRegretSemanticsProbe.linearLoss]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineNoRegretSemanticsCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineNoRegretSemanticsCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Nine new public reconciliation proofs/three reused proofs/six scoped context definitions, fifteen named canary proofs/one test definition. Selected34 compiled nodes; actual direct TYPE and VALUE constant occurrences, not a full registry or teaching/source inventory.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
