import Tests.OnlineLinearizationCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineLinearization.outputHistory_last,
 `BanditRL.OnlineLinearization.history_zero,
 `BanditRL.OnlineLinearization.history_succ,
 `BanditRL.OnlineLinearization.history_castSucc,
 `BanditRL.OnlineLinearization.history_selected,
 `BanditRL.OnlineLinearization.output_linear_run,
 `BanditRL.OnlineLinearization.outputHistory_played,
 `BanditRL.OnlineLinearization.output_mem,
 `BanditRL.OnlineLinearization.history_prefix,
 `BanditRL.OnlineLinearization.output_prefix,
 `BanditRL.OnlineLinearization.oracle_feedback,
 `BanditRL.OnlineLinearization.canonical_feedback,
 `BanditRL.OnlineLinearization.trajectory_finite_loss,
 `BanditRL.OnlineLinearization.support_gap,
 `BanditRL.OnlineLinearization.linearLoss_gap,
 `BanditRL.OnlineLinearization.regret_comparison,
 `BanditRL.OnlineLinearization.regret_transfer,
 `BanditRL.OnlineLinearization.canonical_regret_comparison,
 `BanditRL.OnlineLinearization.Feasible,
 `BanditRL.OnlineLinearization.outputHistory,
 `BanditRL.OnlineLinearization.history,
 `BanditRL.OnlineLinearization.output,
 `BanditRL.OnlineLinearization.selected,
 `BanditRL.OnlineLinearization.LegalFeedback,
 `BanditRL.OnlineLinearization.linearRun,
 `BanditRL.OnlineLinearization.linearLoss,
 `BanditRL.OnlineLinearization.regret,
 `BanditRL.OnlineLinearization.Domain,
 `BanditRL.OnlineLinearization.LinearPolicy,
 `BanditRL.OnlineLinearization.SupportPolicy,
 `LinearizationProbe.learner_feasible,
 `LinearizationProbe.quadratic_support,
 `LinearizationProbe.affine_support,
 `LinearizationProbe.quadratic_on,
 `LinearizationProbe.affine_on,
 `LinearizationProbe.losses_on,
 `LinearizationProbe.x_zero,
 `LinearizationProbe.g_zero,
 `LinearizationProbe.g_one,
 `LinearizationProbe.x_one,
 `LinearizationProbe.x_two,
 `LinearizationProbe.feedback_two,
 `LinearizationProbe.actual_same_linear_run,
 `LinearizationProbe.actual_convex_regret,
 `LinearizationProbe.actual_linear_regret,
 `LinearizationProbe.actual_public_comparison,
 `LinearizationProbe.actual_strict_slack,
 `LinearizationProbe.universal_two,
 `LinearizationProbe.actual_public_transfer,
 `LinearizationProbe.actual_bound_value,
 `LinearizationProbe.nonzero_energy,
 `LinearizationProbe.positive_terminal,
 `LinearizationProbe.canonical_producer_instance,
 `LinearizationProbe.current_and_future_do_not_change_output,
 `LinearizationProbe.zero_horizon_actual_comparison,
 `LinearizationProbe.V,
 `LinearizationProbe.learner,
 `LinearizationProbe.quadratic,
 `LinearizationProbe.affine,
 `LinearizationProbe.losses,
 `LinearizationProbe.policy,
 `LinearizationProbe.bound,
 `LinearizationProbe.invalid_future,
 `LinearizationProbe.x,
 `LinearizationProbe.g]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Tests.OnlineLinearizationCanary }] {} (loadExts := true)
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "Tests.OnlineLinearizationCanary"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "Existing18 linearization proof bodies/9defs/3abbr and whole canary; compiled TEST environment selected65 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
