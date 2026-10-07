import Tests.OnlineSubgradientDescentCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineSubgradientDescent.lemma_2_31,
 `BanditRL.OnlineSubgradientDescent.currentSubgradient_mem,
 `BanditRL.OnlineSubgradientDescent.finite_loss,
 `BanditRL.OnlineSubgradientDescent.iterate_mem,
 `BanditRL.OnlineSubgradientDescent.iterate_prefix,
 `BanditRL.OnlineSubgradientDescent.iterate_support,
 `BanditRL.OnlineSubgradientDescent.iterate_finite_loss,
 `BanditRL.OnlineSubgradientDescent.one_step_chain,
 `BanditRL.OnlineSubgradientDescent.one_step,
 `BanditRL.OnlineSubgradientDescent.regret_fixed,
 `BanditRL.OnlineSubgradientDescent.regret_fixed_coarse,
 `BanditRL.OnlineSubgradientDescent.regret_variable_bound,
 `BanditRL.OnlineSubgradientDescent.regret_variable,
 `BanditRL.OnlineSubgradientDescent.regret_tuned_distance,
 `BanditRL.OnlineSubgradientDescent.regret_tuned,
 `BanditRL.OnlineSubgradientDescent.SubdifferentiableOn,
 `BanditRL.OnlineSubgradientDescent.currentSubgradient,
 `BanditRL.OnlineSubgradientDescent.step,
 `BanditRL.OnlineSubgradientDescent.iterate,
 `BanditRL.OnlineSubgradientDescent.regret,
 `BanditRL.OnlineSubgradientDescent.Domain,
 `OSDOutsideProbe.linear_on,
 `OSDOutsideProbe.support_at_two,
 `OSDOutsideProbe.project_neg_four,
 `OSDOutsideProbe.arbitrary_current_and_actual_clipping,
 `OSDAlgorithmProbe.absolute_on,
 `OSDAlgorithmProbe.chosen_positive,
 `OSDAlgorithmProbe.chosen_negative,
 `OSDAlgorithmProbe.chosen_norm,
 `OSDAlgorithmProbe.project_neg_two,
 `OSDAlgorithmProbe.project_two,
 `OSDAlgorithmProbe.project_one,
 `OSDAlgorithmProbe.fixed_first,
 `OSDAlgorithmProbe.fixed_second,
 `OSDAlgorithmProbe.fixed_clipped_two_round,
 `OSDAlgorithmProbe.fixed_bound_with_terminal,
 `OSDAlgorithmProbe.fixed_terminal_positive,
 `OSDAlgorithmProbe.variable_first,
 `OSDAlgorithmProbe.variable_second,
 `OSDAlgorithmProbe.diameter_two,
 `OSDAlgorithmProbe.variable_bound_with_terminal,
 `OSDAlgorithmProbe.variable_nonconstant_and_terminal,
 `OSDAlgorithmProbe.tuned_all_comparators,
 `OSDAlgorithmProbe.future_inputs_do_not_change_output,
 `OSDAlgorithmProbe.zero_horizon,
 `OSDOutsideProbe.interval,
 `OSDOutsideProbe.linearLoss,
 `OSDAlgorithmProbe.absoluteLoss,
 `OSDAlgorithmProbe.losses,
 `OSDAlgorithmProbe.variableEta,
 `OSDAlgorithmProbe.futureEta,
 `OSDAlgorithmProbe.futureLoss,
 `OSDAlgorithmProbe.interval]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof }, { module := `Tests.OnlineSubgradientDescentCanary }] {} (loadExts := true)
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
      ("dependency_semantics", toJson "direct-constant-occurrence"),
      ("scope", toJson "selected53 existing actual OSD production/canary nodes; not newly authored proofs; direct type/value occurrences only, not full registry graph")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
