import Tests.OnlineSubgradientPolicyCanary
import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
 `BanditRL.OnlineSubgradientPolicy.history_zero,
 `BanditRL.OnlineSubgradientPolicy.history_succ,
 `BanditRL.OnlineSubgradientPolicy.output_zero,
 `BanditRL.OnlineSubgradientPolicy.output_succ,
 `BanditRL.OnlineSubgradientPolicy.history_mem,
 `BanditRL.OnlineSubgradientPolicy.output_mem,
 `BanditRL.OnlineSubgradientPolicy.history_prefix,
 `BanditRL.OnlineSubgradientPolicy.output_prefix,
 `BanditRL.OnlineSubgradientPolicy.oracle_feedback,
 `BanditRL.OnlineSubgradientPolicy.trajectory_finite_loss,
 `BanditRL.OnlineSubgradientPolicy.one_step_chain,
 `BanditRL.OnlineSubgradientPolicy.one_step,
 `BanditRL.OnlineSubgradientPolicy.regret_fixed,
 `BanditRL.OnlineSubgradientPolicy.regret_fixed_coarse,
 `BanditRL.OnlineSubgradientPolicy.regret_variable_bound,
 `BanditRL.OnlineSubgradientPolicy.regret_variable,
 `BanditRL.OnlineSubgradientPolicy.regret_tuned_distance,
 `BanditRL.OnlineSubgradientPolicy.regret_tuned,
 `BanditRL.OnlineSubgradientPolicy.canonicalPolicy_legal,
 `BanditRL.OnlineSubgradientPolicy.canonical_output,
 `BanditRL.OnlineSubgradientPolicy.canonical_selected,
 `BanditRL.OnlineSubgradientPolicy.history,
 `BanditRL.OnlineSubgradientPolicy.output,
 `BanditRL.OnlineSubgradientPolicy.selected,
 `BanditRL.OnlineSubgradientPolicy.OracleLaw,
 `BanditRL.OnlineSubgradientPolicy.canonicalPolicy,
 `BanditRL.OnlineSubgradientPolicy.LegalFeedback,
 `BanditRL.OnlineSubgradientPolicy.regret,
 `BanditRL.OnlineSubgradientPolicy.Domain,
 `BanditRL.OnlineSubgradientPolicy.SupportPolicy,
 `OSDPolicyProbe.flat_on,
 `OSDPolicyProbe.policy_oracle,
 `OSDPolicyProbe.lossA_on,
 `OSDPolicyProbe.lossB_on,
 `OSDPolicyProbe.pref_A,
 `OSDPolicyProbe.pref_B,
 `OSDPolicyProbe.selected_eq_preferred,
 `OSDPolicyProbe.selected_singleton,
 `OSDPolicyProbe.a_tie,
 `OSDPolicyProbe.b_tie,
 `OSDPolicyProbe.a_below,
 `OSDPolicyProbe.b_above,
 `OSDPolicyProbe.a_zero,
 `OSDPolicyProbe.b_zero,
 `OSDPolicyProbe.ga_zero,
 `OSDPolicyProbe.gb_zero,
 `OSDPolicyProbe.a_one,
 `OSDPolicyProbe.b_one,
 `OSDPolicyProbe.ga_one,
 `OSDPolicyProbe.gb_one,
 `OSDPolicyProbe.a_two,
 `OSDPolicyProbe.b_two,
 `OSDPolicyProbe.ga_two,
 `OSDPolicyProbe.gb_two,
 `OSDPolicyProbe.a_three,
 `OSDPolicyProbe.b_three,
 `OSDPolicyProbe.ga_three,
 `OSDPolicyProbe.gb_three,
 `OSDPolicyProbe.a_four,
 `OSDPolicyProbe.b_four,
 `OSDPolicyProbe.history_changes_actual_support,
 `OSDPolicyProbe.legalA,
 `OSDPolicyProbe.legalB,
 `OSDPolicyProbe.a_real_regret,
 `OSDPolicyProbe.b_real_regret,
 `OSDPolicyProbe.a_energy,
 `OSDPolicyProbe.b_energy,
 `OSDPolicyProbe.a_positive_terminal,
 `OSDPolicyProbe.b_positive_terminal,
 `OSDPolicyProbe.a_exact_fixed_bound,
 `OSDPolicyProbe.a_fixed_rhs_equality,
 `OSDPolicyProbe.offPath_history_eq,
 `OSDPolicyProbe.offPath_output_eq,
 `OSDPolicyProbe.offPath_selected_eq,
 `OSDPolicyProbe.offPath_legalA,
 `OSDPolicyProbe.offPath_not_oracle,
 `OSDPolicyProbe.offPath_actual_fixed,
 `OSDPolicyProbe.norm_bound_A,
 `OSDPolicyProbe.unit_diameter,
 `OSDPolicyProbe.offPath_tuned_all_comparators,
 `OSDPolicyProbe.ah_zero,
 `OSDPolicyProbe.gh_zero,
 `OSDPolicyProbe.ah_one,
 `OSDPolicyProbe.gh_one,
 `OSDPolicyProbe.ah_two,
 `OSDPolicyProbe.gh_two,
 `OSDPolicyProbe.ah_three,
 `OSDPolicyProbe.gh_three,
 `OSDPolicyProbe.ah_four,
 `OSDPolicyProbe.harmonic_energy,
 `OSDPolicyProbe.harmonic_last_eta_and_positive_terminal,
 `OSDPolicyProbe.harmonic_real_regret,
 `OSDPolicyProbe.harmonic_actual_variable,
 `OSDPolicyProbe.invalid_future_causal,
 `OSDPolicyProbe.invalid_future_current_loss,
 `OSDPolicyProbe.zero_horizon,
 `OSDPolicyProbe.canonical_invalid_future_bridge,
 `OSDPolicyProbe.empty_support_at_zero,
 `OSDPolicyProbe.empty_support_current_fallback,
 `OSDPolicyProbe.empty_support_actual_selected,
 `OSDPolicyProbe.empty_support_actual_output,
 `OSDPolicyProbe.empty_support_not_legal,
 `OSDPolicyProbe.zero_horizon_actual_fixed,
 `OSDPolicyProbe.zero_horizon_positive_cancelling_endpoints,
 `OSDPolicyProbe.flat,
 `OSDPolicyProbe.preferred,
 `OSDPolicyProbe.policy,
 `OSDPolicyProbe.lossA,
 `OSDPolicyProbe.lossB,
 `OSDPolicyProbe.eta,
 `OSDPolicyProbe.offPathPolicy,
 `OSDPolicyProbe.harmonic,
 `OSDPolicyProbe.futureLoss,
 `OSDPolicyProbe.futureEta,
 `OSDPolicyProbe.emptySupportLoss,
 `OSDPolicyProbe.V,
 `OSDPolicyProbe.a,
 `OSDPolicyProbe.b,
 `OSDPolicyProbe.ga,
 `OSDPolicyProbe.gb,
 `OSDPolicyProbe.ah,
 `OSDPolicyProbe.gh]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof }, { module := `Tests.OnlineSubgradientPolicyCanary }] {} (loadExts := true)
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
      ("scope", toJson "selected122 existing actual finite-history policy production/canary nodes; not newly authored proofs; direct type/value occurrences only, not full registry graph")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
