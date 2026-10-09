import BanditRLProof.OnlinePrescientBregmanSource
import BanditRLProof.OnlineFTLSelector
import Lean
import Lean.Util.FoldConsts
open Lean

def targets : Array Name := #[
`BanditRL.OnlineProximal.convex_minimizer_comparison,
`BanditRL.OnlineBregman.divergence,
`BanditRL.OnlineBregman.divergence_self,
`BanditRL.OnlineBregman.three_point_identity,
`BanditRL.OnlineBregman.divergence_nonneg,
`BanditRL.OnlineBregman.proximal_one_step,
`BanditRL.OnlineBregman.divergence_eq_gradient,
`BanditRL.OnlineBregman.finitePart_convex_of_subdifferentiable,
`BanditRL.OnlineBregman.proximal_finitePart_minimizer_iff,
`BanditRL.OnlineBregman.proximal_one_step_extended,
`BanditRL.OnlineBregman.divergence_extension_eq,
`BanditRL.OnlinePrescientBregman.advance,
`BanditRL.OnlinePrescientBregman.iterate,
`BanditRL.OnlinePrescientBregman.advance_some_spec,
`BanditRL.OnlinePrescientBregman.advance_none_iff,
`BanditRL.OnlinePrescientBregman.iterate_prefix,
`BanditRL.OnlinePrescientBregman.iterate_succ_some_spec,
`BanditRL.OnlinePrescientBregman.iterate_no_recovery,
`BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained,
`BanditRL.OnlinePrescientBregman.iterate_one_step,
`BanditRL.OnlinePrescientBregman.iterate_divergence_sum,
`BanditRL.OnlinePrescientBregman.iterate_fixed_sharp,
`BanditRL.OnlinePrescientBregman.iterate_variable_sharp,
`BanditRL.OnlinePrescientBregman.iterate_fixed_regret,
`BanditRL.OnlinePrescientBregman.iterate_variable_regret,
`BanditRL.OnlineConvex.sourceProper_of_domain,
`BanditRL.OnlinePrescientBregman.penalized_strictConvex,
`BanditRL.OnlinePrescientBregman.advance_eq_some_of_minimizer,
`BanditRL.OnlinePrescientBregman.iterate_eq_of_source_updates,
`BanditRL.OnlinePrescientBregman.source_fixed_regret,
`BanditRL.OnlinePrescientBregman.source_variable_regret,
`BanditRL.OnlineFTLSelector.cumulative,
`BanditRL.OnlineFTLSelector.minimizers,
`BanditRL.OnlineFTLSelector.select,
`BanditRL.OnlineFTLSelector.predict,
`BanditRL.OnlineFTLSelector.cumulative_prefix,
`BanditRL.OnlineFTLSelector.select_some_spec,
`BanditRL.OnlineFTLSelector.select_none_iff,
`BanditRL.OnlineFTLSelector.select_congr,
`BanditRL.OnlineFTLSelector.select_eq_some_of_unique,
`BanditRL.OnlineFTLSelector.predict_zero,
`BanditRL.OnlineFTLSelector.predict_some_spec,
`BanditRL.OnlineFTLSelector.predict_none_iff,
`BanditRL.OnlineFTLSelector.predict_prefix]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof.OnlinePrescientBregmanSource }, { module := `BanditRLProof.OnlineFTLSelector }] {} (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  let mut selected := targets
  let mut i := 0
  while i < selected.size do
    let n := selected[i]!
    i := i + 1
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing proof {n}"
    for dep in deps value do
      if dep.toString.startsWith "_private.Tests.OnlinePrescientBregmanSourceCanary." && !selected.contains dep then
        selected := selected.push dep
  for n in selected do
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
    ("schema_version", toJson (1 : Nat)), ("root_module", toJson "selected-production-module-union"),
    ("lean_version", toJson Lean.versionString),
    ("extraction", Json.mkObj [("source", toJson "compiled-environment"),
      ("dependency_semantics", toJson "coalesced-direct-TYPE_VALUE-constant-presence-not-occurrence-count"),
      ("scope", toJson "31 prescient parent/source declarations plus 13 generic FTL declarations from their actual compiled module union. Direct TYPE_VALUE constant presences only; not occurrence counts, a complete transitive graph, a root gate, shared registry update or independent source-result denominator.")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
