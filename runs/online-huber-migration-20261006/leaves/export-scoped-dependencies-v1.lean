import Lean
import Lean.Util.FoldConsts

open Lean

def targets : Array Name := #[
  `BanditRL.OnlineHuber.hasDerivAt_ite_le,
  `BanditRL.OnlineHuber.huber_three_pieces,
  `BanditRL.OnlineHuber.huber_zero,
  `BanditRL.OnlineHuber.hasDerivAt_join,
  `BanditRL.OnlineHuber.huber_hasDerivAt,
  `BanditRL.OnlineHuber.huber_deriv_clamp,
  `BanditRL.OnlineHuber.huber_convex,
  `BanditRL.OnlineHuber.huber_deriv_bound,
  `BanditRL.OnlineHuber.huber_deriv_source,
  `BanditRL.OnlineHuber.huber_linear_hasGradientAt,
  `BanditRL.OnlineHuber.huber_linear_convex,
  `BanditRL.OnlineHuber.huber_linear_gradient_bound,
  `BanditRL.OnlineHuber.project_fullSpace,
  `BanditRL.OnlineHuber.huber_regular,
  `BanditRL.OnlineHuber.huber_step,
  `BanditRL.OnlineHuber.huber_regret_fixed,
  `BanditRL.OnlineHuber.huber_average_bound,
  `BanditRL.OnlineHuber.huber_rate_tendsto,
  `BanditRL.OnlineHuber.huber_average_eventually,
  `BanditRL.OnlineHuber.huber,
  `BanditRL.OnlineHuber.fullSpace,
  `BanditRL.OnlineHuber.linearLoss]

def moduleName (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString |>.getD "unknown"

def deps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one output path"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof }] {} (loadExts := true)
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
      ("scope", toJson "nineteen retained Huber source-supporting proofs and three definitions; direct type/value boundary only")]),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]
  IO.FS.writeFile output (graph.pretty ++ "\n")
  return 0
