import Tests.OnlineAdaptiveEnergyCanary
import Lean
import Lean.Util.FoldConsts
open Lean

partial def peel (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => peel (body.instantiate1 value)
  | .mdata _ body => peel body
  | _ => if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then peel e.getAppArgs[1]! else e

partial def conjunct (e : Expr) (index : Nat) : Except String Expr := do
  let p := peel e
  if p.getAppFn.isConstOf ``And.intro && p.getAppArgs.size == 4 then
    if index == 0 then return peel p.getAppArgs[2]!
    else conjunct p.getAppArgs[3]! (index - 1)
  else if index == 0 then return p
  else throw "conjunction spine ended early"

def constants (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `Tests.OnlineAdaptiveEnergyCanary}] {}
    (loadExts := true)
  let mut nodes : Array Json := #[]
  for n in #[`BanditRL.OnlineAdaptiveEnergy.sum_div_sqrt_prefix,
      `BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix,
      `BanditRL.OnlineAdaptiveEnergy.source_energy_term_bound,
      `Tests.OnlineAdaptiveEnergyCanary.nonzero_energy_zero_prefix_canary,
      `Tests.OnlineAdaptiveEnergyCanary.zero_boundaries_canary] do
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {n}"
    nodes := nodes.push <| Json.mkObj [
      ("declaration",toJson n.toString), ("has_value",toJson true),
      ("TYPE_constants",toJson <| (constants info.type).map Name.toString),
      ("VALUE_constants",toJson <| (constants value).map Name.toString)]
  let mut branches : Array Json := #[]
  for (name,index) in #[
      (`Tests.OnlineAdaptiveEnergyCanary.nonzero_energy_zero_prefix_canary,0),
      (`Tests.OnlineAdaptiveEnergyCanary.nonzero_energy_zero_prefix_canary,3),
      (`Tests.OnlineAdaptiveEnergyCanary.zero_boundaries_canary,0),
      (`Tests.OnlineAdaptiveEnergyCanary.zero_boundaries_canary,1),
      (`Tests.OnlineAdaptiveEnergyCanary.zero_boundaries_canary,2)] do
    let some info := env.find? name | throw <| IO.userError s!"missing {name}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {name}"
    let selected ← match conjunct value index with
      | .ok e => pure e
      | .error err => throw <| IO.userError err
    let used := constants selected
    let required := `BanditRL.OnlineAdaptiveEnergy.source_energy_term_bound
    if !used.contains required then throw <| IO.userError s!"missing public call in {name}/{index}"
    branches := branches.push <| Json.mkObj [
      ("declaration",toJson name.toString), ("zero_based_conjunct_index",toJson index),
      ("selected_VALUE_constants",toJson <| used.map Name.toString),
      ("required_public_production",toJson required.toString),
      ("required_present",toJson true)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual compiled environment"),
    ("lean_version",toJson Lean.versionString),
    ("nodes",Json.arr nodes), ("selected_conjuncts",Json.arr branches),
    ("boundary",toJson "Direct TYPE/VALUE constants in five selected full declarations and independently selected five inequality conjunction branches (including strictgap via prefixT3), substituting local lets/removing metadata/id. Presence does not certify proof necessity or occurrence counts; no full transitive graph, algorithm guarantee or chapter denominator.")]).pretty ++ "\n")
  return 0
