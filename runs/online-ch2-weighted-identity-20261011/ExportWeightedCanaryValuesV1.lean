import Tests.OnlineWeightedPotentialCanary
import Lean
import Lean.Util.FoldConsts
open Lean

partial def peel (e : Expr) : Expr :=
  let reduced := e.headBeta
  if reduced != e then peel reduced else
  match e with
  | .letE _ _ value body _ => peel (body.instantiate1 value)
  | .mdata _ body => peel body
  | .lam _ _ body _ => peel body
  | _ => if e.getAppFn.isConstOf ``id && e.getAppArgs.size >= 2 then
      peel (mkAppN e.getAppArgs[1]! (e.getAppArgs.extract 2 e.getAppArgs.size)) else e

partial def conjunct (e : Expr) (index : Nat) : Except String Expr := do
  let p := peel e
  if p.getAppFn.isConstOf ``And.intro && p.getAppArgs.size == 4 then
    if index == 0 then return peel p.getAppArgs[2]!
    else conjunct p.getAppArgs[3]! (index - 1)
  else if (p.getAppFn.isConstOf ``And.casesOn || p.getAppFn.isConstOf ``And.rec) then
    conjunct p.getAppArgs.back! index
  else if index == 0 then return p
  else throw "conjunction spine ended early"

def constants (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `Tests.OnlineWeightedPotentialCanary}] {}
    (loadExts := true)
  let mut nodes : Array Json := #[]
  for n in #[`WeightedIdentityProbe.signed_weights_complete, `WeightedIdentityProbe.one_step_free_terminal_complete, `WeightedIdentityProbe.constant_zero_weights_complete, `WeightedIdentityProbe.ogd_three_step_complete, `WeightedIdentityProbe.osd_three_step_complete] do
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {n}"
    nodes := nodes.push <| Json.mkObj [
      ("declaration",toJson n.toString), ("has_value",toJson true),
      ("TYPE_constants",toJson <| (constants info.type).map Name.toString),
      ("VALUE_constants",toJson <| (constants value).map Name.toString)]
  let mut branches : Array Json := #[]
  for (name,index,required) in #[
    (`WeightedIdentityProbe.signed_weights_complete,7,`BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq),
    (`WeightedIdentityProbe.one_step_free_terminal_complete,0,`BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq),
    (`WeightedIdentityProbe.constant_zero_weights_complete,0,`BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq),
    (`WeightedIdentityProbe.constant_zero_weights_complete,2,`BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq),
    (`WeightedIdentityProbe.ogd_three_step_complete,14,`BanditRL.OnlineWeightedPotential.distance_potential_sum_eq),
    (`WeightedIdentityProbe.osd_three_step_complete,15,`BanditRL.OnlineWeightedPotential.distance_potential_sum_eq),
    (`WeightedIdentityProbe.ogd_three_step_complete,8,`BanditRL.OnlineGradientDescentSource.linear_regular),
    (`WeightedIdentityProbe.ogd_three_step_complete,9,`BanditRL.OnlineGradientDescentSource.gradient_linear),
    (`WeightedIdentityProbe.osd_three_step_complete,8,`BanditRL.OnlineConvex.affine_proper),
    (`WeightedIdentityProbe.osd_three_step_complete,9,`BanditRL.OnlineConvex.affine_subdifferential)] do
    let some info := env.find? name | throw <| IO.userError s!"missing {name}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {name}"
    let selected ← match conjunct value index with
      | .ok e => pure e
      | .error err => throw <| IO.userError err
    let used := constants selected
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
    ("boundary",toJson "Five complete actual canary declaration TYPE/VALUEs and ten selected conjunction VALUEs, substituting lets/removing metadata/id. Local lambda binders and And eliminator continuations are traversed syntactically to reach branch values; no type-correct closed subproof is claimed. Branch occurrence is not necessity or a complete dependency graph; no combined package/chapter acceptance.")]).pretty ++ "\n")
  return 0
