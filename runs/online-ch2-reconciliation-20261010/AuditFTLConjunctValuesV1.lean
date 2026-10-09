import Tests.OnlineFTLSelectorCanary
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
  else throw "conjunction spine ended before requested index"

def constants (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `Tests.OnlineFTLSelectorCanary}] {} (loadExts := true)
  let mut rows : Array Json := #[]
  for (name,index,required) in #[
    (`Tests.OnlineFTLSelector.quadratic_trajectory,2,`BanditRL.OnlineFTLSelector.select_eq_some_of_unique),
    (`Tests.OnlineFTLSelector.quadratic_trajectory,3,`BanditRL.OnlineFTLSelector.select_eq_some_of_unique),
    (`Tests.OnlineFTLSelector.quadratic_trajectory,6,`BanditRL.OnlineFTLSelector.predict_some_spec),
    (`Tests.OnlineFTLSelector.current_future_independence,2,`BanditRL.OnlineFTLSelector.predict_prefix),
    (`Tests.OnlineFTLSelector.off_domain_invariance,3,`BanditRL.OnlineFTLSelector.select_congr),
    (`Tests.OnlineFTLSelector.off_domain_invariance,4,`BanditRL.OnlineFTLSelector.predict_prefix),
    (`Tests.OnlineFTLSelector.tied_minimizers,5,`BanditRL.OnlineFTLSelector.select_some_spec),
    (`Tests.OnlineFTLSelector.affine_nonattainment,3,`BanditRL.OnlineFTLSelector.select_none_iff),
    (`Tests.OnlineFTLSelector.affine_nonattainment,5,`BanditRL.OnlineFTLSelector.predict_none_iff),
    (`Tests.OnlineFTLSelector.recovery_after_nonattainment,0,`BanditRL.OnlineFTLSelector.predict_none_iff),
    (`Tests.OnlineFTLSelector.recovery_after_nonattainment,1,`BanditRL.OnlineFTLSelector.select_eq_some_of_unique)] do
    let some info := env.find? name | throw <| IO.userError s!"missing {name}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing value {name}"
    let tail ← match conjunct value index with | .ok e => pure e | .error err => throw <| IO.userError err
    let direct := constants tail
    let mut closure := direct
    let mut helpers : Array Json := #[]
    let mut i := 0
    while i < closure.size do
      let dep := closure[i]!
      i := i + 1
      if dep.toString.startsWith "_private.Tests.OnlineFTLSelectorCanary." then
        let some helper := env.find? dep | throw <| IO.userError s!"missing private helper {dep}"
        let some body := helper.value? (allowOpaque := true) | throw <| IO.userError s!"missing helper VALUE {dep}"
        let ds := constants body
        helpers := helpers.push <| Json.mkObj [
          ("name",toJson dep.toString),("VALUE_dependencies",toJson <| ds.map Name.toString)]
        for d in ds do
          if !closure.contains d then closure := closure.push d
    if !closure.contains required then throw <| IO.userError s!"selected conjunct {name}/{index} lacks {required}"
    rows := rows.push <| Json.mkObj [
      ("declaration",toJson name.toString),("zero_based_conjunct_index",toJson index),
      ("selected_proof_direct_constants",toJson <| direct.map Name.toString),
      ("private_Test_VALUE_expansions",Json.arr helpers),
      ("required_production_VALUE",toJson required.toString),
      ("required_direct",toJson <| direct.contains required),("required_present",toJson true)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual-compiled-environment"),
    ("selection",toJson "Independently substitute top-level lets, remove metadata/id and select the specified And.intro branch. Follow only referenced private Test VALUEs; no production theorem unfolding, proof-irrelevance normalization or import-graph inference. Substitution may retain other let-bound proof constants; required presence is not occurrence counting or proof necessity."),
    ("rows",Json.arr rows)]).pretty ++ "\n")
  return 0
