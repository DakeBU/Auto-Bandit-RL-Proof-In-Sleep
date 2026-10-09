import Tests.OnlineUnboundedOSDCanary
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

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `Tests.OnlineUnboundedOSDCanary}] {} (loadExts := true)
  let mut rows : Array Json := #[]
  for (name,index,required) in #[
    (`BanditRL.OnlineUnboundedOSDCanary.scalar_actual_two_rounds,6,`BanditRL.OnlineUnboundedOSD.switching_scalar_regret_identity),
    (`BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound,6,`BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound),
    (`BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound,7,`BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound),
    (`BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound,8,`BanditRL.OnlineUnboundedOSD.theorem_5_4)] do
    let some info := env.find? name | throw <| IO.userError s!"missing {name}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing value {name}"
    let tail ← match conjunct value index with | .ok e => pure e | .error err => throw <| IO.userError err
    let deps := tail.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let head := match tail.getAppFn with | .const n _ => n.toString | _ => "nonconstant-head"
    if !deps.contains required then throw <| IO.userError s!"numeric branch {name}/{index} lacks {required}"
    rows := rows.push <| Json.mkObj [
      ("declaration",toJson name.toString),("zero_based_conjunct_index",toJson index),
      ("selected_proof_head",toJson head),("required_production_VALUE",toJson required.toString),
      ("required_present",toJson true),("selected_proof_direct_constants",toJson <| deps.map Name.toString)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual-compiled-environment"),
    ("selection",toJson "Substitute top-level lets, remove metadata/explicit id, select each specified And.intro conjunct independently. No theorem unfolding or proof-irrelevance normalization. Whole-conjunction dependencies do not certify selected numeric branches."),
    ("rows",Json.arr rows)]).pretty ++ "\n")
  return 0
