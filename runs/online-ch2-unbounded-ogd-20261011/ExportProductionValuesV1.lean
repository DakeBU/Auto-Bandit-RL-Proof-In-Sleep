import BanditRLProof.OnlineUnboundedOGD
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
  let env ← Lean.importModules #[{module := `BanditRLProof.OnlineUnboundedOGD}] {}
    (loadExts := true)
  let mut nodes : Array Json := #[]
  for n in #[`BanditRL.OnlineUnboundedOGD.regret_lower_bound] do
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {n}"
    nodes := nodes.push <| Json.mkObj [
      ("declaration",toJson n.toString), ("has_value",toJson true),
      ("TYPE_constants",toJson <| (constants info.type).map Name.toString),
      ("VALUE_constants",toJson <| (constants value).map Name.toString)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual compiled environment"),
    ("lean_version",toJson Lean.versionString),
    ("nodes",Json.arr nodes),
    ("boundary",toJson "One complete compiled production declaration TYPE/VALUE constant sets. Occurrence is not necessity, a complete transitive dependency graph, source acceptance or library utility. Imported-module membership is not a theorem implication.")]).pretty ++ "\n")
  return 0
