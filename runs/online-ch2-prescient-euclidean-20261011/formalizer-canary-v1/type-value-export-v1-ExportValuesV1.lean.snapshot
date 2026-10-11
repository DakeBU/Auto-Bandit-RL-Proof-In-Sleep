import Tests.OnlinePrescientEuclideanCanary
import Lean
import Lean.Util.FoldConsts
open Lean

def constants (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `Tests.OnlinePrescientEuclideanCanary}] {}
    (loadExts := true)
  let mut nodes : Array Json := #[]
  for n in #[`PrescientEuclideanProbe.variable_quadratic_actual_run, `PrescientEuclideanProbe.fixed_quadratic_actual_run] do
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
    ("boundary",toJson "Two complete compiled canary declarations TYPE/VALUE constant sets. Occurrence is not necessity, a complete transitive dependency graph, source acceptance or library utility. Imported-module membership is not a theorem implication.")]).pretty ++ "\n")
  return 0
