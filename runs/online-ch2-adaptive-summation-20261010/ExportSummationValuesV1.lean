import BanditRLProof.OnlineAdaptiveSummation
import Lean
import Lean.Util.FoldConsts
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof.OnlineAdaptiveSummation }] {}
    (loadExts := true)
  let name := `BanditRL.OnlineAdaptiveSummation.lemma_4_13
  let some info := env.find? name | throw <| IO.userError "public theorem missing"
  let some value := info.value? (allowOpaque := true) | throw <| IO.userError "BODY missing"
  let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
  let vd := value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
  for required in #[`ContinuousOn.intervalIntegrable_of_Icc,
      `intervalIntegral.integral_mono_on, `intervalIntegral.integral_const,
      `intervalIntegral.sum_integral_adjacent_intervals] do
    if !vd.contains required then throw <| IO.userError s!"missing VALUE dependency {required}"
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual compiled environment"),
    ("lean_version",toJson Lean.versionString),
    ("declaration",toJson name.toString),
    ("kind",toJson "theorem"),
    ("has_value",toJson true),
    ("TYPE_constants",toJson <| td.map Name.toString),
    ("VALUE_constants",toJson <| vd.map Name.toString),
    ("boundary",toJson "Direct compiled TYPE/VALUE constant presences for one selected public theorem; not occurrence counts, proof necessity, a complete transitive graph or an independent result denominator.")]).pretty ++ "\n")
  return 0
