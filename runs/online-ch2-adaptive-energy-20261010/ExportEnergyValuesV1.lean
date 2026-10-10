import BanditRLProof.OnlineAdaptiveEnergy
import Lean
import Lean.Util.FoldConsts
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof.OnlineAdaptiveEnergy }] {}
    (loadExts := true)
  let selected : Array (Name × Name) := #[
    (`BanditRL.OnlineAdaptiveEnergy.sum_div_sqrt_prefix,
      `BanditRLProof.Tsallis.two_mul_sqrt_sub_sqrt_le_sub_div_sqrt),
    (`BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix,
      `BanditRL.OnlineAdaptiveEnergy.sum_div_sqrt_prefix),
    (`BanditRL.OnlineAdaptiveEnergy.source_energy_term_bound,
      `BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix)]
  let mut rows : Array Json := #[]
  for (name, parent) in selected do
    let some info := env.find? name | throw <| IO.userError s!"missing {name}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"BODY missing {name}"
    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let vd := value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    if !vd.contains parent then throw <| IO.userError s!"missing VALUE parent {parent}"
    rows := rows.push <| Json.mkObj [
      ("declaration",toJson name.toString), ("has_value",toJson true),
      ("TYPE_constants",toJson <| td.map Name.toString),
      ("VALUE_constants",toJson <| vd.map Name.toString),
      ("required_direct_parent",toJson parent.toString)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual compiled environment"),
    ("lean_version",toJson Lean.versionString), ("rows",Json.arr rows),
    ("boundary",toJson "Direct compiled TYPE/VALUE constant presences for three proof terminals of one source family; not occurrence counts, proof necessity, full transitive graph, algorithm guarantee or chapter denominator.")]).pretty ++ "\n")
  return 0
