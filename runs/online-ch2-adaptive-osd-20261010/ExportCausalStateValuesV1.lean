import BanditRLProof.OnlineAdaptiveOSD
import Lean
import Lean.Util.FoldConsts
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `BanditRLProof.OnlineAdaptiveOSD}] {} (loadExts := true)
  let mut rows : Array Json := #[]
  for n in #[`BanditRL.OnlineAdaptiveOSD.state, `BanditRL.OnlineAdaptiveOSD.history,
      `BanditRL.OnlineAdaptiveOSD.energy, `BanditRL.OnlineAdaptiveOSD.output,
      `BanditRL.OnlineAdaptiveOSD.selected, `BanditRL.OnlineAdaptiveOSD.eta,
      `BanditRL.OnlineAdaptiveOSD.LegalFeedback, `BanditRL.OnlineAdaptiveOSD.regret,
      `BanditRL.OnlineAdaptiveOSD.state_succ, `BanditRL.OnlineAdaptiveOSD.state_prefix] do
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {n}"
    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let vd := value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    if n == `BanditRL.OnlineAdaptiveOSD.state_prefix && !vd.contains `BanditRL.OnlineAdaptiveOSD.state_succ then
      throw <| IO.userError "prefix missing actual compiled recurrence parent"
    rows := rows.push <| Json.mkObj [
      ("declaration",toJson n.toString), ("has_value",toJson true),
      ("TYPE_constants",toJson <| td.map Name.toString),
      ("VALUE_constants",toJson <| vd.map Name.toString)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual compiled environment"), ("lean_version",toJson Lean.versionString),
    ("rows",Json.arr rows),
    ("boundary",toJson "Eight actual definitions and two structural theorem values; not ten source claims, not full graph/proof necessity or same-run regret closure. Fixed external parameter/policy prefix boundary retained.")]).pretty ++ "\n")
  return 0
