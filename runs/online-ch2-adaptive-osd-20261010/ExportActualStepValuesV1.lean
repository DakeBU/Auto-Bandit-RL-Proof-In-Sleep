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
  for n in #[`BanditRL.OnlineAdaptiveOSD.energy_step_mono, `BanditRL.OnlineAdaptiveOSD.energy_pos_of_selected_ne_zero, `BanditRL.OnlineAdaptiveOSD.eta_pos_of_selected_ne_zero, `BanditRL.OnlineAdaptiveOSD.zero_feedback_step, `BanditRL.OnlineAdaptiveOSD.one_step_chain, `BanditRL.OnlineAdaptiveOSD.one_step, `BanditRL.OnlineAdaptiveOSD.regret_zero_diameter] do
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {n}"
    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let vd := value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    rows := rows.push <| Json.mkObj [
      ("declaration",toJson n.toString), ("has_value",toJson true),
      ("TYPE_constants",toJson <| td.map Name.toString),
      ("VALUE_constants",toJson <| vd.map Name.toString)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual compiled environment"), ("lean_version",toJson Lean.versionString),
    ("rows",Json.arr rows),
    ("boundary",toJson "Seven actual same-run one-step dependency proof VALUEs; direct selected constants, not seven source results, a full graph or proof necessity. Parent regret not yet proved.")]).pretty ++ "\n")
  return 0
