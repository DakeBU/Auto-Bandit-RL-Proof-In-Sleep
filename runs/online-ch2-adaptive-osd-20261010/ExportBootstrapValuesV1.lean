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
  for n in #[`BanditRL.OnlineAdaptiveOSD.energy_succ, `BanditRL.OnlineAdaptiveOSD.output_succ, `BanditRL.OnlineAdaptiveOSD.energy_eq_sum, `BanditRL.OnlineAdaptiveOSD.history_mem, `BanditRL.OnlineAdaptiveOSD.output_mem, `BanditRL.OnlineAdaptiveOSD.energy_nonneg, `BanditRL.OnlineAdaptiveOSD.eta_eq_energy, `BanditRL.OnlineAdaptiveOSD.trajectory_finite_loss, `BanditRL.OnlineAdaptiveOSD.oracle_feedback, `BanditRL.OnlineAdaptiveOSD.canonical_feedback] do
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
    ("boundary",toJson "Ten actual same-run structural/support bootstrap proof VALUEs, not ten source results; direct used-constant evidence, not a full graph or proof necessity. Parent regret remains unproved.")]).pretty ++ "\n")
  return 0
