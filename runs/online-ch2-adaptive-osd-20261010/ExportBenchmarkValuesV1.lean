import BanditRLProof.OnlineAdaptiveBenchmark
import Lean
import Lean.Util.FoldConsts
open Lean
unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `BanditRLProof.OnlineAdaptiveBenchmark}] {} (loadExts := true)
  let mut rows : Array Json := #[]
  for n in #[`BanditRL.OnlineAdaptiveBenchmark.benchmark_isGLB, `BanditRL.OnlineAdaptiveBenchmark.source_benchmark_value, `BanditRL.OnlineAdaptiveBenchmark.benchmark_attained_iff, `BanditRL.OnlineAdaptiveBenchmark.benchmark_positive_minimum, `BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum] do
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
    ("boundary",toJson "Five full benchmark/attainment/source-conjunction actual proof VALUEs. Selected direct constants only; not a full graph, necessity, literal printed-minimum certification, or package/chapter acceptance.")]).pretty ++ "\n")
  return 0
