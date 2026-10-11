import CumulativeProducerCandidate
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.OnlineConvex.cumulative_regularizer_source_strongConvex
run_cmd do
  let env ← getEnv
  let target := `BanditRL.OnlineConvex.cumulative_regularizer_source_strongConvex
  let parent := `BanditRL.OnlineConvex.sourceProper_of_domain
  let some ci := env.find? target | throwError "Missing imported theorem"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing imported value"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  unless (deps value).contains parent.toString do throwError "Missing genuine properness dependency"
  let rec fullCalls : Expr → Nat
    | e@(.app f a) => (if e.getAppFn.isConstOf parent && e.getAppArgs.size == 6 then 1 else 0) + fullCalls f + fullCalls a
    | .lam _ t b _ => fullCalls t + fullCalls b
    | .forallE _ t b _ => fullCalls t + fullCalls b
    | .letE _ t v b _ => fullCalls t + fullCalls v + fullCalls b
    | .mdata _ b => fullCalls b
    | .proj _ _ b => fullCalls b
    | _ => 0
  let calls := fullCalls value
  unless calls > 0 do throwError "Missing six-argument properness application"
  let some idx := env.getModuleIdxFor? target | throwError "No theorem module origin"
  let mod := env.header.moduleNames[idx.toNat]!
  unless mod == `CumulativeProducerCandidate do throwError "Unexpected scratch module binding"
  let olean ← liftIO <| findOLean mod
  let some parentIdx := env.getModuleIdxFor? parent | throwError "No parent origin"
  let parentMod := env.header.moduleNames[parentIdx.toNat]!
  let parentOlean ← liftIO <| findOLean parentMod
  let rec canon : Lean.Expr → Lean.Expr
    | .forallE _ t b i => .forallE .anonymous (canon t) (canon b) i
    | .lam _ t b i => .lam .anonymous (canon t) (canon b) i
    | .letE _ t v b n => .letE .anonymous (canon t) (canon v) (canon b) n
    | .app f a => .app (canon f) (canon a)
    | .mdata _ e => canon e
    | .proj s i e => .proj s i (canon e)
    | e => e
  let writeNew := fun (name : String) (s : String) => liftIO do
    let file ← IO.FS.Handle.mk (System.FilePath.mk "tmp/online-b4-cumulative-producer-body-20261012" / name) .writeNew
    file.putStr s
  writeNew "imported-TYPE-alpha-v1.txt" (reprStr (canon ci.type))
  writeNew "imported-VALUE-alpha-v1.txt" (reprStr (canon value))
  writeNew "imported-constants-v1.json" ((Json.mkObj [
    ("declaration", toJson target.toString), ("TYPE", toJson (deps ci.type)),
    ("VALUE", toJson (deps value)), ("properness_parent", toJson parent.toString),
    ("properness_parent_application_arity", toJson (6 : Nat)),
    ("properness_parent_full_applications", toJson calls),
    ("actual_module", toJson mod.toString), ("actual_resolved_olean", toJson olean.toString),
    ("parent_module", toJson parentMod.toString), ("parent_resolved_olean", toJson parentOlean.toString)]).pretty ++ "\n")
