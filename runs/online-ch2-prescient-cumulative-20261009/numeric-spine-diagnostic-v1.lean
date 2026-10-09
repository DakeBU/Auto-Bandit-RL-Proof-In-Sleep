import Tests.OnlinePrescientBregmanRegretCanary
import Lean
open Lean Elab Command
partial def peel (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => peel (b.instantiate1 v)
  | .mdata _ b => peel b
  | _ => if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then peel e.getAppArgs[1]! else e
run_cmd do
  let env ← getEnv
  for name in #[`BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run,
      `BanditRL.OnlinePrescientBregmanRegretCanary.decreasing_signed_run] do
    let some (.thmInfo info) := env.find? name | throwError "missing actual theorem value"
    let p := peel info.value
    match p.getAppFn with
    | .const n _ => logInfo m!"{name}: actual peeled root {n}, arguments {p.getAppArgs.size}"
    | _ => throwError "unexpected nonconstant root"
