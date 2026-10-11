import FullIffCandidate
import Lean.Util.FoldConsts
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some ci := env.find? `BanditRL.OnlineConvex.stronglyConvex_iff_sourceSubgradient_growth |
    throwError "Missing declaration"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing VALUE"
  let rec canon : Expr → Expr
    | .forallE _ t b i => .forallE .anonymous (canon t) (canon b) i
    | .lam _ t b i => .lam .anonymous (canon t) (canon b) i
    | .letE _ t v b n => .letE .anonymous (canon t) (canon v) (canon b) n
    | .app f a => .app (canon f) (canon a)
    | .mdata _ b => canon b
    | .proj n i b => .proj n i (canon b)
    | e => e
  let rec walk (ctx : Array (Name × Expr)) (e : Expr) : Except String (Array Json) := do
    let mut out := #[]
    let fn := e.getAppFn
    let args := e.getAppArgs
    let binderName := fun (e : Expr) => match e with
      | .bvar i => (ctx[ctx.size-1-i]?.map Prod.fst).getD .anonymous
      | _ => .anonymous
    let requireArg := fun (i : Nat) (n : Name) =>
      if binderName args[i]! == n then Except.ok () else Except.error s!"Operand {i} is not {n}"
    if fn.isConstOf `BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth && args.size == 19 then
      for (i,n) in #[(3,`d),(4,`e),(5,`f),(6,`V),(7,`lam),(8,`hf),(9,`hV),(10,`hdom),
          (11,`hlam),(12,`hstrong),(13,`p),(14,`hp),(15,`g),(16,`hg),(17,`q),(18,`hq)] do requireArg i n
      out := out.push <| Json.mkObj [("check",toJson "forward19 exact original operands and derived hdom"),("passed",toJson true)]
    if fn.isConstOf `BanditRL.OnlineConvex.subgradient_point_finite && args.size == 8 then
      requireArg 4 `hfcoord
      requireArg 6 `g
      requireArg 7 `hg
      let .bvar properIdx := args[4]! | throw "Properness argument not actual local binder"
      let properTy := ctx[ctx.size-1-properIdx]!.2.liftLooseBVars 0 (properIdx+1)
      unless properTy.getAppFn.isConstOf `BanditRL.OnlineConvex.SourceProper do throw "hfcoord type not SourceProper"
      unless canon args[3]! == canon properTy.getAppArgs.back! do throw "Finite parent F differs from coordinate properness F"
      let pointArgs := args[5]!.getAppArgs
      unless pointArgs.size >= 2 && binderName pointArgs.back! == `p &&
          binderName pointArgs[pointArgs.size-2]! == `e do throw "Finite point not actual e applied p"
      out := out.push <| Json.mkObj [("check",toJson "finite8 actual coordinate function equals hfcoord type, actual e(p),g,hg"),("passed",toJson true)]
    if binderName fn == `hgrowth && args.size == 6 then
      requireArg 0 `z
      requireArg 1 `hz
      requireArg 4 `g
      requireArg 5 `hg
      let qn := binderName args[2]!
      unless (qn == `x && binderName args[3]! == `hx) ||
          (qn == `y && binderName args[3]! == `hy) do throw "Converse endpoint not original x/hx or y/hy"
      out := out.push <| Json.mkObj [("check",toJson "converse actual assumed growth at same z,hz,g,hg"),
        ("query",toJson qn.toString),("passed",toJson true)]
    if binderName fn == `hsub && args.size == 2 then
      out := out.push <| Json.mkObj [("check",toJson "actual all-point support premise used"),
        ("point",toJson (binderName args[0]!).toString),("membership",toJson (binderName args[1]!).toString)]
    match e with
    | .app f a => out := out ++ (← walk ctx f) ++ (← walk ctx a)
    | .lam n t b _ | .forallE n t b _ => out := out ++ (← walk ctx t) ++ (← walk (ctx.push (n,t)) b)
    | .letE n t v b _ => out := out ++ (← walk ctx t) ++ (← walk ctx v) ++ (← walk (ctx.push (n,t)) b)
    | .mdata _ b | .proj _ _ b => out := out ++ (← walk ctx b)
    | _ => pure ()
    return out
  let rows ← match walk #[] value with
    | .ok rows => pure rows
    | .error s => throwError "{s}"
  liftIO do
    let file ← IO.FS.Handle.mk "tmp/online-b4-full-iff-body-20261012/imported-structural-operands-v3.json" .writeNew
    file.putStr ((toJson rows).pretty ++ "\n")
