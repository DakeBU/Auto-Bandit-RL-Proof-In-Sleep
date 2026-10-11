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
  let rec stripForall : Expr → Nat × Expr
    | .forallE _ _ b _ => let (n,e) := stripForall b; (n+1,e)
    | .mdata _ b => stripForall b
    | e => (0,e)
  let rec stripLambda : Expr → Nat × Expr
    | .lam _ _ b _ => let (n,e) := stripLambda b; (n+1,e)
    | .mdata _ b => stripLambda b
    | e => (0,e)
  let (typeBinders, typeBody) := stripForall ci.type
  let (valueBinders, valueBody) := stripLambda value
  unless typeBinders == valueBinders do throwError "Telescope alignment mismatch"
  let expectedF ← match typeBody with
    | .letE _ _ f _ _ => pure f
    | _ => throwError "Expected frozen type local F"
  let rec expose : Nat → Expr → Expr
    | 0,e => e
    | n+1,.letE _ _ v b _ => expose n (b.instantiate1 v)
    | n+1,.mdata _ b => expose n b
    | _,e => e
  let rec canon : Expr → Expr
    | .forallE _ t b i => .forallE .anonymous (canon t) (canon b) i
    | .lam _ t b i => .lam .anonymous (canon t) (canon b) i
    | .letE _ t v b n => .letE .anonymous (canon t) (canon v) (canon b) n
    | .app f a => .app (canon f) (canon a)
    | .mdata _ e => canon e
    | .proj s i e => .proj s i (canon e)
    | e => e
  let outer := expose 1000 valueBody
  unless outer.getAppFn.isConstOf ``And.intro && outer.getAppArgs.size == 4 do
    throwError "Expected first conjunction constructor; head constant={outer.getAppFn.constName?}; arity={outer.getAppArgs.size}; lambdaHead={outer.getAppFn.isLambda}"
  let properProp := outer.getAppArgs[0]!
  unless properProp.getAppFn.isConstOf `BanditRL.OnlineConvex.SourceProper && properProp.getAppArgs.size == 2 do
    throwError "First conjunct is not properness"
  unless canon properProp.getAppArgs[1]! == canon expectedF do
    throwError "Properness conclusion objective differs from frozen type F"
  let first := expose 1000 outer.getAppArgs[2]!
  unless first.getAppFn.isConstOf parent && first.getAppArgs.size == 6 do
    throwError "First conjunct is not direct six-argument properness parent"
  let args := first.getAppArgs
  unless canon args[1]! == canon expectedF do throwError "Parent F argument differs from actual frozen F"
  unless args[2]! == Expr.bvar (typeBinders - 1 - 3) do throwError "Parent V argument differs from original V"
  unless args[3]! == Expr.bvar (typeBinders - 1 - 4) do throwError "Parent nonempty argument differs from original hV"
  let output := Json.mkObj [("declaration", toJson target.toString),
    ("telescope_binders", toJson typeBinders), ("first_conjunct", toJson "SourceProper actual F"),
    ("first_provider", toJson parent.toString), ("arity", toJson args.size),
    ("first_conclusion_F_alpha_equals_frozen_type_F", toJson true),
    ("parent_F_alpha_equals_frozen_type_F", toJson true),
    ("parent_V_exact_original_bvar", toJson true), ("parent_hV_exact_original_bvar", toJson true),
    ("method", toJson "Aligned original theorem telescopes; expose proof lets only to inspect first constructor; alpha compare F with frozen actual imported TYPE let value. No defeq/proof irrelevance/equality substitution.")]
  liftIO do
    let file ← IO.FS.Handle.mk "tmp/online-b4-cumulative-producer-body-20261012/imported-operand-flow-v2.json" .writeNew
    file.putStr (output.pretty ++ "\n")
