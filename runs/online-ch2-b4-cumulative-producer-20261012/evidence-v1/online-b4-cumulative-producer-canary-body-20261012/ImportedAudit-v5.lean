import CumulativeProducerCanaries
import Lean.Util.FoldConsts
open Lean Elab Command
#print axioms BanditRL.Tests.OnlineCumulativeStrongConvexCanary.twoLoss_actual_producer_tight_support
#print axioms BanditRL.Tests.OnlineCumulativeStrongConvexCanary.emptyPrefix_zeroCurvature_actual_producer
run_cmd do
  let env ← getEnv
  let ns := `BanditRL.Tests.OnlineCumulativeStrongConvexCanary
  let producer := `BanditRL.OnlineConvex.cumulative_regularizer_source_strongConvex
  let growth := `BanditRL.OnlineConvex.stronglyConvex_support_growth
  let some growthIdx := env.getModuleIdxFor? growth | throwError "Growth has no imported module origin"
  let some producerIdx := env.getModuleIdxFor? producer | throwError "Producer has no imported module origin"
  let growthMod := env.header.moduleNames[growthIdx.toNat]!
  let producerMod := env.header.moduleNames[producerIdx.toNat]!
  unless growthMod == `BanditRLProof.OnlineStrongConvexSupport && producerMod == `CumulativeProducerCandidate do
    throwError "Provider module binding mismatch"
  let growthOlean ← liftIO <| findOLean growthMod
  let producerOlean ← liftIO <| findOLean producerMod
  let names := #[ns ++ `twoLoss_actual_producer_tight_support, ns ++ `emptyPrefix_zeroCurvature_actual_producer]
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let rec expose : Nat → Expr → Expr
    | 0,e => e
    | n+1,.letE _ _ v b _ => expose n (b.instantiate1 v)
    | n+1,.mdata _ b => expose n b
    | n+1,e => if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then expose n e.getAppArgs[1]! else e
  let rec canon : Expr → Expr
    | .forallE _ t b i => .forallE .anonymous (canon t) (canon b) i
    | .lam _ t b i => .lam .anonymous (canon t) (canon b) i
    | .letE _ t v b n => .letE .anonymous (canon t) (canon v) (canon b) n
    | .app f a => .app (canon f) (canon a)
    | .mdata _ e => canon e
    | .proj s i e => .proj s i (canon e)
    | e => e
  let rec projection : Nat → Expr → Array Nat × Expr
    | 0,e => (#[],e)
    | n+1,e =>
      let e := expose 1000 e
      match e with
      | .proj ``And i b => let (p,b) := projection n b; (p.push i,b)
      | _ =>
        let args := e.getAppArgs
        if args.size == 3 && e.getAppFn.isConstOf ``And.left then
          let (p,b) := projection n args[2]!; (p.push 0,b)
        else if args.size == 3 && e.getAppFn.isConstOf ``And.right then
          let (p,b) := projection n args[2]!; (p.push 1,b)
        else (#[],e)
  let rec hasDomainProjection (pkg : Expr) (e : Expr) : Bool :=
    let (p,b) := projection 10 e
    if p == #[1,0] && canon b == canon pkg then true else
      match e with
      | .app f a => hasDomainProjection pkg f || hasDomainProjection pkg a
      | .lam _ t b _ | .forallE _ t b _ => hasDomainProjection pkg t || hasDomainProjection pkg b
      | .letE _ t v b _ => hasDomainProjection pkg t || hasDomainProjection pkg v || hasDomainProjection pkg b
      | .mdata _ b | .proj _ _ b => hasDomainProjection pkg b
      | _ => false
  let numeral := fun (e : Expr) (n : Nat) => e == mkNatLit n ||
    (e.getAppFn.isConstOf ``OfNat.ofNat && e.getAppArgs.size == 3 && e.getAppArgs[1]! == mkRawNatLit n)
  let mut rows : Array Json := #[]
  for i in [:names.size] do
    let name := names[i]!
    let some ci := env.find? name | throwError "Missing canary"
    let some value := ci.value? (allowOpaque := true) | throwError "Missing value"
    let outer := expose 1000 value
    unless outer.getAppFn.isConstOf ``And.intro && outer.getAppArgs.size == 4 do throwError "No outer conjunction"
    let first := expose 1000 outer.getAppArgs[2]!
    unless first.getAppFn.isConstOf growth && first.getAppArgs.size == 17 do throwError "No direct growth provider arity17"
    let remainder := expose 1000 outer.getAppArgs[3]!
    unless remainder.getAppFn.isConstOf ``And.intro && remainder.getAppArgs.size == 4 do throwError "No second conjunction"
    let pkg := expose 1000 remainder.getAppArgs[2]!
    unless pkg.getAppFn.isConstOf producer && pkg.getAppArgs.size == 14 do throwError "Second conjunction not direct producer package"
    let ga := first.getAppArgs
    let pa := pkg.getAppArgs
    let obj := ns ++ (if i == 0 then `twoObjective else `emptyObjective)
    let psi := ns ++ (if i == 0 then `quadraticRegularizer else `linearRegularizer)
    let loss := ns ++ (if i == 0 then `twoLoss else `emptyLoss)
    let support := ns ++ (if i == 0 then `doubleSupport else `unitSupport)
    let gc := #[(3,obj),(4,ns ++ `feasible),(13,support)]
    let pc := #[(3,ns ++ `feasible),(5,psi),(6,loss)]
    for (j,n) in gc do unless ga[j]!.isConstOf n do throwError "Growth operand {j} differs from {n}"
    for (j,n) in pc do unless pa[j]!.isConstOf n do throwError "Producer operand {j} differs from {n}"
    unless numeral ga[5]! (if i == 0 then 1 else 0) && numeral ga[11]! 0 && numeral ga[15]! 1 do
      throwError "Growth coefficient/base/query numerals differ"
    unless numeral pa[7]! (if i == 0 then 2 else 0) && numeral pa[8]! (if i == 0 then 1 else 0) do
      throwError "Producer prefix/coefficient numerals differ"
    let (properPath,properBase) := projection 10 ga[6]!
    let (strongPath,strongBase) := projection 10 ga[10]!
    unless properPath == #[0] && canon properBase == canon pkg do throwError "Properness not projection of identical actual producer package"
    unless strongPath == #[1,1,1] && canon strongBase == canon pkg do throwError "Curvature not projection of identical actual producer package"
    unless hasDomainProjection pkg ga[8]! do throwError "Domain proof lacks actual identical package domain projection"
    let some idx := env.getModuleIdxFor? name | throwError "Missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == `CumulativeProducerCanaries do throwError "Unexpected canary import binding"
    let op ← liftIO <| findOLean mod
    rows := rows.push <| Json.mkObj [("declaration",toJson name.toString),
      ("TYPE",toJson (deps ci.type)),("VALUE",toJson (deps value)),
      ("growth_module",toJson growthMod.toString),("growth_resolved_olean",toJson growthOlean.toString),
      ("producer_module",toJson producerMod.toString),("producer_resolved_olean",toJson producerOlean.toString),
      ("first_provider",toJson growth.toString),("first_provider_arity",toJson ga.size),
      ("second_provider",toJson producer.toString),("second_provider_arity",toJson pa.size),
      ("growth_named_operands",toJson (gc.map fun (j,n) => (j,n.toString))),
      ("producer_named_operands",toJson (pc.map fun (j,n) => (j,n.toString))),
      ("growth_lambda_small_repr",toJson (reprStr ga[5]!)),
      ("growth_base_small_repr",toJson (reprStr ga[11]!)),("growth_query_small_repr",toJson (reprStr ga[15]!)),
      ("producer_prefix_small_repr",toJson (reprStr pa[7]!)),("producer_lambda_small_repr",toJson (reprStr pa[8]!)),
      ("properness_projection_same_package",toJson true),("curvature_projection_same_package",toJson true),
      ("domain_projection_same_package_found",toJson true),("module",toJson mod.toString),("resolved_olean",toJson op.toString)]
  liftIO do
    let file ← IO.FS.Handle.mk "tmp/online-b4-cumulative-producer-canary-body-20261012/imported-provider-v5.json" .writeNew
    file.putStr ((toJson rows).pretty ++ "\n")
