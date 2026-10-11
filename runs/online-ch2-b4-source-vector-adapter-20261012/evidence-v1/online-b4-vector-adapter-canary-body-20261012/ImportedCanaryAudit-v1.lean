import VectorAdapterCanaries
import Lean.Util.FoldConsts
open Lean Elab Command
set_option pp.fullNames true
#check BanditRL.Tests.OnlineStrongConvexSourceSubgradientCanary.supNorm_nonzero_support
#print axioms BanditRL.Tests.OnlineStrongConvexSourceSubgradientCanary.supNorm_nonzero_support
#check BanditRL.Tests.OnlineStrongConvexSourceSubgradientCanary.scaledCoordinates_discriminate_wrong_norm
#print axioms BanditRL.Tests.OnlineStrongConvexSourceSubgradientCanary.scaledCoordinates_discriminate_wrong_norm
run_cmd do
  let env ← getEnv
  let ns := `BanditRL.Tests.OnlineStrongConvexSourceSubgradientCanary
  let target := `BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth
  let names := #[ns ++ `supNorm_nonzero_support, ns ++ `scaledCoordinates_discriminate_wrong_norm]
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let rec expose : Nat → Expr → Expr
    | 0, e => e
    | n + 1, .letE _ _ v b _ => expose n (b.instantiate1 v)
    | n + 1, .mdata _ b => expose n b
    | _, e => e
  let mut rows : Array Json := #[]
  for i in [:names.size] do
    let name := names[i]!
    let some info := env.find? name | throwError "Missing actual imported canary"
    let some value := info.value? (allowOpaque := true) | throwError "Missing actual proof"
    let outer := expose 1000 value
    unless outer.getAppFn.isConstOf ``And.intro && outer.getAppArgs.size == 4 do
      throwError "Expected outer first conjunction constructor"
    let first := expose 1000 outer.getAppArgs[2]!
    unless first.getAppFn.isConstOf target do
      throwError "First conjunction provider is not direct adapter application"
    let args := first.getAppArgs
    unless args.size == 19 do throwError "Unexpected adapter arity"
    let coordinate := if i == 0 then ns ++ `coordinates else ns ++ `scaledCoordinates
    let gradient := if i == 0 then ns ++ `supportVector else ns ++ `scaledSupportVector
    let checks := #[(4, coordinate), (5, ns ++ `objective), (6, ns ++ `feasible),
      (13, ns ++ `base), (15, gradient), (17, ns ++ `query)]
    for (idx, expected) in checks do
      unless args[idx]!.isConstOf expected do
        throwError "Concrete adapter argument {idx} differs from frozen context: expected {expected}"
    let fd := deps first
    unless fd.contains target.toString do throwError "Missing genuine core dependency"
    rows := rows.push <| Json.mkObj [("declaration", toJson name.toString),
      ("TYPE", toJson (deps info.type)), ("VALUE", toJson (deps value)),
      ("first_conjunction_VALUE", toJson fd),
      ("first_provider", toJson target.toString), ("first_provider_arity", toJson args.size),
      ("checked_concrete_arguments", toJson (checks.map fun (i,n) => (i,n.toString))),
      ("dimension_argument_small_repr", toJson (reprStr args[3]!)),
      ("lambda_argument_small_repr", toJson (reprStr args[7]!))]
  liftIO <| IO.FS.writeFile "tmp/online-b4-vector-adapter-canary-body-20261012/imported-canary-type-value-v1.json" ((toJson rows).pretty ++ "\n")
