import Tests.OnlineStrongConvexMinimumCanary
import Lean.Util.FoldConsts
open Lean Elab Command
set_option pp.proofs true
set_option pp.fullNames true
#print BanditRL.Tests.OnlineStrongConvexMinimumCanary.square_two_exact_growth
#print axioms BanditRL.Tests.OnlineStrongConvexMinimumCanary.square_two_exact_growth
#print BanditRL.Tests.OnlineStrongConvexMinimumCanary.interval_zero_extended_domain
#print axioms BanditRL.Tests.OnlineStrongConvexMinimumCanary.interval_zero_extended_domain
run_cmd do
  let env ← getEnv
  let names := #[`BanditRL.Tests.OnlineStrongConvexMinimumCanary.square_two_exact_growth,
    `BanditRL.Tests.OnlineStrongConvexMinimumCanary.interval_zero_extended_domain]
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.find? name | throwError "Missing compiled target"
    let some value := info.value? (allowOpaque := true) | throwError "Missing proof"
    let vd := deps value
    unless vd.contains "BanditRL.OnlineConvex.stronglyConvex_minimum_growth" do
      throwError "Actual public consumer VALUE missing production endpoint"
    rows := rows.push <| Json.mkObj [("declaration", toJson name.toString),
      ("TYPE", toJson (deps info.type)), ("VALUE", toJson vd)]
  liftIO <| IO.FS.writeFile "tmp/online-ch2-b4-strong-convex-growth-installed-audit-20261011/compiled-type-value-v1.json" ((toJson rows).pretty ++ "\n")
