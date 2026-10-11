import Tests.OnlineStrongConvexSupportCanary
import Lean.Util.FoldConsts
open Lean Elab Command
set_option pp.proofs true
set_option pp.fullNames true
#check BanditRL.Tests.OnlineStrongConvexSupportCanary.nonzero_point_nonzero_support_sharp
#print axioms BanditRL.Tests.OnlineStrongConvexSupportCanary.nonzero_point_nonzero_support_sharp
#check BanditRL.Tests.OnlineStrongConvexSupportCanary.boundary_nonzero_support_extended_domain
#print axioms BanditRL.Tests.OnlineStrongConvexSupportCanary.boundary_nonzero_support_extended_domain
run_cmd do
  let env ← getEnv
  let names := #[`BanditRL.Tests.OnlineStrongConvexSupportCanary.nonzero_point_nonzero_support_sharp,
    `BanditRL.Tests.OnlineStrongConvexSupportCanary.boundary_nonzero_support_extended_domain]
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.find? name | throwError "Missing compiled target"
    let some value := info.value? (allowOpaque := true) | throwError "Missing proof"
    let vd := deps value
    unless vd.contains "BanditRL.OnlineConvex.stronglyConvex_support_growth" do
      throwError "Actual public consumer VALUE missing production endpoint"
    let rec expose : Nat → Expr → Expr
      | 0, e => e
      | n + 1, .letE _ _ v b _ => expose n (b.instantiate1 v)
      | n + 1, .mdata _ b => expose n b
      | _, e => e
    let outer := expose 1000 value
    unless outer.getAppFn.isConstOf ``And.intro && outer.getAppArgs.size == 4 do
      throwError "Expected actual first conjunction constructor after zeta reduction"
    let first := outer.getAppArgs[2]!
    let fd := deps first
    unless fd.contains "BanditRL.OnlineConvex.stronglyConvex_support_growth" do
      throwError "First conjunction VALUE does not call required production endpoint"
    rows := rows.push <| Json.mkObj [("declaration", toJson name.toString),
      ("TYPE", toJson (deps info.type)), ("VALUE", toJson vd),
      ("first_conjunction_VALUE", toJson fd), ("first_conjunction_constructor", toJson "And.intro after let/mdata reduction")]
  liftIO <| IO.FS.writeFile "tmp/online-b4-support-canonical-canary-audit-20261011/compiled-type-value-v1.json" ((toJson rows).pretty ++ "\n")
