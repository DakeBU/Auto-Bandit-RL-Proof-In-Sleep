import VectorAdapterCandidate
import Lean.Util.FoldConsts
open Lean Elab Command
set_option pp.fullNames true
#check BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth
#print axioms BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth
run_cmd do
  let env ← getEnv
  let name := `BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth
  let some info := env.find? name | throwError "Missing imported declaration"
  let some value := info.value? (allowOpaque := true) | throwError "Missing proof value"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let vd := deps value
  unless vd.contains "BanditRL.OnlineConvex.stronglyConvex_support_growth" do
    throwError "Required actual support-growth dependency absent"
  unless vd.contains "LinearMap.toContinuousLinearMap" do
    throwError "Required internal finite-dimensional continuity adapter absent"
  unless vd.contains "LinearEquiv.finiteDimensional" do
    throwError "Required internal finite-dimensionality derivation absent"
  let row := Json.mkObj [("declaration", toJson name.toString),
    ("TYPE", toJson (deps info.type)), ("VALUE", toJson vd),
    ("elaborated_type", toJson ((← PrettyPrinter.ppExpr info.type).pretty)),
    ("elaborated_proof", toJson ((← PrettyPrinter.ppExpr value).pretty))]
  liftIO <| IO.FS.writeFile "tmp/online-b4-vector-adapter-body-20261012/imported-type-value-v1.json" (row.pretty ++ "\n")
