import BanditRLProof.OnlineStrongConvexMinimum

#print axioms BanditRL.OnlineConvex.stronglyConvex_minimum_growth
run_cmd do
  let env ← Lean.getEnv
  let name := `BanditRL.OnlineConvex.stronglyConvex_minimum_growth
  let some ci := env.find? name | throwError "missing imported theorem"
  let some idx := env.getModuleIdxFor? name | throwError "not an imported declaration"
  let moduleName := env.header.moduleNames[idx.toNat]!
  let names (e : Lean.Expr) := e.getUsedConstantsAsSet.toArray.map (fun n => Lean.Json.str n.toString)
  let some value := ci.value? (allowOpaque := true) | throwError "missing actual value"
  let report := Lean.Json.mkObj [
    ("declaration", Lean.Json.str ci.name.toString),
    ("module", Lean.Json.str moduleName.toString),
    ("TYPE", Lean.Json.arr (names ci.type)),
    ("VALUE", Lean.Json.arr (names value)),
    ("type_expression_repr", Lean.Json.str (toString (repr ci.type)))]
  Lean.logInfo ("IMPORTED_PRODUCTION_JSON=" ++ report.compress)
