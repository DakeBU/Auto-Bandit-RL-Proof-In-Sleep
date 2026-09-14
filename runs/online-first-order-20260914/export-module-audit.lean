import tools.ProofGraphExport

open Lean

/-- Audit-only use of the existing exporter on a module import closure. -/
unsafe def exportFirstOrderModuleAudit : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `BanditRLProof.OnlineConvexFirstOrder }] {}
    (loadExts := true)
  let graph ← BanditRLProof.ProofGraph.exportJson env
  IO.FS.writeFile "tmp/online-first-order-module-graph-raw.json" (graph.compress ++ "\n")

#eval exportFirstOrderModuleAudit
