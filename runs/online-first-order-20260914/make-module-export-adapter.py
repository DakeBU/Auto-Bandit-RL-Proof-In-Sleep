from pathlib import Path
import hashlib,json
source=Path('tools/ProofGraphExport.lean').read_text(encoding='utf-8-sig')
marker='unsafe def main (args : List String) : IO UInt32 := do'
assert source.count(marker)==1
prefix=source.split(marker)[0]
entry=r'''unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [moduleText, output] =>
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let env ← Lean.importModules #[{ module := moduleText.toName }] {} (loadExts := true)
    let graph ← BanditRLProof.ProofGraph.exportJson env
    let wrapped := Json.mkObj [
      ("actual_import_root", toJson moduleText),
      ("scope", "module-import-closure-not-full-project"),
      ("graph", graph)]
    IO.FS.writeFile output (wrapped.compress ++ "\n")
    return 0
  | _ =>
    IO.eprintln "usage: module-export MODULE OUTPUT.json"
    return 2
'''
p=Path('tmp/proof-graph-module-adapter.lean');p.write_text(prefix+entry,encoding='utf-8')
receipt={'base_exporter':'tools/ProofGraphExport.lean','base_source_lf_sha256':hashlib.sha256(source.encode()).hexdigest(),'unchanged_prefix_lf_sha256':hashlib.sha256(prefix.encode()).hexdigest(),'adapter_lf_sha256':hashlib.sha256((prefix+entry).encode()).hexdigest(),'change':'Entry point only: module name argument and explicit module-scope wrapper; all extraction logic copied exactly from the current exporter','output':str(p),'not_yet_validated':True}
Path('runs/online-first-order-20260914/module-adapter-generation.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
