"""Freeze the final reader only after independently observed current package gates."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
gates=['root-v1-01','Tests-v1-01','full-harness-v1-02','contributor-exact-v1-01',
    'site-final01-build','site-final01-check','registry-final01','browser-final01','review-history-v1-02',
    'scoped-diff-v1-01','candidate-frontier-refresh-v1','candidate-frontier-shadow-v1']
for n in gates:assert load(run/(n+'-exit.json'))['exit_code']==0,n
full=(run/'full-harness-v1-02.log').read_text(encoding='utf-8')
assert 'Ran 466 tests' in full and 'OK (skipped=7)' in full and 'check passed' in full
assert load(run/'full-harness-v1-01-exit.json')['exit_code']!=0
contributor=(run/'contributor-exact-v1-01.log').read_text(encoding='utf-8')
assert 'affected production paths: 4' in contributor and 'changed contribution contracts: 1' in contributor
assert 'Contributor contract passed.' in contributor and 'N/A' not in contributor
site=Path('tmp/online-ftl-migration-site-final01');manifest=load(site/'site-manifest.json')
assert manifest['source_dirty'] is False and manifest['lean_verified'] is True
registry=load(run/'registry-final01.json')
assert registry['status']=='passed' and len(registry['checks'])==10
packet='''Required distinct final source/reader/package review, GPT-6 Astra / medium. Search for mismatch rather than confirming root. Rehash exact raw final-reader-inputs-v1.json rows. This one retained FTL Example2.10 package reuses seven public proof bodies and three definitions, two public nondegenerate canaries; ZERO new proof or registry node claims. Contract and actual-body reviews are separate accepted-with-explicit-delta verdicts, independently root-hash-checked. Actual recursive coefficient prefix, strict-past prediction, feasible output plus historical minimization, failure parity/prediction and exact played-loss regret are genuine producer bodies. Source printed12/PDF24, Lean0=source1, initial coefficient-1/2, later oddLean+1/evenLean-1. Every feasible x0 and T>=1; exact comparator0 regret T-1-x0/2 >=T-3/2. Fixed x0 causality, concrete positive-time zero-prefix -1 tie choice, source failure no later ties. Historical inequality alone permits arbitrary initial x0 at0 because sums vanish; feasible argmin combines membership. No universal all-algorithm lower bound/optimal-comparator equality/expectation/randomized-law/initialization-selection claim.

Two body-review-required reader corrections are implemented: prefix highlight displays equality of predictions under strict-prefix stream equality, not minimization; minimization highlight displays the actual objective inequality and explicitly separates first-round feasibility. Same three old highlights/teaching route, all URLs/IDs and all other reader subtrees unchanged. Source card/algorithm/notes explicitly carry indexing, initial choice, tie and metric boundaries. Public module only source-qualification COMMENT changed, every existing native header and all definition/proof code tokens unchanged; original module/canary and pre-integration Book raw bytes preserved. Earlier source/body and previous accepted OGD final-reader raw rows resolve through explicit exact snapshots (766 rows), not silent live drift. Previous OGD reader subtree and its accepted reports/receipts unchanged.

Fresh actual public body/canary elaborations,12 uniquely named #check/#print axioms standard3-or-none and7 actual safe guards passed. Fresh combined root9087/Tests9228 passed after corrected comment. Reused actual compiled full shared-root graph from previous verified OGD package:10 unchanged FTL nodes/818actualedges/361boundary/six required proof-value pairs. Only Lean delta from exact verified stacked base4b55 is comment; same root/toolchain and code tokens. NO new graph export or canary graph export; actual proof-term versus teaching edges distinct. Full harness second pass466tests7existing skips passed. First full pass failed solely because existing test required literal not completion of Chapter2 phrase; exact phrase restored and failed log preserved, no test/proof weakening. Native workflow phases and role/prompt/source files are not one universally enforcing runtime; target-drift execution-template26UNSET fields remain NOT scientific experiment completion.

Failure history is mandatory: original raw snapshot01 added EOF, trial role lower-worker/status passed were invalid enums, first source COMMENT sign shorthand contained nested-comment opener and unchanged-code assertion rejected it before public build. Exact failed scripts/module/logs retained; corrected prose/header/code, lower/compiled enums and raw write_bytes repair without statement weakening. Original full git whitespace gate and scoped exception inventory must be reported literally; only task raw logs plus explicit exact immutable snapshots may be excepted, all production/JSON/scripts/other documents checked. Clean site build lean_verified uses applicable combined gates and exact source_commit; generated canonical_site never edited. Registry10 nodes/native hashes match uniquely, all inherited IDs/URLs remain. Actual isolated headless Edge first viewport observed; lower-fold text may be independently read but no unobserved lower pixel claim.

Exact stacked contributor base is OPENdraft PR154 head4b55f5ebebb370ebe9e173b9bf5155b97a2e3998, unmerged. Actual committed four productionpaths/one current contract gate passed. Main-relative migration now separately recorded: this one FTL old path is independently reviewed; other historical paths still mandatory and no aggregate manifest coverage equals their source acceptance. Chapter2 has32 numbered entries/twoalgorithmboxes and18 unnumbered draftgroups, not a frozen52-obligation or completion count; mandatory_totalnull. Source full enumeration and exact remaining old production signatures/necessary dependencies still required. Optional independent Problems2.1–2.5 separated, formal main-text results with exercise proofs not omitted. Chapter1 legacy migration and Chapters3–16 mandatory; whole Goal ACTIVE. No main merge/live publication or human/external model review; requested model/medium not independently attested. Draft PR delivery remains pending after package decision.

Write ONLY final-reader-review-v1.md and final-reader-receipt-v1.json here, with seven semantic slots, required_repairs, remaining required gaps, exact reviewed_files raw SHA inventory and report path/SHA. Do not edit inputs or certify chapter/book/Goal/main/live. Include per-repair reader disposition and reused-graph evidence limits.'''
write('final-reader-packet-v1.md',packet)
surfaces=['BanditRLProof/OnlineFTLFailure.lean','Tests/OnlineFTLFailureCanary.lean','BanditRLProof.lean','Tests.lean',
    'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
    'research-wiki/contribution-contracts/ONLINE-FTL-MIGRATION-20261005.json',
    'docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json',
    'website/scripts/build_site.py','website/scripts/check_site.py','lean-toolchain','lakefile.lean','runs/active_frontier.json']
paths=set(surfaces)
paths.update(r['path'] for r in load(run/'public-body-inputs-v1.json')['rows'])
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file() and p.name not in ['final-reader-inputs-v1.json','final-reader-review-v1.md','final-reader-receipt-v1.json'])
paths.update(p.as_posix() for p in Path('runs/online-ch2-enumeration-20261005').rglob('*') if p.is_file())
paths.update((site/n).as_posix() for n in ['site-manifest.json','books/registry.json','chapters/online-ftl-failure/index.html'])
paths.add('tmp/online-ftl-migration-reader-final01.png')
write('final-reader-inputs-v1.json',dict(scope='retained FTL source migration only; Chapter2/book incomplete',
    canonical_surfaces=surfaces,site_commit=manifest['source_commit'],site_source_clean=True,
    retained_proofs=7,definitions=3,new_proofs=0,canary_proofs=2,registry_scope_nodes=10,
    preserved_registry_nodes=registry['preserved_base_node_ids_and_urls'],
    rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Final FTL source/reader inputs frozen:',len(paths),'raw rows, clean site source',manifest['source_commit'])
