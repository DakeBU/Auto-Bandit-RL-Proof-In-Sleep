"""Freeze actual final source/reader inputs after separately observed package gates."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(name,x):
    with (run/name).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
for label in ['root-v2-02','Tests-v2-02','full-harness-v2-02','contributor-exact-v2-03',
    'graph-verify-v2-01','site-final01-build','site-final01-check','registry-final01','browser-final01',
    'review-history-v2-01','current-diff-v2-01','candidate-frontier-refresh-v2','candidate-frontier-shadow-v2']:
    assert load(run/(label+'-exit.json'))['exit_code']==0,label
contributor=(run/'contributor-exact-v2-03.log').read_text(encoding='utf-8')
assert 'affected production paths: 7' in contributor and 'changed contribution contracts: 1' in contributor
assert 'Contributor contract passed.' in contributor and 'N/A' not in contributor
site=Path('tmp/online-ogd-migration-site-final01')
manifest=load(site/'site-manifest.json')
assert manifest['source_dirty'] is False and manifest['lean_verified'] is True
registry=load(run/'registry-final01.json')
assert registry['status']=='passed' and len(registry['checks'])==14 and registry['preserved_base_node_ids_and_urls']==10790
packet='''Required distinct source reviewer, GPT-6 Astra / medium. Final OGD source-repair package/reader review, not chapter/book acceptance. Search for mismatch rather than confirming root. Read final-reader-inputs-v2.json exact raw rows and independently rehash. Original source-contract v1 is rejected for broad source coverage, not false proof bodies. V2 distinct neutral decoder and source contract accepted; actual12 public bodies/2 predicates,30 canaries/7 definitions and old16 declarations/8 definitions separately reviewed. Original16 headers/all old code tokens are unchanged. Both old modules now explicitly qualify stronger RegularLoss in COMMENTS ONLY; exact authorized pre-integration snapshots preserve original receipt bytes. Recheck historical 716 raw rows via review-history-audit-v2.json with explicit snapshot resolution rather than asserting all live originals unchanged.

New SourceRegularLoss: convex on V plus supplied ambient extension differentiable on arbitrary open U containing V; U need not be convex. source_to_feasible actually derives every feasible ambient derivative. Thin V restrictions do not determine a gradient; no extension existence/independence theorem. Same complete-Hilbert generalization, finite-Euclidean source specialization. Genuine affine regularity/gradient identifies the SAME original projection step; both one-step inequalities, actual fixed induction/variable weighted telescope, positive eta denominators, T0 fixed cancellation/T1 variable/zero diameter and tuned positive DGT are retained. No bounded premise in sharp fixed bound. Variable eta(T-1) denominators and negative terminal are explicit; bounded Metric.diam interface separate. Tuned gradient bounds refer to the same single horizon-prescribed run for all comparators.

Actual max(exp(-x),y) Euclidean-plane canary: supplied U={y<exp(-x)} is open/nonconvex, feasible axis unbounded, actual gradient=-e0, next=e0, positive regret1-exp(-2), terminal1. It does NOT formally prove all alternative convex differentiability neighborhoods fail. The mathematical counterexample is independent mathematical review, distinct from compiled canary. Active interval/tuned/variable paths and zero-round/zero-diameter/future-prefix tests actually instantiate proved endpoints; tuned interval test does not assert every iterate clips.75 unique actual named #check/#print axioms are standard3-or-none.12 native public safe-fence guards use actual Lean hypothesis fragments; original draft fence path metadata is only header capture, not an executed safe-verify gate.

Root9087/Tests9228 and full harness466tests7existing skips passed; root/Tests/full rerun after variable COMMENT delta. Exported compiled graph has38 explicit scope nodes and33 required proof-value pairs, separate from teaching route. It was exported before the later variable COMMENT annotation; no code/statement/proof token changed and the fresh integrated builds passed. Actual contributor exact PR153 base64e25407 gate7 productionpaths/one manifest passed AFTER commit. Earlier precommit N/A is NOT acceptance, then real gate02 rejected Tests and unchanged variable path; repair removes Tests from production scope and records tested paths in verification, genuinely qualifies retained variable API. Main-relative gate still reports21 historical missing paths; two selected old OGD files independently migrated, other24 of historical26 audit not accepted by this receipt (three manifest-covered paths are not automatically semantic acceptance).

Original full diff check failed on raw logs and four immutable draft/type/snapshot blank EOFs; scoped check covers every other changed path, including all production proofs/JSON/scripts. Preserve every failed canary/API/protocol/helper/contributor/help attempt and version1 rejection. Native phases/files are distinct from actual runtime Goal. Full harness target-drift execution template26UNSET fields remains NOT scientific experiment completion despite check success. No single-runtime-enforces-all-paper-workflow claim.

Inspect generated source reader /chapters/online-ogd and registry:14 new canonical nodes/native hashes,10790 old IDs/URLs retained, all Book maps share the same Lean graph; old historical declarations remain linked and explicitly qualified. Five source cards (Prop2.11, Lemma2.12, fixed2.13, Eq2.1, variable2.13), not14 independently printed results. Projection card has no eta/horizon/loss/regret premise; one-step card no cumulative horizon. Source printed12–15/PDF24–27, source game printed8/PDF20 and first-order printed11/PDF23. Current site is clean candidate with lean_verified and its exact source_commit in manifest. Root visually inspected only first viewport; lower-fold text independently checked, no lower pixel claim. Source inventory remains historical draft for Prop2.11/Lemma2.12 until additive accepted overlay after this gate. Chapter2 mandatory count remains null, incomplete; Chapters3–16 unenumerated and mandatory. Whole Goal ACTIVE; main/live unchanged; stacked draft PR delivery still pending. No human/external model review; requested Astra/medium not independently attested.

Write ONLY final-reader-review-v2.md and final-reader-receipt-v2.json here. Include seven semantic slots, required repairs, remaining gaps, exact reviewed_files raw SHA inventory, report path and SHA. Do not edit inputs, forge chapter completion or downgrade missing scope.'''
write('final-reader-packet-v2.md',packet)
surfaces=['BanditRLProof.lean','BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentVariable.lean',
    'BanditRLProof/OnlineGradientDescentSource.lean','Tests.lean','Tests/OnlineGradientDescentSourceCanary.lean',
    'docs/contracts/online-book-v1/coverage.json','docs/contracts/online-book-v1/source-inventory.json',
    'research-wiki/contribution-contracts/ONLINE-OGD-MIGRATION-20261005.json',
    'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
    'website/scripts/build_site.py','website/scripts/check_site.py','website/static/lean-graph.js']
paths=set(surfaces)
for n in ['source-contract-receipt-v1.json','source-contract-receipt-v2.json','public-body-receipt-v2.json']:
    paths.update(x['path'] for x in load(run/n)['reviewed_files'])
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file() and p.name not in
    ['final-reader-inputs-v2.json','final-reader-review-v2.md','final-reader-receipt-v2.json'])
for version in [1,2]:paths.update(p.as_posix() for p in Path('docs/contracts/online-ogd-migration-v'+str(version)).rglob('*') if p.is_file())
paths.update((site/n).as_posix() for n in ['site-manifest.json','books/registry.json','chapters/online-ogd/index.html'])
paths.add('tmp/online-ogd-migration-reader-final01.png');paths.add('runs/active_frontier.json')
for p in paths:assert Path(p).is_file(),p
write('final-reader-inputs-v2.json',dict(scope='OGD source repair and retained stronger interfaces only; Chapter2/book incomplete',
    canonical_surfaces=surfaces,site_commit=manifest['source_commit'],site_source_clean=True,
    public_proofs=12,public_definitions=2,old_audited_theorems=16,canary_theorems=30,
    actual_axiom_names=75,public_registry_nodes=14,preserved_registry_nodes=10790,
    rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Frozen final reader:',len(paths),'raw rows; clean source commit',manifest['source_commit'])
