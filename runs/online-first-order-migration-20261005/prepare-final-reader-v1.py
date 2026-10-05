"""Freeze actual final reader/package surfaces after applicable combined and site gates."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;site=Path('tmp/online-first-order-migration-site-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
gates=['root-v1-01','Tests-v1-01','full-harness-v1-01','contributor-exact-v1-01','scoped-diff-v1-01',
 'site-build-v1','site-check-v1','registry-v1-01','browser-v1-01','history-bindings-v1-01',
 'public-axioms-v1-01','candidate-frontier-shadow-v1']
for n in gates:assert load(run/(n+'-exit.json'))['exit_code']==0,n
raw=(run/'full-harness-v1-01.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
reg=load(run/'registry-v1.json');assert reg['new_registry_nodes']==0 and reg['preserved_base_node_ids_and_urls']==10806
manifest=load(site/'site-manifest.json');assert manifest['source_dirty'] is False and manifest['lean_verified'] is True
write('browser-v1-observation.md','Actual task-owned isolated headless Edge screenshot viewed by root at1440x1800 (tool view resized1408x1760). First viewport shows shared Books navigation, supporting-gradients title, current global noBottom/ambient-interior/canonical-local summary, explicit local-route versus textbook-chapter completion status box,3learning goals and exactv10/printed11PDF23 source card. No overlap/clipping of these visible regions observed. Full lower source statement/helper notes/OGD relationship are bound as actual HTML below; no claim to have visually viewed unobserved lower pixels or a physical user device. Task server stopped; screenshot/profile preserved.')
write('integrated-gates-overlay-v1.json',dict(status='passed-scoped-integrated-gates-final-semantic-review-pending',actual_passed_gates=gates,
 root_jobs=9088,Tests_jobs=9230,full_tests=466,existing_skips=7,public_axiom_names=12,native_guards=3,
 retained_proofs=3,new_proofs=0,new_registry_nodes=0,preserved_old_IDs_URLs=10806,actual_scoped_graph_nodes=3,actual_scoped_graph_edges=416,
 site_source_commit=manifest['source_commit'],source_dirty=False,lean_verified=True,prior_raw_bindings_checked=4190,
 exact_stacked_base='a6607d8213860619965c7018e4dd2effff58422a',stacked_base_PR=157,main_relative_gate='FAIL15legacyproductioncontracts',
 full_whitespace_gate='FAILexactrawlogs',scoped_whitespace_gate='PASSenumeratedrawexceptions',
 candidate_manifest_pending_fields_superseded_additively=True,chapter_complete=False,goal_complete=False,merged=False,live=False))
write('final-reader-packet-v1.md','''Distinct final SOURCE/READER/PACKAGE review requested GPT-6 Astra / medium. Independently hash every final-reader-inputs-v1.json row; resolve current/prior raw review rows via history-binding-audit-v1.json and exact historical snapshot chains (4190 independently rechecked rows). Seek mismatch, not confirmation. Source Theorem2.7 p11PDF23 and retained three bodies/zero definitions/new proof code/registry nodes only. Source terminal noBottom/epigraph convexity/ambient interior/canonical F derivative/all-y, outside top retained. finitePart_eventually local representation helper with no convexity/derivative; convex_gradient_lower_bound everywhere-real ConvexOn V/x,y memberships/ambient derivative at x, no open V/local EReal bridge. Complete Hilbert-space generality explicitly extends source Euclidean scope. No global identification of f with F or globally convex F. Three actual headers/all code tokens/byte-exact canary preserved; comment only.

Independently confirm all four required reader corrections on actual selected JSON/chapter/module HTML: two helper classifications; real helper exact scope/no open V/no EReal bridge; stronger historical RegularLoss OGD (convex and differentiable on convex open U) versus separate arbitrary-open source_to_feasible/first_order adapter; canonical F/global noBottom/ambient interior/local embedding/all-y top together. Actual old and source-compatible OGD module bytes supplied; no predicate equivalence/extension-independence claim. Every other structured Book subtree unchanged. Same3 representative links/3notation/3highlights, one printed source terminal; do not attribute helpers as3printed results. Nondegenerate actual public canary real identity onpositive halfline, finite1/2, derivative/gradient1 andtop at-1, all-y bound and anonymous outside query.

Fresh actual root9088/Tests9230/full466tests7existing skips;12 named standard3-or-none axioms/3nativeguards passed. Fresh scoped actual compiled shared-root3node416edge graph before source comment delta, allproof tokens unchanged and actual terminal references to local helper/real helper/shared convexExtended bridge confirmed. NOT full graph/canary export. Exact stacked base OPENdraftPR157 a6607d8213860619965c7018e4dd2effff58422a (REST refreshed);4production paths/1manifest pass. Main-relative gate remains FAIL15legacyproductioncontracts, not main-ready. Full whitespace fails exact raw logs, scoped code/JSON/scripts/docs check passes explicitly enumerated raw original/output exceptions; raw bytes not trimmed. Source-comment qualification/publicbuild/native guards/semantic targets have no math failure or repair. Diagnostic read attempts with nonexistent tools/build_site.py and tools/check_site.py were corrected to actual website/scripts help; no build result claimed from those attempts.

Clean site exactsource63453e28ae0ce86a87c6cc1b11ef0403bfe0141c, leanverifiedtrue/source_dirtyfalse after current applicable gates. This source commit differs from later metadata/final PR head.3unique retained frozen canonical shared nodes/OnlineBookmembership and all10806oldIDsURLs preserved, same registryidentity; zero newnodes. Actual headless Edge first viewport viewed, full lowerHTML bound separately, no unobserved lowerpixels/physicaldevice claim. Canonicalgenerated_site unchanged. Earlier accepted finite-loss/convex/FTL/OGD reports/receipts untouched; exact snapshots resolve source-comment and onlyonline-first-order shared-reader delta.

Existing native CLI gates versus role/prompt/file conventions distinct, not one runtime certifying all process. Three distinct required automated actors with prior history; no human/external/independently attested runtime-model claim. Whole Chapters1-16 Goal ACTIVE/unbudgeted; Chapter2totalnull/incomplete. Legacy19beforeboundedacceptance may become18 onlyafterallpackagegates, no mathematical newproofcount. Future chapters3-16unenumeratedmandatory; noChapter3writing or merge/deploy/retirement. Finalpackageacceptance/PR follow this separate reviewer decision; notwholechapter/book completion.

Write ONLY final-reader-review-v1.md/final-reader-receipt-v1.json here, actor.task=/root/source_reviewer, verdict, mathematical_repairs/required_repairs, seven slots and reader/helper/OGD qualification audit, actualgates/registry/raw historical bindings, reviewed_files exactSHA/reportpath/reportSHA, remaining obligations. No edits to inputs.''')
surfaces=['BanditRLProof/OnlineConvexFirstOrder.lean','Tests/OnlineConvexFirstOrderCanary.lean','BanditRLProof.lean','Tests.lean',
 'BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentSource.lean',
 'website/content/books.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json',
 'research-wiki/contribution-contracts/online-first-order-migration-20261005.json','lean-toolchain','lakefile.lean','lake-manifest.json',
 'runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json']
paths=set(surfaces);paths.update(row['path'] for row in load(run/'public-body-inputs-v1.json')['rows'])
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.update((site/p).as_posix() for p in ['site-manifest.json','books/registry.json','chapters/online-first-order/index.html'])
paths.add('tmp/online-first-order-migration-reader-v1.png')
for c in reg['checks']:paths.add((site/c['url'].split('#',1)[0].lstrip('/')).as_posix())
paths={str(Path(p)/'index.html') if Path(p).is_dir() else p for p in paths}
for p in paths:assert Path(p).is_file(),p
write('final-reader-inputs-v1.json',dict(scope='three retained first-order proofs/helper-qualified source reader only',canonical_surfaces=surfaces,
 site_commit=manifest['source_commit'],retained_proofs=3,new_proofs=0,new_registry_nodes=0,mandatory_chapter_total=None,chapter_complete=False,goal_complete=False,
 rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Final source/reader package fixed inputs',len(paths),'rows; clean source',manifest['source_commit'])
