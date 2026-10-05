"""Freeze final source/reader/package inputs after actual current integrated gates."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;site=Path('tmp/online-optimality-migration-site-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
gates=['root-v1-01','Tests-v1-01','full-harness-v1-01','contributor-exact-v1-01','scoped-diff-v1-01','site-build-v1','site-check-v1',
 'registry-v1-01','browser-v1-01','history-bindings-v1-01','public-axioms-v1-01','candidate-frontier-shadow-v1']
for n in gates:assert load(run/(n+'-exit.json'))['exit_code']==0,n
raw=(run/'full-harness-v1-01.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
reg=load(run/'registry-v1.json');assert reg['new_registry_nodes']==0 and len(reg['checks'])==4 and reg['preserved_base_node_ids_and_urls']==10806
manifest=load(site/'site-manifest.json');assert manifest['source_dirty'] is False and manifest['lean_verified'] is True
history=load(run/'history-binding-audit-v1.json')
write('integrated-gates-overlay-v1.json',dict(status='passed-scoped-integrated-gates-final-semantic-review-pending',actual_passed_gates=gates,
 root_jobs=9088,Tests_jobs=9230,full_tests=466,existing_skips=7,public_axiom_names=13,native_guards=4,retained_proofs=4,new_proofs=0,new_registry_nodes=0,
 preserved_old_IDs_URLs=10806,actual_scoped_graph_nodes=4,actual_scoped_graph_edges=510,site_source_commit=manifest['source_commit'],source_dirty=False,
 lean_verified=True,prior_raw_bindings_checked=history['raw_rows_verified'],exact_stacked_base='c9b47c8ba79a234d0dfa6e8ef5643a43677dd33a',stacked_base_PR=158,
 main_relative_gate='FAIL14legacyproductioncontracts',full_whitespace_gate='FAILexactrawlogs',scoped_whitespace_gate='PASSenumeratedrawexceptions',
 candidate_manifest_pending_fields_superseded_additively=True,chapter_complete=False,goal_complete=False,merged=False,live=False))
write('final-reader-packet-v1.md','''Required distinct final SOURCE/READER/PACKAGE review GPT-6 Astra / medium. Independently hash all final-reader-inputs-v1.json rows and resolve historical snapshot chains/current and prior receipt bindings from history-binding-audit-v1.json (5874rows). Four retained optimality proofs/no definitions/newproofcode/registry nodes only: Theorem2.8 and mandatory following unnumbered interiorzero consequence plus two libraryhelpers. Actual4headers/proof tokens/canarybytes unchanged; leading sourcecomment only. Exactsourcev10p11PDF23; completeHilbert generality explicit. Source neighborhoodconvexity weakenedtoConvexOnV givingstrongertheorem, not strengtheningpremise/equivalence; arbitraryopenUcontainsV finitebothinfinitiesexcluded andcanonicalF differentiableonU. NoConvexU/globalnoBottom/finite/convexFoutsideU. Proved coe_toReal identity onfiniteU giveslocalderivativemeaning; suppliedextension isnotexistence/independenceclaim.

Audit all5requiredreadercorrections onactualJSON/chapter/moduleHTML: classifytwohelpers andprinted/unnumberedsource separately; everywhere-realhelper exactConvexOnV/xmember/ambientderivative noopen/ERealbridge; finitebridge onlyfiniteV/xmember no convexity/open/derivative; weakervsstronger wording/sourceConvexOnUrestriction butnoactualConvexU; canonicalF/finiteU/localidentity/outsideinfinities plus IsMinOnmembershipseparate/extraambientinterior/differentiabilityretaineddespiteFermatfallback. Boundarygradient1 and smaller0.5outsideV/larger2inside meaningful, actualsourceConvexOnUcanaryrestricts; nonconstantquadraticopenV interior0/gradient0/values0vs1. Nozero-gradientboundary/nonconvexsufficiency/existence/uniqueness/closedness/boundedness claim. Onlyonline-optimalitysubtreechanged; same4representativelinks/3notation/4highlights, allotherBooks retained.

Fresh actualroot9088/Tests9230/full466tests7existingskips,13namedstandard3-or-noneaxioms/4nativeguards andfixedheaders pass. Scopedfreshactualcompiledsharedroot4node510directedges/5projectproofvaluepairs beforecommentdelta, alltokenssame after; notfull/canarygraphexport. Exactstacked OPENdraftPR158c9b47c8ba79a234d0dfa6e8ef5643a43677dd33a refreshedREST,4production/1manifestpass. Main-relativecontributor diagnosticstillFAIL14otherlegacyproductioncontracts. FullwhitespaceFAILexactrawlogs, scopedcodeJSONscriptsdocsPASSwithenumeratedraworiginals/output exceptions; rawbytesnottrimmed. Auxiliaryhistoryscript twodescriptivelabels corrected beforefirstexecution, originalpreparationhash retained plusadditivecorrection; no mathgatefailure/repair/targetweakening. NativeCLIcommand gates versus prompts/files/rolesdistinct, notsingleruntime allflow enforcement.

Cleanactualsiteusesexactsourcecommitinregistry/finalinputs, source_dirtyfalse/leanverifiedtrue onlyafterapplicablefreshcombinedgates. Latermetadata/PRheaddifferent.4uniquefrozenretainedcanonicalnodes/OnlineBookmembership,10806oldIDsURLs andsharedidentity retained, no newnodes. ActualheadlessEdgefirstviewportviewed/observationbound, no unobservedlowerpixels/physicaldeviceclaim; fulllowerHTMLbound separately. Generated_siteuntouched. Allpriorfirst-order/finite-loss/convex/FTL/OGD acceptedreports/receipts immutable, exactsnapshotchainsresolve sharedsurface delta. Three distinct automatedrequiredactors requestedAstra/mediumwithpriorhistory; nohuman/external/independentlyattestedruntimeclaim.

WholeChapters1-16Goalactive/unbudgeted, Chapter2null/incomplete; legacy18beforeboundedacceptance maybe17onlyafterallpackagegates, notnewmathproofcount. Allremainingmaintext/source/appendix/Ch3-16mandatory, noChapter3writing/merge/deploy/retirement. WriteONLY final-reader-review-v1.md/final-reader-receipt-v1.json here withactor.task=/root/source_reviewer, verdict, required_repairs/mathematical_repairs, seven slots/readercorrections/gates/registry/rawhistorical audit, exactreviewedfiles/reportpath/reportSHA. Seekmismatch, noinputs edits. Packageimmutableacceptance/PR follows separateverdict.''')
surfaces=['BanditRLProof/OnlineConvexOptimality.lean','Tests/OnlineConvexOptimalityCanary.lean','Tests/OnlineConvexFirstOrderCanary.lean',
 'BanditRLProof/OnlineConvexFirstOrder.lean','BanditRLProof.lean','Tests.lean','website/content/books.json','website/content/readings.json',
 'website/content/highlights.json','website/content/chapters.json','research-wiki/contribution-contracts/online-optimality-migration-20261005.json',
 'lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json']
paths=set(surfaces);paths.update(row['path'] for row in load(run/'public-body-inputs-v1.json')['rows'])
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.update((site/p).as_posix() for p in ['site-manifest.json','books/registry.json','chapters/online-optimality/index.html'])
paths.add('tmp/online-optimality-migration-reader-v1.png')
for c in reg['checks']:paths.add((site/c['url'].split('#',1)[0].lstrip('/')).as_posix())
paths={str(Path(p)/'index.html') if Path(p).is_dir() else p for p in paths}
for p in paths:assert Path(p).is_file(),p
write('final-reader-inputs-v1.json',dict(scope='four retained optimality proofs/source-qualified reader only',canonical_surfaces=surfaces,site_commit=manifest['source_commit'],
 retained_proofs=4,new_proofs=0,new_registry_nodes=0,mandatory_chapter_total=None,chapter_complete=False,goal_complete=False,rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Optimality final source/reader package fixed inputs',len(paths),'rows; actualclean source',manifest['source_commit'])
