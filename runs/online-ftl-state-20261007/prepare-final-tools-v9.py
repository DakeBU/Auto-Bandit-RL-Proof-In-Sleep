from common_v1 import *
fixed(proving=True,integrated=True)
combined=load(RUN/'combined-gates-reader-v5.json')
assert combined['full_tests']==472 and combined['existing_skips']==7
resolution_audit='''
resolution=load(RUN/'catalog-scope-reviewed-source-resolution-v6.json')
scope_receipt=load(RUN/'catalog-scope-receipt-v6.json');assert scope_receipt['verdict']=='accepted-with-explicit-delta' and sha(scope_receipt['report'])==scope_receipt['report_sha256']
scope_reviewed={x['path']:x['sha256'] for x in scope_receipt['reviewed_files']}
for x in load(RUN/'catalog-scope-review-inputs-v6.json')['rows']:
 p=x['path'];resolved=resolution['immutable_snapshot'] if Path(p).resolve()==(ROOT/resolution['original_live_path']).resolve() else p
 assert scope_reviewed[p]==x['sha256']==sha(resolved),p
for p,h in scope_reviewed.items():
 resolved=resolution['immutable_snapshot'] if Path(p).resolve()==(ROOT/resolution['original_live_path']).resolve() else p
 assert sha(resolved)==h,p
'''
accept=(RUN/'record-acceptance-v3.py').read_text(encoding='utf-8')
accept=accept.replace("audits=[]","audits=[]\n"+resolution_audit)
accept=accept.replace("assert requirements==", "audits.append(dict(receipt='catalog-scope-receipt-v6.json',receipt_sha256=sha(RUN/'catalog-scope-receipt-v6.json'),report_sha256=scope_receipt['report_sha256'],fixed_rows=19,all_raw_bindings_match=True,reviewed_scanner_resolution=resolution))\nassert requirements==")
accept=accept.replace('BODY=body,','BODY=body,BODY_review_current=dict(status="accepted-with-explicit-delta",receipt_sha256=sha(RUN/"public-body-receipt-v1.json"),historical_pending_field_retained=True),source_presentation_repair=dict(scope_receipt_sha256=sha(RUN/"catalog-scope-receipt-v6.json"),implementation_sha256=sha(RUN/"catalog-implementation-bindings-v7.json"),registry_repair_sha256=sha(RUN/"registry-boundary-repair-v4.json"),new_python_regression_tests=6),')
write(RUN/'record-acceptance-v4.py',accept)
publication=(RUN/'prepare-publication-v3.py').read_text(encoding='utf-8').replace('registry-v3/site-v3','registry-v4/site-v4').replace('IDs/URLs/native hashes','IDs/URLs/source-presentation hashes')
publication=publication.replace('Runtime gates and file/role conventions remain distinct.', 'Approved narrow shared source-presentation hook pins the unchanged complete equation-style ftlState definition; no fabricated statement override, no inherited100-definition migration, and no new mathematical/native recursive-fence claim. Whole845module/10835declaration source comparison changes only newftlState; allold10823 ID/URL/statement hashes and other11new node hashes exact. Six meaningful Python tests reject stale/wrong/truncated ranges, included in the current472-test harness. Actual31images have zero horizontal scroll containers after aligned source formula layout. Priorv3catalogue appended a neighboring theorem; failedpriorcapture/scanner-helper invocation and repairs retained. Runtime gates and file/role conventions remain distinct.')
write(RUN/'prepare-publication-v4.py',publication)
complete=(RUN/'complete-publication-v3.py').read_text(encoding='utf-8').replace('prepare-publication-v3.py','prepare-publication-v4.py').replace('commit-owned-v1.py','commit-owned-v2.py').replace('check-scoped-diff-v1.py','check-scoped-diff-v2.py').replace('audit-scope-v2.py','audit-scope-v3.py')
complete=complete.replace("assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw", "counts=re.search(r'Ran (\\d+) tests',raw);skips=re.search(r'OK \\(skipped=(\\d+)\\)',raw);assert counts and skips and int(counts[1])==load(RUN/'integrated-gates-overlay-v1.json')['full_tests'] and int(skips[1])==load(RUN/'integrated-gates-overlay-v1.json')['existing_skips'] and 'check passed' in raw")
write(RUN/'complete-publication-v4.py',complete)
delivery=(RUN/'prepare-delivery-v3.py').read_text(encoding='utf-8').replace('registry-v3.json','registry-v4.json').replace('pixel-review-v3.json','pixel-review-v4.json').replace('IDsURLs/nativehashes','IDsURLs/source-presentation-hashes')
delivery=delivery.replace("'full-harness-final-v1-exit.json']", "'full-harness-final-v1-exit.json','catalog-scope-receipt-v6.json','catalog-implementation-bindings-v7.json','registry-boundary-repair-v4.json','catalog-focused-tests-v7-exit.json']")
write(RUN/'prepare-delivery-v4.py',delivery)
active=['record-acceptance-v4.py','prepare-publication-v4.py','create-pr-v1.py','complete-publication-v4.py','prepare-delivery-v4.py','audit-committed-raw-v1.py','commit-owned-v2.py','audit-scope-v3.py','check-scoped-diff-v2.py']
write(RUN/'publication-tools-before-FINAL-v5.json',dict(rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in active],scope='Active recorded workflow v4 acceptance/publication/delivery; applicable clean registry-v4/site-v4/pixel-review-v4. Expanded owned v2 and actual scope audit3. Inactive earlier plans retained never executed; no universal runtime disable claim.',current_full_harness_tests=472,existing_skips=7,source_boundary_tests=6,source_math_unchanged=True,chapter_complete=False,goal_complete=False))
final=(RUN/'prepare-final-review-v4.py').read_text(encoding='utf-8')
final=final.replace('formula-render-v3','formula-render-v4').replace('registry-v3','registry-v4').replace('site-v3','site-v4').replace('pixel-review-v3','pixel-review-v4').replace('source-card07','source-card07')
final=final.replace('combined-gates-reader-v4.json','combined-gates-reader-v5.json')
final=final.replace('Actual builtin wideformula scrolled tobothends;', 'All source formulas fit after alignment; actual zero horizontal formula scrollers;')
final=final.replace("labels=['combined-root-v1'", "labels=['catalog-focused-tests-v7','contributor-reader-v5','scoped-diff-reader-v5','source-scope-reader-v5','full-harness-reader-v5','combined-root-v1'")
final=final.replace("write(RUN/'pixel-review-v4.json'", resolution_audit+"\nwrite(RUN/'pixel-review-v4.json'")
final=final.replace('466fullharnesstests7existing skips','472fullharnesstests7existing skips (including6newPythonboundarytests)')
final=final.replace('Prepared ACTIVEv3 nativeacceptance/publication/delivery ONLY per publication-tools-before-FINAL-v4', 'Prepared ACTIVEv4 nativeacceptance/publication/delivery ONLY per publication-tools-before-FINAL-v5')
final=final.replace('current applicable record/sourcecommit/nativehashes','current applicable record/sourcecommit/source-presentation-hashes').replace('currentregistry-v3','currentregistry-v4')
final=final.replace("research-wiki/contribution-contracts/online-ftl-state-20261007.json']", "research-wiki/contribution-contracts/online-ftl-state-20261007.json','website/scripts/build_site.py','website/content/declaration-boundaries.json','tools/test_source_declaration_boundaries.py']")
extra='''
CURRENT repair scope: source-presentation ONLY, actual source reviewer scope-v6 accepted19fixed/21rawreceiptrows. Verify every prior scope input via catalog-scope-reviewed-source-resolution-v6.json: the exact preimplementation build_site.py is preserved as rawsnapshot at its originalsha; no other fixed input changes. Current scanner/config/test source are separately FINALfixed. Approved generic opt-in boundary hook verifies canonicalpublicdef/file/start/end/fullfileSHA/LFblockSHA/no skippednoncommentcode/targetresolution/duplicates; missingconfig keepsdefault scanner. Six actual Python regressiontests pass; full472tests7existingskips. Actual before/after845modules10835declarations comparison changes ONLYnewftlState statement to complete3-line equations, no followingftlPredict_prefix header. Actual registry-v4 separately verifies all10823old IDsURLs/sourcepresentationhashes EXACT and other11newnode hashes unchanged; onlynewftlState corrected. These are website source presentation hashes, NOTa native recursive declaration fence; nine theorem headers have actual native fence evidence. Generic broader proposal would change100olddefinitions/no proofs and is NOTapplied; candidates remain separateperdefinitionsourceaudit, relevant OnlineBook ones still required in chapterreconciliation. Oldv3site/catalogue/capture failedFINAL despite mechanicalpass; all31v4images are the actualcurrentpixel evidence. Module-new-declaration12 must show complete recursive equations WITHOUTnexttheoremheader. ROOT actually individuallyviewsall31v4images, actualzero wideformula scrollers; no claim of scrollingbothends. ReviewedScopev6 permits this source-only delta, no Leanpublic/Testbody/19Prop/24kernel/16VALUE1979ref change. Helperv7directmoduleimport failed beforemutation; versionedv8addsrepoROOT tosys.path; actualsource comparison/focusedtests pass. Allhistoricalfailures preserved. Activefuturev4tools and v5selectionrecord bindregistry-v4+pixel-review-v4 and fullcountsactualparsed, ownedv2/scopediffv2/sourceauditv3; earlierplans retained inactivebyworkflow not universalruntime prohibition. FINALdoesnotacceptchapter/Goal/main/live/merge.
'''
final=final.replace('# Distinct FINAL for general-initial FTL and actual recursive count/value state\n', '# Distinct FINAL for general-initial FTL and actual recursive count/value state\n'+extra)
final=final.replace("all_prior_raw_bindings_unchanged=True,actual_viewed_images", "all_prior_raw_bindings_unchanged=True,approved_scope_rows=19,scope_scanner_snapshot_resolution=resolution,actual_viewed_images")
write(RUN/'prepare-final-review-v5.py',final)
print('Concrete current v4 future helpers prepared; FINAL freeze still pending actual31pixel views.')
