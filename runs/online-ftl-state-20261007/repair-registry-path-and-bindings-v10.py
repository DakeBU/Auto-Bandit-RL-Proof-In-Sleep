from common_v1 import *
fixed(proving=True,integrated=True)
assert load(RUN/'registry-v4-exit.json')['exit_code']==1 and load(RUN/'site-check-v4-exit.json')['exit_code']==0
source=(RUN/'verify-registry-v4.py').read_text(encoding='utf-8')
start=source.index("write(RUN/'registry-v4.json'");extra=source.index("current={x['id']:x for x in new}")
record=source[start:extra].strip();body=source[:start]+source[extra:]+ '\n'+record+'\n'
body=body.replace('scanner.scan_module(PUBLIC)','scanner.scan_module(PUBLIC.resolve())').replace("registry-v4.json'","registry-v5.json'").replace("registry-boundary-repair-v4.json'","registry-boundary-repair-v5.json'")
write(RUN/'verify-registry-v5.py',body)
write(RUN/'registry-path-repair-v10.json',dict(actual_failed_gate='registry-v4',exit_code=1,log_sha256=sha(RUN/'registry-v4.log'),partial_record='registry-v4.json',partial_record_not_complete_gate=True,actual_cause='Scanner requires absolute path; helper passed relative PUBLIC after successful old/new registry checks.',repair='Newv5 helper resolves PUBLIC absolute and writes final success only after every assertion. Same clean site-v4/source commit; no source/Lean/definition change.',prior_partial_record_preserved=True,current_required_record='registry-v5.json'))
capture=(RUN/'capture-reader-v4.py').read_text(encoding='utf-8').replace("registry-v4.json'","registry-v5.json'")
write(RUN/'capture-reader-v5.py',capture)
for old,new in [('record-acceptance-v4.py','record-acceptance-v5.py'),('prepare-publication-v4.py','prepare-publication-v5.py'),('prepare-delivery-v4.py','prepare-delivery-v5.py'),('complete-publication-v4.py','complete-publication-v5.py')]:
 text=(RUN/old).read_text(encoding='utf-8').replace('registry-boundary-repair-v4','registry-boundary-repair-v5').replace('registry-v4','registry-v5').replace('prepare-publication-v4.py','prepare-publication-v5.py')
 if old=='prepare-publication-v4.py':text=text.replace('applicable registry-v5/site-v4','applicable registry-v5/site-v4')
 write(RUN/new,text)
active=['record-acceptance-v5.py','prepare-publication-v5.py','create-pr-v1.py','complete-publication-v5.py','prepare-delivery-v5.py','audit-committed-raw-v1.py','commit-owned-v2.py','audit-scope-v3.py','check-scoped-diff-v2.py']
write(RUN/'publication-tools-before-FINAL-v6.json',dict(rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in active],scope='Active recorded workflow v5 acceptance/publication/delivery; complete current registry-v5 over same clean site-v4/pixel-review-v4. Partial registry-v4 gate failed after core checks; retained and not final evidence. Owned v2/sourceaudit3/scopediff2. Earlier plans inactive by recorded workflow, not universal runtime prohibition.',current_full_harness_tests=472,existing_skips=7,source_boundary_tests=6,source_math_unchanged=True,chapter_complete=False,goal_complete=False))
final=(RUN/'prepare-final-review-v5.py').read_text(encoding='utf-8').replace('registry-v4','registry-v5').replace('site-build-v3','site-build-v4').replace('site-check-v3','site-check-v4').replace('ACTIVEv4','ACTIVEv5').replace('Activefuturev4','Activefuturev5').replace('Activefuturev4','Activefuturev5').replace('publication-tools-before-FINAL-v5','publication-tools-before-FINAL-v6').replace('v5selectionrecord','v6selectionrecord')
final=final.replace('FINALdoesnotacceptchapter/Goal/main/live/merge.', 'Actual registry-v4 helper exited1 after partial core-check record because it supplied a relative path to shared scan_module. Newv5 uses PUBLIC.resolve() and performs every assertion before final registry-v5 success record; same clean site-v4 has not changed. Partialv4 record/log retained, not complete-gate evidence. Currentfuturev5 helpers and selectionv6 bind registry-v5/site-v4/pixel-review-v4 explicitly. FINALdoesnotacceptchapter/Goal/main/live/merge.')
write(RUN/'prepare-final-review-v6.py',final)
gate('registry-v5',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v5.py')
gate('formula-render-v4',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v5.py')
