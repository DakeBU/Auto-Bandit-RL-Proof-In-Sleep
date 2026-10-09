from publication_guard_v1 import *
from proof_driver import native_snapshot
fixed()
assert load(RUN/'full-harness-inspected-v1.json')['actual_check_passed']
docs=[ROOT/d/(TASK+'.md') for d in ['proof-obligations','research-wiki/retrieval-index']]
write(RUN/'pre-candidate-owned-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [CONTRIBUTION,*docs]]))
summary=('Six frozen source-loss/actual-source-update proof terminals and two complete8/6conjunct canaries have focused/public VALUE, standard-only axioms, frozen native fences and distinct CONTRACT/BODY/publication acceptance. '
 'The source codomain/domain assumptions now produce properness; strict penalized objectives identify supplied actual minima with the same classical selector; induction identifies the supplied valid source trajectory with the actual Option recursion. Both printed fixed and decreasing-step bounds are derived, not assumed. '
 'All six proof bodies and both full canaries passed combined root/Tests/full harness with actual markers/hashes in inspected receipts. Selected8public/8total nodes,1431coalesced directTYPE_VALUE presences,20requiredVALUEpairs and two individually selected numeric Eq.mpr branches retaining their specific new source endpoints. '
 'This is conditional valid-run source transport, not universal attained minima or automatic interior preservation. Six Lean proofs are not six printed source results. All eight Chapter2 source forward containers remain required/open pending dedicated reconciliation; Chapter2 partial/null, Ch3-16 unenumerated/null, persistent Chapters1-16 Goal ACTIVE. '
 'Shared registry/site/browser/original-pixel/FINAL/native/delivery gates pending. Stacked unmerged PR212 exact '+BASE+'. No main/live/merge/deploy/CI/retirement claim.')
for p in docs:p.write_bytes(p.read_bytes()+('\nIntegrated candidate: '+summary+'\n').encode('utf8'))
c=load(CONTRIBUTION)
c['verification']['bandit_check']='Actual combined root/Tests and complete tools/bandit.py check passed, compiler/unittest/exporter/check markers inspected; actual counts and RAW command/source hashes in RUN combined-root-Tests-inspected-v1.json/full-harness-inspected-v1.json. FINAL/native/site/delivery pending.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'memory-digest-candidate-v1.md','# '+TASK+'\n\n'+summary+'\n')
names=[t['name'] for t in load(CONTRACT/'stabilized-v1.json')['six_targets']]
tests=[t['name'] for t in load(CONTRACT/'canary-headers-draft-v2.json')['targets']]
write(RUN/'proof-obligations-candidate-v1.json',dict(terminals=[dict(declaration=n,status='focused/combined/public/frozen/BODY accepted; FINAL pending') for n in names],public_canaries=tests,source_forward_containers_open=8,chapter_proof_total=None,chapter_complete=False,whole_Goal='ACTIVE'))
native_snapshot('pre-candidate-native-v1')
event('native-integrated-candidate-v1','candidate',dict(task=TASK,terminals=names,combined_harness_sha256=sha(RUN/'full-harness-inspected-v1.json'),BODY_review_sha256=sha(RUN/'six-BODY-review-v1.json'),FINAL_pending=True,chapter_complete=False,whole_Goal='ACTIVE'))
_,out=capture('candidate-production-lookup-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls','OnlinePrescientBregmanSource','--statement')
assert all(n in out for n in names)
_,out=capture('candidate-Test-lookup-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls','OnlinePrescientBregmanSourceCanary','--include-tests','--statement')
assert all(n in out for n in tests)
native_snapshot('pre-reference-index-native-v1')
capture('candidate-reference-index-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','reference-index','--help')
capture('candidate-reference-index-v1',sys.executable,'-B','-X','utf8',RUN/'reference-index-scoped-v1.py','reference-index')
idx=load(RUN/'reference-index-v1/local_lean_declarations.json');indexed={r['full_name'] for r in idx['declarations']}
assert all(n in indexed for n in names) and all(n not in indexed for n in tests)
outputs=list((RUN/'reference-index-v1').glob('*.json'));assert len(outputs)==8
write(RUN/'candidate-reference-index-inspected-v1.json',dict(output_rows=rows(outputs),six_production_present=True,Test_probes_separate=True,global_indexes_unchanged=True))
capture('candidate-frontier-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','frontier-refresh','--help')
capture('candidate-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; bounded six source transport proofs','--leaf',TASK,'--kind','review','--statement',summary,'--file',RUN/'six-BODY-review-v1.md','--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','review:source-transport-BODY:accepted','--trials',RUN/'trials.jsonl','--output',RUN/'current-frontier-v1.json','--shadow-status','pending')
_,out=capture('candidate-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'current-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate']
write(RUN/'shadow-inspected-v1.json',dict(actual_report=shadow,global_SGB_unchanged=True,source_container_closed=False,chapter_complete=False,whole_Goal='ACTIVE'))
fixed()
print('Integrated candidate/actual own lookup/index/shadow recorded; full source-container closure pending.')
