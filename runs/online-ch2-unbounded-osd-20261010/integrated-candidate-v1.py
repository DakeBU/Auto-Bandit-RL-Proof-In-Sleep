from publication_guard_v1 import *
from canary_driver import native_snapshot
fixed()
assert load(RUN/'full-harness-inspected-v1.json')['actual_check_passed']
docs=[ROOT/d/(TASK+'.md') for d in ['proof-obligations','research-wiki/retrieval-index']]
write(RUN/'pre-candidate-owned-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [CONTRIBUTION,*docs]]))
summary=('Eleven frozen production proof terminals, four source witness definitions and two FULL7/9conjunct public canaries passed actual focused/public/axiom/fence/VALUE/BODY and combined root/Tests/full harness gates. '
 'The SAME canonical causal OSD affine selector/update/recursion gives the exact scalar regret identity, then actual sum-integral bounds and horizon threshold give the printed Theorem5.4 lower bound; unit direction embeds the run, nontrivial finite-dimensional E supplies the source existential. phi range and left limit/numerical supplement are proved separately. '
 'Selected17public/17total nodes,3240coalesced directTYPE_VALUE presences,24requiredVALUEpairs and4individually selected compiled numeric/existential branches retaining the new source proofs. Counts are not source results or chapter denominators. '
 'T2 scalar states0->1->1-2^(-1/2),R2=1; T64 E2D actual nonzero state, source threshold,256/15<=R,17<R and full source existential. Different horizon-specific loss streams, not common prefixes. '
 'Positive dimension/source-implicit Nontrivial is necessary; totalphi(1)=1 differs from its left limit. No assumed regret/trajectory or minimax-all-learners result. '
 'All eight Chapter2 source forward containers remain required/open pending dedicated reconciliation and chapter gates; Chapter2partial/null, Ch3-16unenumerated/null, persistent Chapters1-16 Goal ACTIVE. '
 'Shared registry/site/original-pixel/FINAL/native/delivery gates pending. Stacked on OPEN draft unmerged PR213 exact '+BASE+'. No main/live/merge/deploy/CI/retirement claim.')
for p in docs:p.write_bytes(p.read_bytes()+('\nIntegrated candidate: '+summary+'\n').encode('utf8'))
c=load(CONTRIBUTION)
c['verification']['bandit_check']='Actual combined root/Tests and complete tools/bandit.py check passed, compiler/unittest/exporter/check markers inspected; exact counts and RAW source/command hashes in combined-root-Tests-inspected-v1.json/full-harness-inspected-v1.json. FINAL/site/native/delivery pending.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'memory-digest-candidate-v1.md','# '+TASK+'\n\n'+summary+'\n')
names=[n['full_name'] for n in load(RUN/'reader-proposal-v1.json')['notes']]
proofs=[t['name'] for t in load(CONTRACT/'stabilized-v1.json')['targets']]
tests=[t['name'] for t in load(CONTRACT/'canary-headers-draft-v2.json')['targets']]
write(RUN/'proof-obligations-candidate-v1.json',dict(terminals=[dict(declaration=n,status='focused/combined/public/frozen/BODY accepted; FINAL pending') for n in proofs],definitions=names[:4],public_canaries=tests,source_forward_containers_open=8,chapter_proof_total=None,chapter_complete=False,whole_Goal='ACTIVE'))
native_snapshot('pre-candidate-native-v1')
event('native-integrated-candidate-v1','candidate',dict(task=TASK,terminals=proofs,combined_harness_sha256=sha(RUN/'full-harness-inspected-v1.json'),BODY_review_sha256=sha(RUN/'canary-BODY-review-v1.json'),FINAL_pending=True,chapter_complete=False,whole_Goal='ACTIVE'))
_,out=capture('candidate-production-lookup-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls','OnlineUnboundedOSD','--statement')
assert all(n in out for n in names)
_,out=capture('candidate-Test-lookup-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls','OnlineUnboundedOSDCanary','--include-tests','--statement')
assert all(n in out for n in tests)
native_snapshot('pre-reference-index-native-v1')
capture('candidate-reference-index-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','reference-index','--help')
capture('candidate-reference-index-v1',sys.executable,'-B','-X','utf8',RUN/'reference-index-scoped-v1.py','reference-index')
idx=load(RUN/'reference-index-v1/local_lean_declarations.json');indexed={r['full_name'] for r in idx['declarations']}
assert all(n in indexed for n in names) and all(n not in indexed for n in tests)
outputs=list((RUN/'reference-index-v1').glob('*.json'));assert len(outputs)==8
write(RUN/'candidate-reference-index-inspected-v1.json',dict(output_rows=rows(outputs),fifteen_production_present=True,Test_probes_separate=True,global_indexes_unchanged=True))
capture('candidate-frontier-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','frontier-refresh','--help')
capture('candidate-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; Chapter2 required unbounded OSD failure dependency','--leaf',TASK,'--kind','review','--statement',summary,'--file',RUN/'canary-BODY-review-v1.md','--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','review:OSD-source-BODY:accepted','--trials',RUN/'trials.jsonl','--output',RUN/'current-frontier-v1.json','--shadow-status','pending')
_,out=capture('candidate-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'current-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate']
write(RUN/'shadow-inspected-v1.json',dict(actual_report=shadow,global_SGB_unchanged=True,source_container_closed=False,chapter_complete=False,whole_Goal='ACTIVE'))
fixed()
print('Integrated candidate/actual own lookup/index/shadow recorded; source-container reconciliation pending.',flush=True)
