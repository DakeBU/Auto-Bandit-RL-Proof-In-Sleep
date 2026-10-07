"""Actual combined shared root/Tests/full harness after new bounded source integration."""
from common_v4 import *
fixed(True,True);assert load(RUN/'reader-integration-v1.json')['production_new_proofs']==3
for p in ['BanditRLProof.lean','Tests.lean']:
 assert Path(p).read_bytes().startswith((RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt')).read_bytes()),p
raw=Path('MANIFEST.md').read_bytes();assert TASK.encode() not in raw
write(RUN/'manifest-before-nondiff-entry-v1.txt',raw)
Path('MANIFEST.md').write_bytes(raw+('\n\n## '+TASK+'\n\nOrabona v10 unnumberedexample afterT2.30/endSection2.2.1 immediatelybefore2.2.2 printed19/PDF31. NewactualrealEuclidean2 globalconvex+ALLclosedsegment ambientnondifferentiability terminal:3publicproofs/1definition/5nondegeneratecanaryproofs/9standardkernel4guards/9actualnodes1194refs9requiredpairs. CONTRACTv1sourceM1rejection/v2metadata-onlyrepair/BODYaccepted; originalfailures/fingerprints preserved. Combinedproject/site/FINAL/native/actualPRpending atthishistoricalcandidateentry. FormaluncountabilityconsequenceseparatelyREQUIREDplanned, Chapter2null/incomplete/GoalACTIVE, no merge/mainlive.\n').encode())
native('named-public-search-v1','list-lean-decls','coordinate','--statement')
native('named-terminal-search-v1','list-lean-decls','convex_nondifferentiable_segment','--statement')
gate('root-v1-01','lake','build','BanditRLProof')
gate('Tests-v1-01','lake','build','Tests')
assert passed('Tests-v1-01')['started_at']>=passed('root-v1-01')['ended_at']
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m; jobs[label]=int(m.group(1))
write(RUN/'proof-obligations-candidate-v1.json',dict(stage='candidate',required_terminal=PRE+'convex_nondifferentiable_segment',state='actualnewterminalcompiled/CONTRACTv2andBODYreviewed/sharedrootTests passed/fullharnesssiteFINALpending',sequential_project_jobs=jobs,new_public_proofs=3,new_definitions=1,new_canary_proofs=5,named_kernel_checks=9,native_guards=4,cardinality_required_separate=True,chapter_complete=False,goal_complete=False))
digest=TASK+' Actualnew2Dglobalconvex+ALLclosedsegment ambientterminal compiled/CONTRACTv2metadatarepair/BODYaccepted. Realhorizontalderivativeproducer, no oracle/scalar-onlyclosure. Five actualnondegeneratecanaries/9kernel4guards/9selectednodes1194refs9actualpairs. SharedrootTests pass/fullharnesssiteFINALnativePRpending. Separateuncountabilityterminal/nineOTHERChapter1gaps/remainingmaintextrequired; Chapter2null/incomplete/legacy0notcompletion/GoalACTIVE. SGBfixed/nomerge/mainlive.'
write(RUN/'memory-digest-candidate-v1.md',digest);write(RUN/'retrieval-index-candidate-v1.md',digest)
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==TASK))
event('candidate',dict(sequential_jobs=jobs,remaining_gates=['fullharness','historyexactbasediff','site/registry/actualpixels/FINAL/native','actualPR'],cardinality_required=True),attempt='combined-v1')
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','PersistentOrabonaChapters1-16 Goal; exactunnumbered2Dexample candidateonly, formalcardinality/chapter/bookrequired','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'convex_nondifferentiable_segment'),'--declaration',PRE+'convex_nondifferentiable_segment','--file',PUBLIC,'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:'+PRE+'coordinate_absolute_convex:compiled','--dependency','lean:'+PRE+'coordinate_absolute_not_differentiable:compiled','--dependency','review:source-body:accepted','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed(True,True);gate('full-harness-v1-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
print('Actualcurrentnewsource combinedrootTests/fullharness/taskshadow passed; FINAL/native/actualPRseparate.')
