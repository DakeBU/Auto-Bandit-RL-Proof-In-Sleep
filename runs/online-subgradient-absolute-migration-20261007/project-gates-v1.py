from common import *
fixed(True);assert load(RUN/'body-binding-audit-v1.json')['status']=='passed'
gate('root-v1-01','lake','build','BanditRLProof')
gate('Tests-v1-01','lake','build','Tests')
assert passed('Tests-v1-01')['started_at']>=passed('root-v1-01')['ended_at']
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
f=fixed(True)
write(RUN/'proof-obligations-candidate-v1.json',dict(stage='candidate',required=[dict(name=n,statement_hash=h,state='exact body compiled; distinct BODY accepted; integrated project gates pending') for n,h in f['headers'].items()],sequential_project_jobs=jobs,new_production_proofs=0,whole_canary_proofs=3,named_kernel_checks=7,native_guards=4,source_package_accepted=False,chapter_complete=False,goal_complete=False))
digest=TASK+' — only full scalar Example2.24 candidate; four retained proof refinements/zero defs/zero new math or TESTs. Threecase whole-set equality everyx/everyg/allambienty; full inclusive zero[-1,1]; strict sign leaf/nonzero cancellation and direct allx dispatch. Generic S wider than printedproper-function definition but fixedabs globallyfinite/proper; sharedS borrowed not newowned. Whole3oldcanaries endpoints/½/exclude2/noANYsingleton/fullterminal2,-2,0. Sevenkernel standardfoundations-or-none/fournativeguards/sevenselectedproofnodes; fourreadinessnodes separate/notfullgraph. Distinct CONTRACT/BODY accepted; postcomment sequential rootTests PASS. Task-onlyshadow/globalSGBfixed; exactPR170stackbase/remainingChapter1contracts/Chapter2nullincomplete/3-16unenumerated/wholeGoalACTIVE; fullharness/siteFINAL/PR stillpending. No mainlive/merge/deploy/retirement.'
write(RUN/'memory-digest-candidate-v1.md',digest)
write(RUN/'retrieval-index-candidate-v1.md','Current native local search/retrievalrecord/four @types/full borrowedS/eleven pinned APIs/fourreadinessproofs666refs/seven selectedproducer-canary proofnodes/explicitvaluepairs; reuse-only. No externalcompatible rebuild or global reference-index rewrite. Frozen sourcePDF30/headers and historical old source contracts preserved; acceptance pending current full gates and FINAL.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==TASK))
event('candidate',dict(frozen_headers=f['headers'],sequential_jobs=jobs,source_package_accepted=False,remaining_gates=['fullharness','exact contributor/diff/history','site/registry/browser/FINAL','raw/PR']))
sys.path.insert(0,str(Path(__file__).resolve().parents[2]));from tools.abrl_lifecycle import lean_declaration_header
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; Example2.24 package candidate only, Chapter2/book incomplete','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'example_2_24'),'--declaration',PRE+'example_2_24','--file',PUBLIC,'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:'+PRE+'abs_subgradient_zero:compiled','--dependency','lean:'+PRE+'abs_subgradient_positive:compiled','--dependency','lean:'+PRE+'abs_subgradient_negative:compiled','--dependency','review:source-body:accepted','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed(True)
gate('full-harness-v1-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
print('Actual postcomment sequential rootTests/fullharness and task-only candidate shadow PASS; full package/site/FINAL/PR remain separate.')
