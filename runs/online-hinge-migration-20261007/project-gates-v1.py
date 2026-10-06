from common_v2 import *
f=fixed(True);assert load(RUN/'body-binding-audit-v1.json')['status']=='passed-at-review-boundary'
gate('root-v1-01','lake','build','BanditRLProof')
gate('Tests-v1-01','lake','build','Tests')
assert passed('Tests-v1-01')['started_at']>=passed('root-v1-01')['ended_at']
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
f=fixed(True);b=load(RUN/'public-actual-bindings-v1.json');g=load(RUN/'compiled-dependencies-v1.json')
write(RUN/'proof-obligations-candidate-v1.json',dict(stage='candidate',required=[dict(name=n,statement_hash=h,state='retained full definitions/producers compiled; CONTRACT/BODY accepted; combined/site/final acceptance pending') for n,h in f['headers'].items()],sequential_project_jobs=jobs,retained_proofs=13,retained_definitions=2,new_production_proofs=0,whole_canary_proofs=5,whole_canary_definitions=0,named_kernel_checks=20,native_guards=15,source_package_accepted=False,chapter_complete=False,goal_complete=False))
delta=load('research-wiki/contribution-contracts/online-hinge-migration-20261007.json')['truth_boundary']
digest=TASK+' — '+delta+' CONTRACT/BODY accepted. Current postcomment sequential rootTests passed; fullharness/siteFINAL/PR pending. GlobalSGBfixed/task-only frontier, legacy2 pending realPR. No chapter/Goalcompletion or mainlive.'
write(RUN/'memory-digest-candidate-v1.md',digest)
write(RUN/'retrieval-index-candidate-v1.md','Actual20public/canary @types and nine full compiled definition signatures;14 qualified pinned APIs/native retrieval/ready15nodes1367refs23pairs/selected20nodes actualrefs29pairs/20kernelchecks15guards. Retained existing producer/wholecanary, no newgeneric theorem/externalcompatible rebuild/pin/globalindex/perBook library change. Current combined gates/sourceBODY; ONE source Example2.27 with three branches, twelve dependencies/two definitions. FOURhighlights/FOURcuratedlinks/THREEnotation/ONEsourcecard/15publiccanonical10811registry. '+digest)
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==TASK))
event('candidate',dict(frozen_headers=f['headers'],sequential_jobs=jobs,source_package_accepted=False,remaining_gates=['fullharness','exact contributor/diff/history','site/registry/pixels/FINAL','raw/PR']))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only Example2.27 candidate, chapter/book incomplete','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'example_2_27'),'--declaration',PRE+'example_2_27','--file',PUBLIC,'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:'+PRE+'sourceHinge:compiled','--dependency','lean:'+PRE+'hingeFamily:compiled','--dependency','review:source-body:accepted','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed(True);gate('full-harness-v1-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
print('Actual postcomment sequentialrootTests/fullharness/task-only shadow passed; site/FINAL/PR/wholeGoal remain separate.')
