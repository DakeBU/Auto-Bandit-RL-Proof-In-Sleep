from common import *
f=fixed(True);assert load(RUN/'body-binding-audit-v2.json')['status']=='passed-at-review-boundary'
gate('root-v1-01','lake','build','BanditRLProof')
gate('Tests-v1-01','lake','build','Tests')
assert passed('Tests-v1-01')['started_at']>=passed('root-v1-01')['ended_at']
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
f=fixed(True)
write(RUN/'proof-obligations-candidate-v1.json',dict(stage='candidate',required=[dict(name=n,statement_hash=h,state='retained fulldefinition/producers compiled; CONTRACT/BODYv2 accepted; combined gates pending') for n,h in f['headers'].items()],sequential_project_jobs=jobs,retained_proofs=3,retained_definitions=1,new_production_proofs=0,whole_canary_proofs=4,whole_canary_definitions=2,named_kernel_checks=10,native_guards=4,source_package_accepted=False,chapter_complete=False,goal_complete=False))
digest=TASK+' — ONE Example2.25/THREE exact equalities/ONE full owned normal definition/zero new math or TESTs. Intrinsic definition no FD/nonempty/convexity; actualthree theorem FD, firsttwo nonemptyconvexV; everyquery incloutsideempty/ALLambient support/all feasible normaly; nonemptyindicatorproper versus genericimproperS. Actual ambient ball/nonzerodisplacement and normalization/Cauchy produce interiorzero/fullclosedunitballnonnegative rayincl0. Whole4canaryproof2TESTdefs includingactual2D, singletondoesnotproveemptyinterior. Ten kernelchecks/fourguards; ready4nodes818refs8pairs distinctselected10nodes1581refs15pairs. CONTRACT/BODYv2 accepted, BODYv1 evidence-pointerreject retained/repaired without mathchange. Current postcomment sequential rootTests passed; fullharness/siteFINAL/PR pending. NextT2.26/allremainingChapter1/2/appendixrequired; Chapter2nullincomplete/3-16unenumerated/wholeGoalACTIVE. No mainlive/merge/deploy/retirement.'
write(RUN/'memory-digest-candidate-v1.md',digest)
write(RUN/'retrieval-index-candidate-v1.md','Actual10 @types/fullownedN/borrowedS-J-proper-domain/pinned15APIs/localnative retrievalrecord/ready4nodes818refs8pairs/selected10nodes1581refs15actualvaluepairs. Reuse-only/fullsourcePDF30/headers/wholeoldcanary fixed; no externalcompatible rebuild/globalindex rewrite. Three curated links/three notation entries/four existingcanonicaldeclarations. Current fullgates/FINAL/PR pending; onlyExample2.25 scope.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==TASK))
event('candidate',dict(frozen_headers=f['headers'],sequential_jobs=jobs,source_package_accepted=False,remaining_gates=['fullharness','exact contributor/diff/history','site/registry/browser/FINAL','raw/PR']))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only Example2.25 candidate, chapter/book incomplete','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'normalCone_unitBall_boundary'),'--declaration',PRE+'normalCone_unitBall_boundary','--file',PUBLIC,'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:'+PRE+'SourceNormalCone:compiled','--dependency','review:source-body:accepted','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed(True)
gate('full-harness-v1-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
print('Actual postcomment sequential rootTests/fullharness and task-only candidate shadow PASS; fullpackage/site/FINAL/PR separate.')
