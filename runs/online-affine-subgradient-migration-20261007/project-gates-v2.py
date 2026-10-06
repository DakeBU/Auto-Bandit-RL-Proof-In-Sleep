from common_v2 import *
f=fixed(True);assert load(RUN/'reader-integration-v1.json')['publication']=='research-wiki/contribution-contracts/online-affine-subgradient-migration-20261007.json';assert load(RUN/'integrated-public-guard-audit-v1.json')['status']=='passed';assert load(RUN/'public-comment-qualification-v1.json')['exact_original_raw_suffix'];assert load(RUN/'body-binding-audit-v1.json')['status']=='passed-at-review-boundary'
gate('root-v2-01','lake','build','BanditRLProof')
gate('Tests-v2-01','lake','build','Tests')
assert passed('Tests-v2-01')['started_at']>=passed('root-v2-01')['ended_at']
jobs={}
for label in ['root-v2-01','Tests-v2-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
write(RUN/'proof-obligations-candidate-v2.json',dict(stage='candidate',required=[dict(name=PRE+n,statement_hash=h,state='retained producer compiled; CONTRACT/BODY accepted; fullharness/siteFINAL pending') for n,h in f['headers'].items()],sequential_project_jobs=jobs,retained_proofs=1,retained_definitions=0,new_public_proofs=0,whole_canary_proofs=7,whole_canary_definitions=2,named_kernel_checks=10,native_guards=1,source_package_accepted=False,chapter_complete=False,goal_complete=False))
delta=load('research-wiki/contribution-contracts/online-affine-subgradient-migration-20261007.json')['truth_boundary']
digest=TASK+' — '+delta+' CONTRACT/BODY accepted; postcomment rootTests pass/fullharness/siteFINAL/nativePRpending. GlobalSGBfixed/task-onlyfrontier, legacy1pendingrealPR, nottotalmandatorycount. No Chapter/Goalcompletion/mainlive.'
write(RUN/'memory-digest-candidate-v2.md',digest)
write(RUN/'retrieval-index-candidate-v2.md','Actualtenpublic/canarytypes/fiveborrowedcompileddefinitionbinders/elevenAPIs/native retrieval/ready1proof169refs2pairs/selected10nodes8proof2TESTdefs/tenkernelchecksoneguard. Singleexisting producer/full7canaries, no newgeneric theorem/externalcompatible rebuild/pin/globalindex/perBook library. Onehighlight/curatedlink/sourcecard,threenotation/onecanonicalpublicnode/10811registry. '+digest)
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write(RUN/'candidate-scoped-trials-v2.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==TASK))
event('candidate',dict(frozen_headers=f['headers'],sequential_jobs=jobs,source_package_accepted=False,remaining_gates=['fullharness','exactcontributor/diff/history','site/registry/pixels/FINAL/native','rawPR']))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native('candidate-frontier-refresh-v2','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only Theorem2.28 candidate, chapter/book incomplete','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'theorem_2_28'),'--declaration',PRE+'theorem_2_28','--file',PUBLIC,'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:'+PRE+'SourceSubdifferential:compiled','--dependency','review:source-body:accepted','--trials',RUN/'candidate-scoped-trials-v2.jsonl','--output',RUN/'candidate-frontier-v2.json','--shadow-status','pending')
native('candidate-frontier-shadow-v2','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v2.jsonl','--memory-digest',RUN/'memory-digest-candidate-v2.md','--frontier',RUN/'candidate-frontier-v2.json')
fixed(True);gate('full-harness-v2-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
print('Current postcomment rootTests/fullharness/task-onlyshadow pass; remaining package/wholeGoal obligations separate.')
