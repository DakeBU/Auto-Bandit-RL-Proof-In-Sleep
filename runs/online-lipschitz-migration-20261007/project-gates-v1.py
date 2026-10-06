"""Only after real reader integration and both frozen guards, run combined Lean gates."""
from common_v2 import *
f=fixed(True)
manifest='research-wiki/contribution-contracts/online-lipschitz-migration-20261007.json'
assert load(RUN/'reader-integration-v1.json')['publication']==manifest
assert load(RUN/'integrated-public-guard-audit-v1.json')['status']=='passed'
assert load(RUN/'public-comment-qualification-v1.json')['exact_original_raw_suffix']
assert load(RUN/'body-binding-audit-v1.json')['status']=='passed-at-review-boundary'
gate('root-v1-01','lake','build','BanditRLProof')
gate('Tests-v1-01','lake','build','Tests')
assert passed('Tests-v1-01')['started_at']>=passed('root-v1-01')['ended_at']
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
write(RUN/'proof-obligations-candidate-v1.json',dict(stage='candidate',required=[dict(name=PRE+n,statement_hash=h,state='retained exactbody compiled; CONTRACT/convention/BODY accepted; fullharness/siteFINAL pending') for n,h in f['headers'].items()],sequential_project_jobs=jobs,retained_proofs=1,retained_definitions=1,new_public_proofs=0,whole_canary_proofs=18,whole_canary_definitions=6,whole_canary_abbreviations=2,named_kernel_checks=28,native_guards=2,source_package_accepted=False,chapter_complete=False,goal_complete=False))
delta=load(manifest)['truth_boundary'];digest=TASK+' — '+delta+' CurrentCONTRACT/convention/BODY accepted, postcomment rootTests pass/fullharness/siteFINAL/nativePRpending. Legacyqueue0notchaptertotal; globalSGBfixed/task-onlyfrontier/GoalACTIVE. No mainlive.'
write(RUN/'memory-digest-candidate-v1.md',digest);write(RUN/'retrieval-index-candidate-v1.md','Actual28types/sixdefinitionbinders/12APIs/native retrieval/ready2nodes260refs4actualpairs/selected28nodes1819refs14pairs/28kernel2guards/2canonicalhighlightcuratedsourcecards/3notation/10811IDsURLs. Not fullregistrygraph/newmath. '+digest)
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==TASK))
event('candidate',dict(frozen_headers=f['headers'],sequential_jobs=jobs,source_package_accepted=False,remaining_gates=['fullharness','exactcontributor/diff/history','site/registry/pixels/FINAL/native','rawPR']))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only Definition2.29/Theorem2.30 candidate, chapter/book incomplete','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'theorem_2_30'),'--declaration',PRE+'theorem_2_30','--file',PUBLIC,'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:'+PRE+'subgradient_exists_of_domain_interior:compiled','--dependency','review:source-body:accepted','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed(True);gate('full-harness-v1-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
print('Current postcomment rootTests/fullharness/task-onlyshadow pass; FINAL/native/PR separate, GoalACTIVE.')
