"""Resume only the missing native events after the preserved Python payload failure."""
from common_v2 import *
fixed(True)
assert load(RUN/'record-acceptance-v4-01-exit.json')['exit_code']==1
assert "multiple values for keyword argument 'chapter_complete'" in (RUN/'record-acceptance-v4-01.log').read_text(encoding='utf-8')
passed('accepted-reviewer-trial-v1')
assert not (RUN/'accepted-lifecycle-v1-exit.json').exists()
assert not (RUN/'native-acceptance-overlay-v1.json').exists()
final=load(RUN/'final-reader-receipt-v2.json')
assert final['actor']['task']=='/root/source_reviewer' and final['verdict']=='accepted-with-explicit-delta'
assert sha(final['report'])==final['report_sha256']
assert all(r['verdict']=='satisfied' for r in final['reader_requirement_verdicts'].values())
assert final['repair_verdict']['M5']['verdict']=='satisfied'
a=load(RUN/'accepted-decision-v1.json');f=fixed(True)
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert a['public_module_sha256']==sha(PUBLIC) and a['canary_sha256']==sha(CANARY)
assert a['raw_headers']==f['raw_headers'] and a['native_headers']==f['native_headers']
for r in load(RUN/'accepted-binding-audit-v1.json')['rows']:
 assert sha(r['resolved_raw_file'])==r['sha256']
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
accepted=[r for r in trials if r.get('task')==TASK and r.get('attempt_id')=='OSD-PUBLIC-REUSE-V1' and r.get('status')=='accepted']
assert len(accepted)==1,accepted
existing=['accepted-decision-v1.json','accepted-binding-audit-v1.json','accepted-reader-discharge-v1.json','accepted-obligations-v1.json','accepted-scoped-trials-v1.jsonl']
write(RUN/'native-acceptance-repair-v1.json',dict(status='metadata repair; native replay pending',cause='The wrapper inserts chapter_complete/goal_complete; duplicate keys in the accepted payload raised TypeError before invoking the accepted lifecycle CLI.',failed_wrapper='record-acceptance-v4-01',actual_reviewer_trial_already_passed=True,reviewer_trial_replayed=False,existing_rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in existing],repair='Call existing event wrapper with only nonreserved payload keys; run only previously unexecuted native accepted event/frontier/shadow.',target_reader_and_proof_unchanged=True,source_package_only=True,chapter_complete=False,goal_complete=False))
event('repair',dict(native_metadata_repair=(RUN/'native-acceptance-repair-v1.json').as_posix(),target_reader_and_proof_unchanged=True),attempt='native-v5')
event('accepted',dict(accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(),source_package_accepted=True,new_proofs=0,new_definitions=0,merged=False,live=False),attempt='native-v5')
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native('accepted-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; existing canonical OSD reuse audit accepted only, generic policy and chapters REQUIRED','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'regret_tuned'),'--declaration',PRE+'regret_tuned','--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:'+PRE+'regret_tuned_distance:compiled','--dependency','lean:'+PRE+'regret_fixed:compiled','--dependency','review:source-reader:accepted','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
fixed(True)
for r in load(RUN/'native-acceptance-repair-v1.json')['existing_rows']:assert sha(r['path'])==r['sha256']
write(RUN/'native-acceptance-overlay-v1.json',dict(status='passed',accepted_decision_sha256=sha(RUN/'accepted-decision-v1.json'),actual_attempt='OSD-PUBLIC-REUSE-V1',globalSGB_unchanged=True,PR_delivery_pending=True,source_package_accepted=True,chapter_complete=False,goal_complete=False,preserved_actual_failure='record-acceptance-v4-01',effective_repair='record-acceptance-repair-v5.py',separate_metadata_repair_review_pending=True))
print('Previously missing native accepted event/frontier/shadow passed; original partial outputs/trial preserved; separate metadata review pending.')
