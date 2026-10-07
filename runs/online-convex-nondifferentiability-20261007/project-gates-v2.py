"""Preserve failed harness v1; satisfy existing tracked-source fence and rerun."""
from common_v4 import *
fixed(True,True)
assert load(RUN/'full-harness-v1-01-exit.json')['exit_code']==1
assert load(RUN/'project-gates-v1-01-exit.json')['exit_code']==1
failure=(RUN/'full-harness-v1-01.log').read_text(encoding='utf-8')
assert 'ValueError: untracked Lean source under allowlisted tree: '+PUBLIC.as_posix() in failure
before={str(p):sha(p) for p in [PUBLIC,CANARY,Path('BanditRLProof.lean'),Path('Tests.lean')]}
subprocess.run(['git','add','--',str(PUBLIC),str(CANARY)],check=True)
tracked=set(subprocess.check_output(['git','ls-files'],text=True).splitlines())
assert PUBLIC.as_posix() in tracked and CANARY.as_posix() in tracked
assert before=={p:sha(p) for p in before}
write(RUN/'harness-tracked-source-repair-v2.json',dict(failed_attempt='full-harness-v1-01',reason='Existing anonymous supplement test uses git ls-files and rejects untracked Lean sources',repair='Stage only the two owned new Lean files; no source/header/test/runtime changes',source_hashes=before,existing_test_preserved=True,chapter_complete=False,goal_complete=False))
event('repair',dict(reason='Harness tracked-source fence; index-only repair',failed_attempt='full-harness-v1-01',source_unchanged=True),attempt='harness-v2')
gate('root-v2-01','lake','build','BanditRLProof')
gate('Tests-v2-01','lake','build','Tests')
assert passed('Tests-v2-01')['started_at']>=passed('root-v2-01')['ended_at']
gate('full-harness-v2-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
fixed(True,True)
jobs={}
for label in ['root-v2-01','Tests-v2-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m; jobs[label]=int(m.group(1))
write(RUN/'combined-project-gates-v2.json',dict(status='passed',actual_labels=['root-v2-01','Tests-v2-01','full-harness-v2-01'],sequential_jobs=jobs,preserved_failure='full-harness-v1-01',index_only_repair=True,source_hashes=before,chapter_complete=False,goal_complete=False))
print('Actual shared root, Tests and full harness v2 passed; prior v1 failure preserved. FINAL/site/native/PR remain separate.')
