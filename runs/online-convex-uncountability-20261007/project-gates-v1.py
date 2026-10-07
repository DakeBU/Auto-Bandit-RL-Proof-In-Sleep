"""Actual sequential shared root, Tests and full harness; no source acceptance inference."""
from common_v2 import *
fixed(True,True);passed('integrate-reader-v1-01')
gate('root-v1-01','lake','build','BanditRLProof')
gate('Tests-v1-01','lake','build','Tests')
assert passed('Tests-v1-01')['started_at']>=passed('root-v1-01')['ended_at']
gate('full-harness-v1-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m; jobs[label]=int(m.group(1))
raw=(RUN/'full-harness-v1-01.log').read_text(encoding='utf-8');m=re.search(r'Ran (\d+) tests?',raw);assert m
sk=re.search(r'OK \(skipped=(\d+)\)',raw);assert sk
write(RUN/'combined-project-gates-v1.json',dict(status='passed',actual_labels=['root-v1-01','Tests-v1-01','full-harness-v1-01'],root_Tests_jobs=jobs,full_tests=int(m.group(1)),existing_skips=int(sk.group(1)),cached_jobs_included=True,new_public_proofs=2,new_definitions=0,new_canary_proofs=4,current_reader_sources_included=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True,True);print('Actual root/Tests/full harness pass',jobs,'tests',m.group(1),'existing skips',sk.group(1),'; site/FINAL/native/PR pending.')
