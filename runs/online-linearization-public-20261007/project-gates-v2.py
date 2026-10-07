from common_v2 import *
fixed(True);assert load(RUN/'reader-integration-v2.json')['new_proofs']==0
gate('combined-root-v2','lake','build');gate('combined-Tests-v2','lake','build','Tests');gate('full-harness-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
jobs={}
for label in ['combined-root-v2','combined-Tests-v2']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
raw=(RUN/'full-harness-v2.log').read_text(encoding='utf-8');tests=re.search(r'Ran (\d+) tests?',raw);skips=re.search(r'OK \(skipped=(\d+)\)',raw)
assert tests and 'check passed' in raw and 'FAILED (' not in raw
write(RUN/'combined-gates-v2.json',dict(status='actual-root-Tests-full-harness-passed',jobs_including_cached=jobs,full_tests=int(tests.group(1)),existing_skips=int(skips.group(1)) if skips else 0,current_reader_included=True,new_proofs=0,new_definitions=0,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True);print('Actual combined gates passed:',jobs,'tests',tests.group(1),'skips',skips.group(1) if skips else 0)
