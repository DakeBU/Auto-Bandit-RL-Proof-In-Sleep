from common_v1 import *
fixed(proving=True,integrated=True)
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Implement reviewed general-initial FTL and recursive mean/count state'],check=True)
gate('combined-root-v1','lake','build')
gate('combined-Tests-v1','lake','build','Tests')
native('full-harness-v1','check')
jobs={}
for label in ['combined-root-v1','combined-Tests-v1']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
raw=(RUN/'full-harness-v1.log').read_text(encoding='utf-8');tests=re.search(r'Ran (\d+) tests?',raw);skips=re.search(r'OK \(skipped=(\d+)\)',raw)
assert tests and 'check passed' in raw and 'FAILED (' not in raw
write(RUN/'combined-gates-v1.json',dict(status='actual-root-Tests-full-harness-passed',jobs_including_cached=jobs,full_tests=int(tests.group(1)),existing_skips=int(skips.group(1)) if skips else 0,current_reader_and_six_tests_included=True,new_public_math=9,new_public_definitions=3,new_named_validation_proofs=6,source_subobligations=2,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(proving=True,integrated=True)
