from common_v1 import *
headers();b=load(RUN/'body-bindings-v1.json');assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
for path,line in [('BanditRLProof.lean','import BanditRLProof.OnlineGuessingSubgradientPolicy'),('Tests.lean','import Tests.OnlineGuessingSubgradientPolicyCanary')]:
 p=Path(path);before=(RUN/'snapshots'/path).read_bytes();assert p.read_bytes()==before
 assert line.encode() not in before;p.write_bytes(before+(b'' if before.endswith(b'\n') else b'\n')+line.encode()+b'\n')
write(RUN/'combined-imports-v1.json',dict(status='additive-shared-project-imports',rows=[dict(path=p,before_sha256=sha(RUN/'snapshots'/p),after_sha256=sha(p)) for p in ['BanditRLProof.lean','Tests.lean']],single_shared_Lean_registry=True,combined_gate='pending',other_imports_preserved=True,source_BODY_pending=True,chapter_complete=False,goal_complete=False))
gate('combined-root-v1-01','lake','build')
gate('combined-Tests-v1-01','lake','build','Tests')
gate('full-harness-v1-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
jobs={}
for label in ['combined-root-v1-01','combined-Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
raw=(RUN/'full-harness-v1-01.log').read_text(encoding='utf-8')
tests=re.search(r'Ran (\d+) tests',raw);skips=re.search(r'OK \(skipped=(\d+)\)',raw)
assert tests and 'build failed' not in raw and 'FAILED (' not in raw
write(RUN/'combined-gates-v1.json',dict(status='actual-root-Tests-full-harness-passed',jobs_including_cached=jobs,full_tests=int(tests.group(1)),existing_skips=int(skips.group(1)) if skips else 0,raw_log_rows=[dict(label=x,sha256=sha(RUN/(x+'.log')),receipt_sha256=sha(RUN/(x+'-exit.json'))) for x in ['combined-root-v1-01','combined-Tests-v1-01','full-harness-v1-01']],public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),source_BODY_review='separate',reader_FINAL_site='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
headers();print('Current combined root/Tests/full harness gates actually passed;',jobs,'tests',tests.group(1),'site/FINAL separate.')
