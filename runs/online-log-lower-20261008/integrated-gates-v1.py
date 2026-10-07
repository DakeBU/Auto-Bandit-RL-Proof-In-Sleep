from common_integrated_v1 import *
fixed_integrated()
for label,p in [('contributor','tools/check_contributor_contract.py'),('site-build','website/scripts/build_site.py'),('site-check','website/scripts/check_site.py')]:gate('help-'+label+'-v1',sys.executable,'-B','-X','utf8',p,'--help')
gate('scope-pre-gates-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','pre-gates-v1')
gate('stage-owned-public-tests-v1','git','add','--',PUBLIC,CANARY)
baseline=Path('tmp/online-regret-domains-site-v1/books/registry.json')
assert sha(baseline)==load('runs/online-regret-domains-20261007/registry-v4.json')['registry_sha256']
assert len(load(baseline)['nodes'])==10835
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip()]
trials=[x for x in trials if x.get('task')==TASK];assert trials
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(x,ensure_ascii=False) for x in trials))
header=load(CONTRACT/'planned-public-headers-v1.json')
print('frozen header schema',type(header).__name__,flush=True)
statement=PUBLIC.read_text(encoding='utf8').split('theorem randomized_log_lower ',1)[1].split(':= by',1)[0]
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1–16; actual C1 logarithmic lower producer','--leaf',TASK,'--kind','lean','--statement','theorem randomized_log_lower '+statement,'--declaration',PRE+'randomized_log_lower','--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','review:source-body:accepted','--dependency','lean:'+PRE+'randomized_harmonic_lower:compiled','--dependency','lean:log_add_one_le_harmonic:compiled','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory_digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
gate('combined-root-v1','lake','build')
gate('combined-Tests-v1','lake','build','Tests')
native('full-harness-v1','check')
write(RUN/'integrated-gates-v1.json',dict(status='Actual root/Tests/fullharness/shadow commands passed',root_log_sha256=sha(RUN/'combined-root-v1.log'),Tests_log_sha256=sha(RUN/'combined-Tests-v1.log'),harness_log_sha256=sha(RUN/'full-harness-v1.log'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),nonvacuous_contributor_clean_site_FINAL_PR_pending=True,chapter_complete=False,goal_complete=False))
fixed_integrated()
