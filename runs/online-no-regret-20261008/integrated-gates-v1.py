from common_integrated_v1 import *
fixed_integrated()
owned=[PUBLIC.as_posix(),CANARY.as_posix(),CONTRACT.as_posix(),RUN.relative_to(ROOT).as_posix(),MANIFEST.as_posix(),'BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json','MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl','runs/trials.jsonl']+[folder+'/'+TASK+'.md' for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']]
write(RUN/'owned-commit-paths-v1.json',owned)
for label,args in [('contributor',[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--help']),('site-build',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--help']),('site-check',[sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--help']),('frontier-refresh',[sys.executable,'-B','-X','utf8','tools/bandit.py','frontier-refresh','--help']),('frontier-shadow',[sys.executable,'-B','-X','utf8','tools/bandit.py','frontier-shadow','--help'])]:gate('help-'+label+'-v1',*args)
gate('scope-pre-gates-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','pre-gates-v1')
gate('stage-owned-public-tests-v1','git','add','--',PUBLIC,CANARY)
baseline=Path('tmp/online-log-lower-site-v2/books/registry.json')
assert sha(baseline)==load('runs/online-log-lower-20261008/registry-v3.json')['registry_sha256']
assert len(load(baseline)['nodes'])==10894
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip()]
trials=[x for x in trials if x.get('task')==TASK];assert trials
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(x,ensure_ascii=False) for x in trials))
header=next(x['header'] for x in load(CONTRACT/'targets-v1.json')['targets'] if x['name']==PRE+'NoRegretCounterexample.strict_separation')
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1–16; exact C1 no-regret semantic reconciliation','--leaf',TASK,'--kind','lean','--statement',header,'--declaration',PRE+'NoRegretCounterexample.strict_separation','--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','review:source-body:accepted','--dependency','lean:'+PRE+'NoRegretCounterexample.noRegret:compiled','--dependency','lean:'+PRE+'NoRegretCounterexample.no_limit:compiled','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory_digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
gate('combined-root-v1','lake','build')
gate('combined-Tests-v1','lake','build','Tests')
native('full-harness-v1','check')
gate('contributor-exact-base-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v1','git','diff','--check',BASE)
write(RUN/'integrated-gates-v1.json',dict(status='Actual combined root/Tests/fullharness/ownshadow/exact-base contributor/diff gates passed',root_log_sha256=sha(RUN/'combined-root-v1.log'),Tests_log_sha256=sha(RUN/'combined-Tests-v1.log'),harness_log_sha256=sha(RUN/'full-harness-v1.log'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),globalSGB_unchanged=True,clean_site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
fixed_integrated();print('Combined shared project gates passed; clean site and FINAL review remain.')
