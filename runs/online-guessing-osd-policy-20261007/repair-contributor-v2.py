"""Use actual contributor CLI production-file schema; retain tests in owned verification fields."""
from common_v1 import *
headers();assert load(RUN/'contributor-exact-v1-01-exit.json')['exit_code']==1
manifest=Path('research-wiki/contribution-contracts/online-guessing-osd-policy-20261007.json')
write(RUN/'snapshots/contribution-before-production-schema-repair-v2.json',manifest.read_bytes())
c=load(manifest);assert CANARY.as_posix() in c['affected_files'] and 'Tests.lean' in c['affected_files']
c['affected_files']=[p for p in c['affected_files'] if p not in [CANARY.as_posix(),'Tests.lean']]
assert c['verification']['owned_test_files']==[CANARY.as_posix()] and c['verification']['owned_test_root_files']==['Tests.lean']
manifest.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
write(RUN/'contributor-metadata-repair-v2.json',dict(status='metadata-only production coverage repair',original_failure='contributor-exact-v1-01',actual_CLI_rule='affected_files must match changed protected/production surfaces; Tests and Tests.lean are not those surfaces.',repair='Remove two test paths from affected_files only; retain both actual files and owned verification fields.',public_and_canary_bytes_unchanged=True,frozen_types_unchanged=True,chapter_complete=False,goal_complete=False))
native('contributor-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,failed_gate='contributor-exact-v1-01',metadata_repair='Separate production affected_files from owned test files; exact actual CLI schema.',no_math_change=True,chapter_complete=False,goal_complete=False)))
native('contributor-repair-resume-v2','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,metadata_only=True,frozen_types_unchanged=True,chapter_complete=False,goal_complete=False)))
native('contributor-repaired-candidate-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,contributor_gate_rerun=True,reader_FINAL_pending=True,chapter_complete=False,goal_complete=False)))
text=(RUN/'source-site-gates-v1.py').read_text(encoding='utf-8').replace("'contributor-exact-v1-01'","'contributor-exact-v2-01'").replace("'Prove absolute-loss regret for played-legal finite-history OSD policies'","'Align guessing-policy contribution production and test coverage fields'")
write(RUN/'source-site-gates-v2.py',text)
headers();print('Only contributor production/test annotations repaired; original failure retained, exact gate rerun prepared.')
