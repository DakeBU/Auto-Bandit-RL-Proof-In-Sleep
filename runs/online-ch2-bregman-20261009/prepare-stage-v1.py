from publication_guard_v1 import *
fixed()
assert load(RUN/'full-harness-inspected-v1.json')['actual_check_passed']
stage=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'BanditRLProof.lean','Tests.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix()]
stage += [x+'/'+TASK+'.md' for x in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']]
write(RUN/'candidate-stage-plan-v1.json',dict(stage=stage,allowed_old_paths=[x['path'] for x in load(CONTRACT/'exact-publication-plan-v2.json')['rows']],no_merge_deploy_retirement=True,whole_Goal_status='ACTIVE'))
capture('candidate-stage-v1','git','add',*stage)
changed=subprocess.check_output(['git','diff','--cached','--name-only',BASE],encoding='utf8').splitlines()
allowed_old={Path(x['path']).relative_to(ROOT).as_posix() for x in load(CONTRACT/'exact-publication-plan-v2.json')['rows']}
basepaths={Path(x['path']).relative_to(ROOT).as_posix() for x in load(RUN/'baseline-v1.json')['rows']}
assert set(changed)&basepaths==allowed_old
for path in changed:
    assert any(path==a or path.startswith(a+'/') for a in stage),path
rc,out=capture('candidate-full-diff-check-v1','git','diff','--cached',BASE,'--check',required=False)
assert rc==0,out
write(RUN/'candidate-diff-audit-v1.json',dict(full_whitespace_gate_passed=True,actual_full_exit=rc,changed_count=len(changed),changed_paths=changed,only_five_old_paths_changed=True,all_other_baseline_immutable=True,RAW_EOF_exceptions=[],whole_Goal_status='ACTIVE'))
fixed()
print('Exact scoped staging and full package whitespace actual0; no EOF exemptions.')
