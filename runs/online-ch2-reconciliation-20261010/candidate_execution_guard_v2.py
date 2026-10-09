from integration_guard_v2 import *
import fnmatch

def candidate_plan_fixed():
    p=RUN/'candidate-git-site-plan-review-v1.json'
    assert sha(p)=='ff2d8854b7e320e4b94a38958d958eacfaf34a8cc029e11fb7b3b915ed113585'
    r=load(p);assert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
    a=load(RUN/'prospective-CRLF-attributes-plan-v3.json')
    assert sha(a['path'])==a['after_sha256']==sha(a['after_snapshot'])
    original=base64.b64decode(a['before_raw_base64']);assert hashlib.sha256(original).hexdigest()==a['before_sha256']
    for row in load(r['input_manifest'])['rows']:
        if row['path']==a['path']:assert row['sha256']==a['before_sha256']
        else:assert sha(row['path'])==row['sha256'],row['path']
    for row in r['approved_helper_hashes']:assert sha(row['path'])==row['sha256']
    s=load(RUN/'candidate-execution-repair-review-v2.json')
    assert s['verdict']=='accepted-with-explicit-delta' and not s['required_repairs']
    assert sha(s['report'])==s['report_sha256'] and sha(s['input_manifest'])==s['input_manifest_sha256']
    for row in load(s['input_manifest'])['rows']:
        if row['path']==a['path']:assert row['sha256']==a['before_sha256']
        else:assert sha(row['path'])==row['sha256'],row['path']
    for row in s['approved_helper_hashes']:assert sha(row['path'])==row['sha256']
    old=load(RUN/'candidate-binary-artifacts-bound-v1.json')['rows']
    current=[]
    for p in RUN.rglob('*'):
        if p.is_file():
            rel=p.relative_to(RUN).as_posix()
            if p.suffix=='.raw' or fnmatch.fnmatch(rel,'forward-readonly-retrieval/*.txt') or p.name=='integration_guard_v1.py':current.append(p.as_posix())
    assert set(current)=={x['path'] for x in old}
    for row in old:assert sha(row['path'])==row['sha256']
    fixed()

def exact_cached_scope():
    plan=load(RUN/'candidate-stage-plan-v1.json');stage=plan['stage']
    changed=subprocess.check_output(['git','diff','--cached','--name-only',BASE],encoding='utf8').splitlines()
    baseline={Path(r['path']).relative_to(ROOT).as_posix() for r in load(RUN/'baseline-v1.json')['rows']}
    assert set(changed)&baseline==set(plan['old_changed_paths'])
    for p in changed:assert any(p==s or p.startswith(s+'/') for s in stage),p
    for rel in ['BanditRLProof/OnlineFTLSelector.lean','Tests/OnlineFTLSelectorCanary.lean']:
        assert subprocess.check_output(['git','show',':'+rel])==(ROOT/rel).read_bytes()
    return changed
