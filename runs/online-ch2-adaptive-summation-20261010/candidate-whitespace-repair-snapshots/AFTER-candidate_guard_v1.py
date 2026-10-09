from integration_guard_v1 import *

PLAN=RUN/'candidate-stage-plan-v1.json'
REVIEW=RUN/'candidate-git-site-plan-review-v1.json'

def candidate_fixed():
    fixed()
    d=load(REVIEW)
    assert d['verdict'] in ['accepted','accepted-with-explicit-delta'] and not d['required_repairs']
    assert sha(d['report'])==d['report_sha256'] and sha(d['input_manifest'])==d['input_manifest_sha256']
    for row in load(d['input_manifest'])['rows']: assert sha(row['path'])==row['sha256'],row['path']
    assert d['approved_stage_plan_sha256']==sha(PLAN)
    for row in d['approved_helper_hashes']: assert sha(row['path'])==row['sha256'],row['path']

def exact_cached_scope():
    plan=load(PLAN)
    changed=subprocess.check_output(['git','diff','--cached','--name-only',BASE],encoding='utf8').splitlines()
    baseline={Path(r['path']).relative_to(ROOT).as_posix() for r in load(RUN/'baseline-v1.json')['rows']}
    assert set(changed)&baseline==set(OLD_ALLOWED)
    for p in changed: assert any(p==s or p.startswith(s+'/') for s in plan['stage']),p
    # One binary-safe batch reads every staged changed blob; compare actual RAW worktree bytes.
    requests=''.join(':'+p+'\n' for p in changed).encode('utf8')
    batch=subprocess.run(['git','cat-file','--batch'],input=requests,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=ROOT)
    assert batch.returncode==0,batch.stderr.decode('utf8',errors='replace')
    data=batch.stdout;cursor=0;bindings=[]
    for p in changed:
        end=data.index(b'\n',cursor);header=data[cursor:end].split();assert len(header)==3 and header[1]==b'blob',p
        size=int(header[2]);blob=data[end+1:end+1+size];cursor=end+1+size
        assert data[cursor:cursor+1]==b'\n';cursor+=1
        assert blob==(ROOT/p).read_bytes(),p
        bindings.append(dict(path=p,sha256=hashlib.sha256(blob).hexdigest(),bytes=size,index_equals_RAW=True))
    assert cursor==len(data)
    return changed,bindings

def actual_gates_fixed():
    d=load(RUN/'full-harness-inspected-v1.json')
    assert d['actual_exit']==0 and d['actual_check_passed'] and d['actual_ProofGraphExport_compile_present']
    assert d['unittest_runs'] and d['cached_inclusive_successful_build_jobs']
    assert sha(RUN/'combined-full-harness-v1.json')==d['command_receipt_sha256']
    for key,p in [('production_sha256',MODULE),('Test_sha256',TEST),('root_sha256',ROOT/'BanditRLProof.lean'),('Test_root_sha256',ROOT/'Tests.lean')]: assert sha(p)==d[key]
    for p,h in d['source_pins'].items(): assert sha(ROOT/p)==h
    roots=load(RUN/'combined-root-Tests-inspected-v1.json')
    assert roots['root_Tests_passed'] and {r['target'] for r in roots['rows']}=={'BanditRLProof','Tests'}
    for r in roots['rows']: assert r['actual_exit']==0 and r['cached_inclusive_jobs'] and sha(RUN/('combined-root-v1.json' if r['target']=='BanditRLProof' else 'combined-Tests-v1.json'))==r['receipt_sha256']
