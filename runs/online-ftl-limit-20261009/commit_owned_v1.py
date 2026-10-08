from common_accepted_v2 import *
OWNED={CONTRIBUTION.relative_to(ROOT).as_posix(),'runs/lifecycle_sessions.jsonl',
    *[p.relative_to(ROOT).as_posix() for p in APPEND_METADATA]}
PREFIX=[RUN.relative_to(ROOT).as_posix()+'/',CONTRACT.relative_to(ROOT).as_posix()+'/']
def owned(p):
    return p in OWNED or any(p.startswith(x) for x in PREFIX)
def stage_owned():
    changed=subprocess.check_output(['git','diff','HEAD','--name-only','-z']).decode('utf8').split('\0')
    others=subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z']).decode('utf8').split('\0')
    paths=sorted(set(p for p in changed+others if p))
    assert all(owned(p) for p in paths),[p for p in paths if not owned(p)]
    for i in range(0,len(paths),60):
        subprocess.run(['git','add','--',*paths[i:i+60]],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
    staged=subprocess.check_output(['git','diff','--cached','--name-only','-z']).decode('utf8').split('\0')
    assert all(owned(p) for p in staged if p)
def post_fixed():
    accepted_fixed()
    r=load(RUN/'post-native-receipt-v1.json')
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert r['inputs_unchanged'] and not r['required_blocking_repairs']
    assert r['report_sha256']==sha(RUN/'post-native-review-v1.md')
    assert all(sha(x['path'])==x['sha256'] for x in load(RUN/'post-native-review-inputs-v1.json')['rows'])
    return r
def commit_owned(message,label):
    post_fixed();stage_owned()
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    assert subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').strip()
    log=ROOT/'tmp'/(TASK+'-'+label+'.log');assert not log.exists()
    command=['git','commit','-m',message];tick=time.monotonic()
    with log.open('wb') as stream:
        child=subprocess.run(command,cwd=str(ROOT),stdout=stream,stderr=subprocess.STDOUT)
    receipt=dict(command=command,cwd=ROOT.as_posix(),actual_exit=child.returncode,
        seconds=time.monotonic()-tick,log_sha256=sha(log),log_path=log.as_posix())
    write(log.with_suffix('.json'),receipt)
    assert child.returncode==0
    assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
    receipt['actual_head']=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
    receipt['actual_clean_after_commit']=True
    print('Actual reviewed owned commit:',receipt['actual_head'],flush=True)
    return receipt
