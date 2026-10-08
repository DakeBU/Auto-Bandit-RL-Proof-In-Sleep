from common_delivery_v5 import *

delivery_fixed()
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
assert subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BRANCH],encoding='utf8').split()[0]==head
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/194']))
assert pr['head']['sha']==head and pr['base']['ref']==BASE_BRANCH and pr['draft'] and pr['state']=='open' and not pr['merged']
assert pr['body'].replace('\r\n','\n').strip()==(RUN/'prospective-pr-body-v5.md').read_text(encoding='utf8').strip()
tracked=subprocess.check_output(['git','ls-files','--',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),PUBLIC.as_posix(),CANARY.as_posix(),
    MANIFEST.as_posix(),*[folder+'/'+TASK+'.md' for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']]],encoding='utf8').splitlines()
for p in tracked:
    assert subprocess.check_output(['git','show','HEAD:'+p])==Path(p).read_bytes(),p
for p in ['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']:
    old=(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes()
    assert Path(p).read_bytes().startswith(old),p
    assert subprocess.check_output(['git','show','HEAD:'+p]).startswith(subprocess.check_output(['git','show',BASE+':'+p])),p
    if p.endswith('.jsonl'):
        for line in Path(p).read_bytes()[len(old):].decode('utf8').splitlines():
            if line.strip():
                row=json.loads(line)
                assert row.get('task',row.get('session_id'))==TASK
canonical=Path('E:/ABRL/research')
assert not subprocess.check_output(['git','-C',str(canonical),'status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
print(json.dumps(dict(status='passed DIRECT; no file writes',PR=194,head=head,local_dirty=False,remote_and_REST_exact=True,
    exact_raw_tracked_files=len(tracked),four_historical_globals_separate_working_and_Git_prefixes_preserved=True,
    original_12_exception_hashes_unchanged=True,delivery_bound_raw_evidence_files=14,
    canonical_head=subprocess.check_output(['git','-C',str(canonical),'rev-parse','HEAD'],encoding='utf8').strip(),
    chapter_complete=False,goal_complete=False,merged=False,live=False,worktree_retained=True)),flush=True)
