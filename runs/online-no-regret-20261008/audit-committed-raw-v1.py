from common_accepted_v1 import *
accepted_fixed()
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
scopes=[RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),PUBLIC.as_posix(),CANARY.as_posix()]
extra=[p for p in load(RUN/'owned-commit-paths-v2.json') if Path(p).is_file() and p not in scopes and p!=APPEND_PATH]
scopes+=extra
entries=subprocess.check_output(['git','ls-tree','-r','-z',head,'--',*scopes]).split(b'\0')
objects={e.split(b'\t',1)[1].decode('utf8'):e.split(b'\t',1)[0].split()[2].decode('ascii') for e in entries if e}
files=[p for root in [RUN,CONTRACT] for p in sorted(root.rglob('*')) if p.is_file()]+[PUBLIC,CANARY]+[Path(p) for p in extra]
rels=list(dict.fromkeys(p.resolve().relative_to(ROOT).as_posix() for p in files))
ignored_query=subprocess.run(['git','check-ignore','--stdin','-z'],input=('\0'.join(rels)+'\0').encode('utf8'),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
assert ignored_query.returncode in [0,1]
ignored=set(x.decode('utf8') for x in ignored_query.stdout.split(b'\0') if x)
checked=[p for p in rels if p not in ignored]
assert all(p in objects for p in checked),[p for p in checked if p not in objects]
raw=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(objects[p] for p in checked)+'\n').encode('ascii'))
cursor=0;rows=[]
for p in checked:
    end=raw.index(b'\n',cursor);header=raw[cursor:end].decode('ascii').split()
    assert header[0]==objects[p] and header[1]=='blob'
    size=int(header[2]);cursor=end+1;content=raw[cursor:cursor+size];cursor+=size+1
    assert raw[cursor-1:cursor]==b'\n'
    h=hashlib.sha256(content).hexdigest();assert h==sha(p),p
    rows.append(dict(path=p,git_blob=objects[p],sha256_raw_bytes=h))
assert cursor==len(raw)
# Explicit inherited mixed-line-ending representation: never normalize a receipt.
base_bytes=subprocess.check_output(['git','show',BASE+':'+APPEND_PATH])
git_bytes=subprocess.check_output(['git','show',head+':'+APPEND_PATH])
original=RUN/'snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw'
addition=RUN/'Asymptotic-source-comment-addition-v3.txt'
assert len(base_bytes)==1374 and len(original.read_bytes())==1407
assert git_bytes==base_bytes+addition.read_bytes()
assert Path(APPEND_PATH).read_bytes()==original.read_bytes()+addition.read_bytes()
representations=dict(path=APPEND_PATH,base_Git_blob_sha256=hashlib.sha256(base_bytes).hexdigest(),
    current_Git_blob_sha256=hashlib.sha256(git_bytes).hexdigest(),
    original_worktree_raw_sha256=sha(original),current_worktree_raw_sha256=sha(APPEND_PATH),
    exact_addition_sha256=sha(addition),Git_base_prefix_bytes=1374,worktree_original_prefix_bytes=1407,
    same_exact_677_byte_addition=True,original_raw_CRLF_count=33,base_Git_CRLF_count=0,
    raw_representation_hashes_are_distinct=True,no_hash_normalization=True,
    separately_reviewed_raw_prefix_and_actual_Git_prefix_each_preserved=True)
if len(sys.argv)>1 and sys.argv[1]=='direct':
    assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BRANCH],encoding='utf8').split()[0]
    assert remote==head
    pr=load(RUN/'created-PR-v1.json')
    current=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(pr['number'])]))
    assert current['head']['sha']==head and current['state']=='open' and current['draft'] and not current['merged']
    assert current['body'].replace('\r\n','\n').strip()==(RUN/'PR-body-v2.md').read_text(encoding='utf8').strip()
    print(json.dumps(dict(status='DIRECT-no-file-write-passed',head=head,local_remote_REST_equal=True,clean=True,
        actual_raw_files_verified=len(rows),ignored_runtime_files_preserved=len(ignored),
        Asymptotic_exact_two_representation_prefixes_plus_same_addition=True,
        PR=current['html_url'],PRstate='OPEN-DRAFT-unmerged',goal_complete=False,chapter_complete=False,main_live_unchanged=True)))
else:
    write(RUN/'committed-raw-audit-v1.json',dict(status='passed-at-explicit-audited-head',audited_head=head,
        raw_files=len(rows),rows=rows,ignored_files_preserved=sorted(ignored),
        batch_Git_blobs_rehashed_without_normalization=True,scope=scopes,
        inherited_Asymptotic_exact_raw_and_Git_representations=representations,
        final_DIRECT_audit_no_self_head_write=True,chapter_complete=False,goal_complete=False))
    print('Actual',len(rows),'raw files equal Git blobs; inherited Asymptotic prefixes separately exact in both representations.')
