from common_accepted_v1 import *
accepted_fixed()
scopes=load(RUN/'owned-commit-paths-v2.json')
tracked=subprocess.check_output(['git','ls-files','-z','--',*scopes]).split(b'\0')
rows=[]
for token in tracked:
    if not token:
        continue
    p=token.decode('utf8')
    if p==APPEND_PATH:
        continue  # Separately exact BASE Git prefix and reviewed worktree prefix.
    w=Path(p).read_bytes();g=subprocess.check_output(['git','show','HEAD:'+p])
    if w!=g:
        assert w.replace(b'\r\n',b'\n')==g,p
        assert p.startswith(RUN.relative_to(ROOT).as_posix()+'/') or p.startswith(CONTRACT.as_posix()+'/'),p
        rows.append(dict(path=p,worktree_raw_sha256=sha(p),Git_blob_raw_sha256=hashlib.sha256(g).hexdigest(),
            worktree_raw_bytes=len(w),Git_blob_raw_bytes=len(g),worktree_CRLF_count=w.count(b'\r\n'),Git_CRLF_count=g.count(b'\r\n'),
            observed_difference_only_CRLF_to_LF=True,raw_hashes_are_distinct=True))
write(RUN/'committed-raw-line-ending-diagnosis-v2.json',dict(
    status='actual diagnostic, repair pending',head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),
    failed_audit='audit-committed-raw-v1.py actualexit1 at accepted-frontier-refresh-v1.log; no successful raw audit claimed',
    source='System Git config core.autocrlf=true; affected task evidence has no text/eol attribute.',
    actual_differing_files=rows,count=len(rows),
    repair='Stage ONLY listed owned task evidence with git -c core.autocrlf=false add --renormalize. Preserve actual working bytes and all independent reviewed raw hashes; no global config/attribute changes, source/reader changes, or broad hash normalization.',
    source_and_reader_raw_identity_already_verified=True,Asymptotic_two_prefix_representations_preserved=True,
    chapter_complete=False,goal_complete=False))
print('Actual differing owned evidence files:',len(rows),'; all are inherited checkout CRLF versus Git LF. No source or reader mismatch.')
