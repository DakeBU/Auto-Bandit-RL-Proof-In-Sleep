from common_accepted_v1 import *
accepted_fixed()
paths=[x.decode('utf8') for x in subprocess.check_output(['git','ls-files','-z','--',*load(RUN/'owned-commit-paths-v2.json')]).split(b'\0') if x]
rows=[]
for p in paths:
    if p==APPEND_PATH:
        continue
    w=Path(p).read_bytes();g=subprocess.check_output(['git','show','HEAD:'+p])
    if w==g:
        continue
    assert w.replace(b'\r\n',b'\n')==g,p
    owned_evidence=p.startswith(RUN.relative_to(ROOT).as_posix()+'/') or p.startswith(CONTRACT.as_posix()+'/')
    inherited=None
    if not owned_evidence:
        assert p in ['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl'],p
        snapshot=RUN/'snapshots'/(p.replace('/','--')+'.raw')
        original=snapshot.read_bytes();baseblob=subprocess.check_output(['git','show',BASE+':'+p])
        assert w.startswith(original) and g.startswith(baseblob),p
        inherited=dict(original_worktree_raw_sha256=sha(snapshot),original_Git_prefix_raw_sha256=hashlib.sha256(baseblob).hexdigest(),
            original_worktree_prefix_bytes=len(original),original_Git_prefix_bytes=len(baseblob),both_exact_prefixes_preserved=True,
            worktree_append_raw_sha256=hashlib.sha256(w[len(original):]).hexdigest(),Git_append_raw_sha256=hashlib.sha256(g[len(baseblob):]).hexdigest(),
            ownership_guard='audit-scope-v3.py exact ownTASK/native reference-index append checks')
    rows.append(dict(path=p,worktree_raw_sha256=sha(p),Git_blob_raw_sha256=hashlib.sha256(g).hexdigest(),
        worktree_raw_bytes=len(w),Git_blob_raw_bytes=len(g),worktree_CRLF_count=w.count(b'\r\n'),Git_CRLF_count=g.count(b'\r\n'),
        observed_difference_only_CRLF_to_LF=True,raw_hashes_are_distinct=True,
        owned_new_task_evidence=owned_evidence,inherited_appendonly_prefix=inherited))
write(RUN/'committed-raw-line-ending-diagnosis-v3.json',dict(status='actual diagnostic, bounded repair pending',
    audited_head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),
    failed_attempts=['actual raw auditv1 exited1 at accepted-frontier-refresh-v1.log',
        'diagnosticv2 exited1 because it wrongly assumed every difference was newly owned evidence; inherited MANIFEST.md also differs'],
    source='System Git config core.autocrlf=true; no global or .gitattributes change.',rows=rows,
    owned_new_task_evidence_count=sum(x['owned_new_task_evidence'] for x in rows),
    inherited_appendonly_count=sum(not x['owned_new_task_evidence'] for x in rows),
    repair='Stage only enumerated NEW OWNED EVIDENCE with per-command core.autocrlf=false; preserve full working raw bytes. Keep inherited global Git prefixes unchanged and bind their distinct worktree/Git representations explicitly, like Asymptotic. No broad receipt normalization or global prefix rewrite.',
    source_reader_proof_bytes_unchanged=True,chapter_complete=False,goal_complete=False))
print('Differences:',len(rows),'owned new evidence',sum(x['owned_new_task_evidence'] for x in rows),'inherited global append-only',sum(not x['owned_new_task_evidence'] for x in rows))
