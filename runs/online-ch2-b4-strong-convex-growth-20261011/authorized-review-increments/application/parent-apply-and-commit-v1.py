import hashlib, json, pathlib, subprocess, sys
from datetime import datetime, timezone

ROOT = pathlib.Path(__file__).resolve().parents[3]
APP = pathlib.Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT)
def textgit(*args): return git(*args).decode().strip()
def binding(p): return dict(path=p.relative_to(ROOT).as_posix(), sha256=sha(p), bytes=p.stat().st_size)
def write_new(p, obj):
    with p.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')

version, proposal_sha, emitter_sha, review_rel, review_sha = sys.argv[1:]
proposal = APP / ('canonical-freeze-application-proposal-'+version+'.json')
emitter = APP / ('emit-canonical-freeze-'+version+'.ps1')
review_path = ROOT / review_rel
assert sha(proposal)==proposal_sha and sha(emitter)==emitter_sha and sha(review_path)==review_sha
p=json.loads(proposal.read_bytes()); review=json.loads(review_path.read_bytes())
assert review['verdict']=='PASS_APPLICATION_DESIGN_REVIEW'
assert review['proposal_sha256']==proposal_sha and review['emitter_sha256']==emitter_sha
assert review['readiness_sha256']==p['independent_readiness']['sha256']
assert not review.get('blockers', review.get('blocking_repairs', []))
head=textgit('rev-parse','HEAD')
assert head=='4034f9d3c63acbb3a1b62a2683ed35c204923246' and not git('status','--porcelain=v1','-z')
assert not git('diff','--cached','--name-only')
auth={key:value for key,value in p['authorization_protocol'].items() if key in ['action','preproof_readiness']}
auth.update(proposal_sha256=proposal_sha,emitter_sha256=emitter_sha,source_head=head,
            actor='/root',scope='Authorized exact canonical evidence freeze and commit only; separate BODY authorization required.',
            BODY_authorized=False,maintenance_accepted=False,reader_pending=True)
auth['freeze_application_review']=dict(path=review_rel,sha256=review_sha,verdict_json_pointer='/verdict',
    success_verdict='PASS_APPLICATION_DESIGN_REVIEW',proposal_sha256_json_pointer='/proposal_sha256',
    emitter_sha256_json_pointer='/emitter_sha256',readiness_sha256_json_pointer='/readiness_sha256')
already={pathlib.Path(r['source']).resolve() if pathlib.Path(r['source']).is_absolute() else (ROOT/r['source']).resolve() for r in p['archival_rows']}
already.update((ROOT/r['path']).resolve() for r in p['required_v3_increments'])
already.update([proposal.resolve(),emitter.resolve()])
auth['additional_archive_bindings']=[]
for source in sorted(APP.iterdir()):
    if source.is_file() and source.resolve() not in already:
        b=binding(source); b['destination']=p['canonical_run']+'/authorized-review-increments/application/'+source.name
        auth['additional_archive_bindings'].append(b)
auth_path=APP/('parent-freeze-authorization-'+version+'.json')
write_new(auth_path,auth)
pwsh='C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'
argv=[pwsh,'-NoProfile','-File',str(emitter),'-AuthorizationFile',str(auth_path)]
started=datetime.now(timezone.utc).isoformat()
run=subprocess.run(argv,cwd=ROOT,capture_output=True)
for suffix,data in [('stdout.raw',run.stdout),('stderr.raw',run.stderr)]:
    with (APP/('parent-application-'+version+'.'+suffix)).open('xb') as f: f.write(data)
execution=dict(argv=argv,actual_exit=run.returncode,start_utc=started,end_utc=datetime.now(timezone.utc).isoformat(),
    source_head=head,proposal=binding(proposal),emitter=binding(emitter),review=binding(review_path),authorization=binding(auth_path))
write_new(APP/('parent-application-execution-'+version+'.json'),execution)
assert run.returncode==0, run.stderr.decode(errors='replace')
receipt_path=ROOT/p['canonical_doc']/('freeze-application-receipt-'+version+'.json')
receipt=json.loads(receipt_path.read_bytes())
assert receipt['source_head']==head and receipt['BODY'] is False and receipt['maintenance_accepted'] is False
owned=[]
for row in receipt['archival_rows']:
    dest=ROOT/row['destination']; assert sha(dest)==row['sha256'] and dest.stat().st_size==row['bytes']
    owned.append(row['destination'])
owned.append(receipt_path.relative_to(ROOT).as_posix())
assert len({x.casefold() for x in owned})==len(owned)
for start in range(0,len(owned),35): git('-c','core.longpaths=true','add','-f','--',*owned[start:start+35])
staged=git('diff','--cached','--name-only','-z').decode().split('\0')[:-1]
assert set(staged)==set(owned)
assert all(x.startswith((p['canonical_doc']+'/',p['canonical_run']+'/')) for x in staged)
git('diff','--cached','--check')
index={}
for line in git('ls-files','--stage','-z').decode().split('\0'):
    if not line: continue
    meta,name=line.split('\t',1); mode,oid,stage=meta.split()
    if name in owned: assert stage=='0'; index[name]=oid
assert set(index)==set(owned)
ordered=list(index)
batch=subprocess.run(['git','cat-file','--batch'],cwd=ROOT,input=('\n'.join(index[x] for x in ordered)+'\n').encode(),capture_output=True,check=True).stdout
offset=0
for name in ordered:
    end=batch.index(b'\n',offset); oid,kind,size=batch[offset:end].split(); size=int(size)
    blob=batch[end+1:end+1+size]; assert kind==b'blob' and blob==(ROOT/name).read_bytes(), name
    offset=end+1+size+1
assert offset==len(batch)
assert textgit('rev-parse','HEAD')==head
commit_output=git('commit','-m','Freeze reviewed conditional strong-convex minimum-growth target')
new_head=textgit('rev-parse','HEAD')
assert textgit('rev-parse','HEAD^')==head and not git('status','--porcelain=v1','-z')
commit_receipt=dict(status='CANONICAL_FREEZE_COMMITTED_CLEAN_NO_BODY_AUTHORIZATION',head=new_head,parent=head,
    branch=textgit('branch','--show-current'),gate_source_head=head,changed_paths=staged,all_archive_RAW_equals_index_blob=True,
    freeze_application_receipt=binding(receipt_path),proposal_sha256=proposal_sha,emitter_sha256=emitter_sha,
    independent_application_review=binding(review_path),maintenance_accepted=False,reader_pending=True,BODY_authorized=False,
    root_Tests_harness_rerun_on_new_commit=False,scope='Only new DOC/RUN evidence. Baseline gate HEAD remains4034. Separate applied independent review and BODY authorization pending.')
target=APP/('parent-freeze-commit-receipt-'+version+'.json'); write_new(target,commit_receipt)
print(json.dumps(dict(commit_receipt=binding(target),head=new_head,changed_paths=len(staged),clean=True,BODY_authorized=False)))
