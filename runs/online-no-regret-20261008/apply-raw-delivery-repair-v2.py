from common_accepted_v1 import *
accepted_fixed()
receipt=load(RUN/'raw-delivery-receipt-v2.json')
assert receipt['actor']['task']=='/root/source_reviewer' and receipt['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not receipt['required_repairs'] and sha(receipt['report'])==receipt['report_sha256']
reviewed={x['path']:x['sha256'] for x in receipt['reviewed_files']}
for row in load(RUN/'raw-delivery-review-inputs-v2.json')['rows']:
    assert sha(row['path'])==row['sha256']==reviewed[row['path']]
d=load(RUN/'committed-raw-line-ending-diagnosis-v3.json')
paths=[x['path'] for x in d['rows'] if x['owned_new_task_evidence']]
assert len(paths)==193
for row in d['rows']:
    assert sha(row['path'])==row['worktree_raw_sha256']
for start in range(0,len(paths),32):
    command=['git','-c','core.autocrlf=false','add','--renormalize','--',*paths[start:start+32]]
    result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert result.returncode==0,result.stdout.decode('utf8',errors='replace')
entries=subprocess.check_output(['git','ls-files','--stage','-z','--',*paths]).split(b'\0')
objects={e.split(b'\t',1)[1].decode('utf8'):e.split(b'\t',1)[0].split()[1].decode('ascii') for e in entries if e}
raw=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(objects[p] for p in paths)+'\n').encode('ascii'))
cursor=0;actual=[]
for p in paths:
    end=raw.index(b'\n',cursor);header=raw[cursor:end].decode('ascii').split()
    assert header[0]==objects[p] and header[1]=='blob'
    size=int(header[2]);cursor=end+1;content=raw[cursor:cursor+size];cursor+=size+1
    assert hashlib.sha256(content).hexdigest()==sha(p),p
    actual.append(dict(path=p,staged_Git_blob=objects[p],actual_raw_sha256=sha(p)))
assert cursor==len(raw)
write(RUN/'raw-delivery-repair-applied-v2.json',dict(status='actual staged raw identity passed',
    reviewer_receipt_sha256=sha(RUN/'raw-delivery-receipt-v2.json'),actual193raw_staged_rows=actual,
    original_source_and_reader_bytes_unchanged=True,inherited_global_and_Asymptotic_Git_prefixes_not_restaged=True,
    all_independent_receipts_and_raw_logs_unchanged=True,no_global_Git_config_or_attributes_change=True,
    final_full_raw_audit_and_push_pending=True,new_mathematical_progress=0,chapter_complete=False,goal_complete=False))
new=[p for p in subprocess.check_output(['git','ls-files','--others','--exclude-standard'],encoding='utf8').splitlines() if p]
assert all(p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in new),new
for start in range(0,len(new),32):
    result=subprocess.run(['git','-c','core.autocrlf=false','add','--',*new[start:start+32]],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert result.returncode==0,result.stdout.decode('utf8',errors='replace')
staged=subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').splitlines()
assert all(p.startswith(RUN.relative_to(ROOT).as_posix()+'/') or p.startswith(CONTRACT.as_posix()+'/') for p in staged),staged
result=subprocess.run(['git','commit','-m','Preserve reviewed raw evidence bytes and inherited Git prefixes'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print('\n'.join(result.stdout.decode('utf8',errors='replace').splitlines()[-5:]),flush=True)
assert result.returncode==0
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
accepted_fixed()
print('193 actual raw staged objects exact; scoped evidence repair committed; full raw audit/push next.')
