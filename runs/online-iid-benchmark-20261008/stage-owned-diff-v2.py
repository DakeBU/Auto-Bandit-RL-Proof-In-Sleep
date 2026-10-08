from common_integrated_v2 import *
fixed_integrated()
gate('scope-before-staging-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v2.py','before-staging-v2')
globals=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']
status=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True)
paths=sorted(set(line[3:] for line in status.splitlines()))
prior=load(RUN/'owned-paths-before-staging-v2.json')['paths']
assert all(p in prior or p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in paths)
owned=[p for p in paths if p not in globals]
for offset in range(0,len(owned),48):
    child=subprocess.run(['git','-c','core.autocrlf=false','add','--']+owned[offset:offset+48],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert child.returncode==0,child.stdout.decode('utf8',errors='replace')
changed_globals=[p for p in paths if p in globals]
child=subprocess.run(['git','add','--']+changed_globals,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert child.returncode==0
for p in owned: assert subprocess.check_output(['git','show',':'+p])==Path(p).read_bytes(),p
for p in changed_globals: assert subprocess.check_output(['git','show',':'+p]).startswith(subprocess.check_output(['git','show',BASE+':'+p])),p
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE,'--','.']
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'pre-source-full-diff-v2.log',child.stdout)
write(RUN/'pre-source-full-diff-v2-exit.json',dict(command=command,actual_exit_code=child.returncode,log_sha256=sha(RUN/'pre-source-full-diff-v2.log'),
    staged_owned_count=len(owned),separate_historical_globals=len(changed_globals),math_source_headers_unchanged=True,
    raw_staged_bytes_verified=True,package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual complete diff-check exit',child.returncode,'; raw stdout retained; no acceptance inference.')
