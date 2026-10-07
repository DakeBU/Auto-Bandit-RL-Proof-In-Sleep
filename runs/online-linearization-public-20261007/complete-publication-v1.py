"""Execute authorized concrete draft only after distinct FINAL/native acceptance."""
from common_v2 import *
fixed(True);assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed' and load(RUN/'accepted-decision-v1.json')['source_package_accepted']
gate('full-harness-current-reader-v2-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
raw=(RUN/'full-harness-current-reader-v2-01.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'prepare-publication-v1.py')],check=True)
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Accept causal linearization source reuse after distinct FINAL review'],check=True)
gate('contributor-final-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','final-v1')
old=(RUN/'audit-scope-v1.py').read_text(encoding='utf-8');write(RUN/'audit-scope-final-v1.py',old.replace('source-scope-audit-v1.json','source-scope-audit-final-v1.json'))
gate('source-scope-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-scope-final-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind final linearization contributor and preservation gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
cmd=[sys.executable,'-B','-X','utf8',str(RUN/'audit-committed-raw-v1.py')];temporary=Path('tmp/online-linearization-public-raw-audit-v1.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'committed-raw-audit-v1-01.log',temporary.read_bytes());write(RUN/'committed-raw-audit-v1-01-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'committed-raw-audit-v1-01.log'),stdout_ignored_until_completion=True));assert child.returncode==0
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve raw linearization evidence before authorized draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
gate('push-creation-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin',BRANCH)
gate('create-pr-v1-01',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
fixed(True);print('Actual zero-new-math draft created; app attachment/delivery/final DIRECT audit remain.')
