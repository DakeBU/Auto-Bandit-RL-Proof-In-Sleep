"""Scoped accepted proof package: final exact-base gates/raw audit, push, actual draft creation."""
from common_v1 import *
headers();assert load(RUN/'accepted-decision-v1.json')['source_package_accepted'] and load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Accept frozen guessing-policy terminal and bind semantic and shared Book evidence'],check=True)
gate('contributor-final-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','final-v1')
scope=(RUN/'audit-scope-v5.py').read_text(encoding='utf-8').replace('source-scope-audit-v5.json','source-scope-audit-final-v1.json');write(RUN/'audit-scope-final-v1.py',scope)
gate('source-scope-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-scope-final-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind final exact-base guessing-policy contributor and preservation gates'],check=True)
# The audit itself checks every current nonignored run file and writes only after
# all bytes equal their committed blobs; a final DIRECT audit covers this receipt.
cmd=[sys.executable,'-B','-X','utf8',str(RUN/'audit-committed-raw-v1.py')]
temporary=Path('tmp/online-guessing-osd-policy-raw-audit-v1.log');start=time.time()
with temporary.open('wb') as stream: child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'committed-raw-audit-v1-01.log',temporary.read_bytes())
write(RUN/'committed-raw-audit-v1-01-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'committed-raw-audit-v1-01.log')))
assert child.returncode==0
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Retain final guessing-policy raw byte audit before draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
gate('push-creation-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin','codex/research-online-guessing-osd-policy')
gate('create-pr-v1-01',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
headers();print('Actual scoped draft created; app attachment/delivery metadata/final DIRECT audit pending.')
