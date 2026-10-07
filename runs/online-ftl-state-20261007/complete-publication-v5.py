from common_v1 import *
fixed(proving=True,integrated=True);assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
gate('full-harness-final-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
raw=(RUN/'full-harness-final-v1.log').read_text(encoding='utf-8');counts=re.search(r'Ran (\d+) tests',raw);skips=re.search(r'OK \(skipped=(\d+)\)',raw);assert counts and skips and int(counts[1])==load(RUN/'integrated-gates-overlay-v1.json')['full_tests'] and int(skips[1])==load(RUN/'integrated-gates-overlay-v1.json')['existing_skips'] and 'check passed' in raw
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'prepare-publication-v5.py')],check=True)
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Accept general-initial FTL and true state producer after distinct FINAL'],check=True)
gate('contributor-final-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','final-v1')
gate('source-scope-final-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','final-v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Bind final FTL-state contributor and source-preservation gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
cmd=[sys.executable,'-B','-X','utf8',str(RUN/'audit-committed-raw-v1.py')];temporary=Path('tmp/online-ftl-state-raw-audit-v1.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'committed-raw-audit-v1.log',temporary.read_bytes());write(RUN/'committed-raw-audit-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'committed-raw-audit-v1.log'),stdout_ignored_until_completion=True));assert child.returncode==0
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Preserve raw FTL-state evidence before authorized draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
gate('push-creation-v1','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin',BRANCH)
gate('create-pr-v1',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
fixed(proving=True,integrated=True)
