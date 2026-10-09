from common_nonsmooth_publication_v2 import *
import base64

fixed()
assert not SITE.exists()
stage=load(RUN/'nonsmooth-candidate-stage-plan-v1.json')['stage']
subprocess.run(['git','add',*stage],cwd=str(ROOT),check=True)
capture('nonsmooth-metadata-scoped-diff-check-v1','git','diff','--cached','--check')
subprocess.run(['git','add',*stage],cwd=str(ROOT),check=True)
pending=[]
def clean_capture(label,command):
    command=list(map(str,command));tick=time.monotonic()
    p=subprocess.run(command,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    receipt=dict(command=command,cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-tick,
        stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii'))
    write(ROOT/'tmp'/(TASK+'-'+label+'.json'),receipt);pending.append((label,receipt))
    print(label,'actual exit',p.returncode,flush=True);assert p.returncode==0,label
    return p.stdout.decode('utf8',errors='replace')
clean_capture('nonsmooth-manifest-repair-commit-v1',['git','commit','-m','Correct nonsmooth contribution test-file metadata'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
for label,base in [('nonsmooth-contributor-stack-v3',BASE),('nonsmooth-contributor-main-v3','origin/main')]:
    out=clean_capture(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base])
    assert 'Contributor contract: N/A' not in out and PUBLIC.relative_to(ROOT).as_posix() in out
fixed()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
clean_capture('nonsmooth-site-build-v1',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE])
for label,receipt in pending:write(RUN/(label+'.json'),receipt)
write(RUN/'nonsmooth-clean-candidate-binding-v1.json',dict(actual_head=head,proof_commit='d6ec4fd9fce5cc9d20936f1ebf372aef07a26a56',stacked_base=BASE,
    actual_clean_at_site_start=True,applicable_full_harness_receipt_sha256=sha(RUN/'nonsmooth-full-harness-inspected-v1.json'),
    nonempty_two_base_contributor_gates=True,local_site_output=SITE.as_posix(),deployed=False,FINAL_pending=True,
    chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('nonsmooth-site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
capture('nonsmooth-registry-command-v1',sys.executable,'-B','-X','utf8',RUN/'verify-nonsmooth-registry-v1.py')
fixed()
print('Actual clean committed candidate/two nonempty contributor gates/local Lean-verified site/check/registry passed. Pixels and distinct FINAL pending.')
