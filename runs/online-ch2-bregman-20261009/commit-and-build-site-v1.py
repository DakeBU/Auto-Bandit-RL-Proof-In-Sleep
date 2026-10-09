from publication_guard_v1 import *
fixed()
assert load(RUN/'full-harness-inspected-v1.json')['actual_check_passed']
assert load(RUN/'candidate-diff-audit-v1.json')['full_whitespace_gate_passed']
stage=load(RUN/'candidate-stage-plan-v1.json')['stage']
subprocess.run(['git','add',*stage],cwd=ROOT,check=True)
pending=[]
def clean_capture(label,command):
    command=list(map(str,command));start=time.monotonic()
    p=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    rec=dict(command=command,cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii'))
    write(ROOT/'tmp'/(TASK+'-'+label+'.json'),rec);pending.append((label,rec))
    print(label,'actual exit',p.returncode,flush=True)
    if p.returncode!=0:print(p.stdout.decode('utf8',errors='replace')[-14000:])
    assert p.returncode==0,label
    return p.stdout.decode('utf8',errors='replace')
clean_capture('candidate-commit-v1',['git','commit','-m','Prove canonical Bregman algebra and nonsmooth proximal comparison'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
for label,base in [('contributor-stack-v1',BASE),('contributor-main-v1','origin/main')]:
    out=clean_capture(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base])
    assert 'Contributor contract: N/A' not in out and PUBLIC.relative_to(ROOT).as_posix() in out
fixed()
assert not SITE.exists()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
clean_capture('site-build-v1',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE])
for label,receipt in pending:write(RUN/(label+'.json'),receipt)
write(RUN/'clean-candidate-site-binding-v1.json',dict(actual_head=head,stacked_base=BASE,actual_clean_at_site_start=True,applicable_full_harness_receipt_sha256=sha(RUN/'full-harness-inspected-v1.json'),two_nonempty_contributor_bases=True,local_site_output=SITE.as_posix(),no_fresh_build_at_later_evidence_head_claim=True,deployed=False,FINAL_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
capture('registry-command-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
fixed()
print('Actual clean candidate site/check/exact shared registry passed; DOM/pixels/FINAL/native/delivery pending.')
