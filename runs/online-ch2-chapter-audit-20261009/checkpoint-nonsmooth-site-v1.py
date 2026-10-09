from common_nonsmooth_publication_v2 import *
import base64

fixed()
plan=load(RUN/'nonsmooth-candidate-stage-plan-v1.json');stage=plan['stage']
assert plan['actual_full_diff_exit']==2
exceptions=[RUN/'nonsmooth-blind-reconstruction-v1.md',RUN/'nonsmooth-canary-blind-reconstruction-v1.md',RUN/'nonsmooth-canary-blind-reconstruction-v2.md']
actual=set()
for line in plan['full_diff_stdout'].splitlines():
    if ': trailing whitespace.' in line or ': new blank line at EOF.' in line:actual.add(line.split(':',1)[0])
assert actual=={p.relative_to(ROOT).as_posix() for p in exceptions}
prod=load(RUN/'nonsmooth-production-BODY-review-input-v1.json')['rows']
can=load(RUN/'nonsmooth-canary-publication-review-input-v1.json')['rows']
for p,rs in [(exceptions[0],prod),(exceptions[2],can)]:
    row=next(r for r in rs if Path(r['path']).resolve()==p.resolve());assert sha(p)==row['sha256']
old=load(RUN/'nonsmooth-canary-blind-receipt-v1.json')
assert sha(exceptions[1]) in json.dumps(old)
capture('nonsmooth-candidate-scoped-diff-check-v1','git','diff','--cached','--check','--','.',
    *[':(exclude)'+p.relative_to(ROOT).as_posix() for p in exceptions])
write(RUN/'nonsmooth-candidate-diff-audit-v1.json',dict(actual_full_exit=2,
    retained_exact_RAW_decoder_exceptions=rows(exceptions),scoped_gate_passed=True,
    production_Test_reader_contract_exemptions=False,
    reason='Only three hash-bound historical decoder report files; preserve exact reviewed/received bytes. Distinct FINAL must inspect this exception; no mathematical or reader exemption.',
    chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('nonsmooth-candidate-final-stage-v1','git','add',*stage)
pending=[]
def clean_capture(label,command):
    command=list(map(str,command));tick=time.monotonic()
    p=subprocess.run(command,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    receipt=dict(command=command,cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-tick,
        stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii'))
    write(ROOT/'tmp'/(TASK+'-'+label+'.json'),receipt);pending.append((label,receipt))
    print(label,'actual exit',p.returncode,flush=True)
    assert p.returncode==0,label
    return p.stdout.decode('utf8',errors='replace')
# Final staging receipt is itself owned evidence and must enter the candidate.
subprocess.run(['git','add',*stage],cwd=str(ROOT),check=True)
clean_capture('nonsmooth-candidate-commit-v1',['git','commit','-m','Formalize absolute-value and labelled-hinge nonsmooth examples'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
for label,base in [('nonsmooth-contributor-stack-v2',BASE),('nonsmooth-contributor-main-v2','origin/main')]:
    out=clean_capture(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base])
    assert 'Contributor contract: N/A' not in out and PUBLIC.relative_to(ROOT).as_posix() in out
fixed();assert not SITE.exists()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
clean_capture('nonsmooth-site-build-v1',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE])
for label,receipt in pending:write(RUN/(label+'.json'),receipt)
write(RUN/'nonsmooth-clean-candidate-binding-v1.json',dict(actual_head=head,stacked_base=BASE,
    actual_clean_at_site_start=True,applicable_full_harness_receipt_sha256=sha(RUN/'nonsmooth-full-harness-inspected-v1.json'),
    nonempty_two_base_contributor_gates=True,local_site_output=SITE.as_posix(),deployed=False,FINAL_pending=True,
    chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('nonsmooth-site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
capture('nonsmooth-registry-command-v1',sys.executable,'-B','-X','utf8',RUN/'verify-nonsmooth-registry-v1.py')
fixed()
print('Actual committed candidate/two nonempty contributor gates/local clean Lean-verified site/check/registry passed. Pixels and distinct FINAL pending.')
