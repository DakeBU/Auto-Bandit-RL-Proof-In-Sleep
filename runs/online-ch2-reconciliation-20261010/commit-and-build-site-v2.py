from candidate_execution_guard_v2 import *
candidate_plan_fixed()
fixed()
assert load(RUN/'full-harness-inspected-v2.json')['actual_check_passed']
assert load(RUN/'candidate-shadow-inspected-v1.json')['actual_report']['mismatches']==[]
assert load(RUN/'candidate-stage-inspected-v1.json')['actual_active_text_diff_exit']==0
stage=load(RUN/'candidate-stage-plan-v1.json')['stage']
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
pending=[]
def clean_capture(label,args):
    start=time.monotonic();args=list(map(str,args));p=subprocess.run(args,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    rec=dict(command=args,cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii'))
    write(ROOT/'tmp'/(TASK+'-'+label+'.json'),rec);pending.append((label,rec))
    print(label,'actual exit',p.returncode,flush=True)
    assert p.returncode==0,(label,p.stdout.decode('utf8',errors='replace')[-16000:])
    return p.stdout.decode('utf8',errors='replace')
clean_capture('candidate-final-stage-v2',['git','add',*stage])
changed=exact_cached_scope()
assert not subprocess.check_output(['git','diff','--name-only'],encoding='utf8').strip()
assert not subprocess.check_output(['git','ls-files','--others','--exclude-standard'],encoding='utf8').strip()
clean_capture('candidate-final-diff-v2',['git','diff','--cached',BASE,'--check'])
assert exact_cached_scope()==changed
clean_capture('candidate-commit-v2',['git','commit','-m','Formalize generic strict-past FTL selector and reconcile Chapter 2 sources'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
for label,base in [('contributor-stack-v1',BASE),('contributor-main-v1','origin/main')]:
    out=clean_capture(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base])
    assert 'Contributor contract: N/A' not in out and MODULE.relative_to(ROOT).as_posix() in out
fixed();assert not SITE.exists()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
clean_capture('site-build-v1',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE])
for label,rec in pending:write(RUN/(label+'.json'),rec)
write(RUN/'clean-candidate-site-binding-v1.json',dict(actual_head=head,stacked_base=BASE,actual_clean_at_site_start=True,
    applicable_full_harness_receipt_sha256=sha(RUN/'full-harness-inspected-v2.json'),production_sha256=sha(MODULE),Test_sha256=sha(TEST),
    two_nonempty_contributor_bases=True,local_site_output=SITE.as_posix(),fresh_site_at_later_evidence_head=False,deployed=False,FINAL_pending=True,chapter_complete=False,whole_Goal='ACTIVE'))
capture('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
capture('registry-command-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
fixed()
print('Clean candidate site/check/shared registry passed; browser/original-pixel/FINAL/native/delivery pending.')
