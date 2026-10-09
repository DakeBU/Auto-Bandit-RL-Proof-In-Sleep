from common_reader_v4 import *
fixed()
assert not load(RUN/'candidate-shadow-gate-v1.json')['actual_shadow']['mismatches']
READERS=[Path(r['path']) for r in load(RUN/'reader-integration-bindings-v1.json')['rows']]
stage=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'BanditRLProof.lean','Tests.lean',CONTRACT.relative_to(ROOT).as_posix(),RUN.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix(),*[p.relative_to(ROOT).as_posix() for p in READERS],*[d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']]]
allowed_files={PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'BanditRLProof.lean','Tests.lean',CONTRIBUTION.relative_to(ROOT).as_posix(),*[p.relative_to(ROOT).as_posix() for p in READERS],*[d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']]}
for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines():
    p=line[3:];assert p in allowed_files or p.startswith(CONTRACT.relative_to(ROOT).as_posix()+'/') or p.startswith(RUN.relative_to(ROOT).as_posix()+'/'),p
gate('candidate-stage-checkpoint-v1','git','add',*stage)
code=gate('candidate-full-diff-check-v1','git','diff','--cached','--check',required=False);excluded=[]
if code:
    for line in (RUN/'candidate-full-diff-check-v1.log').read_text('utf8').splitlines():
        if ': trailing whitespace.' not in line and ': new blank line at EOF.' not in line:continue
        p=line.split(':',1)[0];assert p.startswith(RUN.relative_to(ROOT).as_posix()+'/') and Path(p).suffix in ['.log','.raw'],p
        if p not in excluded:excluded.append(p)
    assert excluded
    gate('candidate-scoped-diff-check-v1','git','diff','--cached','--check','--','.',*[':(exclude)'+p for p in excluded])
write(RUN/'candidate-diff-audit-v1.json',dict(actual_full_exit=code,retained_exact_RAW_exceptions=rows([ROOT/p for p in excluded]),production_Test_reader_contract_exemptions=False,scoped_gate_passed=True,full_unexcluded_gate_zero=(code==0),reason='Preserve exact RAW baseline/compiler evidence; SHA-bound narrowly scoped exceptions await independent FINAL.'))
pending=[]
for label,command in [('candidate-stage-final-v1',['git','add',*stage]),('candidate-commit-v1',['git','commit','-m','Prove general-initial FTL and audit Chapter1 source contracts'])]:
    log=ROOT/'tmp'/(TASK+'-'+label+'.log');assert not log.exists();tick=time.monotonic()
    with log.open('wb') as stream:child=subprocess.run(command,cwd=str(ROOT),stdout=stream,stderr=subprocess.STDOUT)
    receipt=dict(command=command,cwd=ROOT.as_posix(),actual_exit=child.returncode,seconds=time.monotonic()-tick,log_sha256=sha(log))
    pending.append((label,log,receipt));print(label,'actual exit',child.returncode,flush=True);assert child.returncode==0
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
write(ROOT/'tmp/online-c1-chapter-audit-candidate-head-v1.json',dict(actual_head=head,base=BASE,scope='Current Chapter1 source17 candidate, four actual general-init proofs/27canaries; FINAL pending',chapter_complete=False,goal_complete=False))
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
fixed();assert not SITE.exists()
temp=ROOT/'tmp/online-c1-chapter-audit-site-build-v1.log';assert not temp.exists()
command=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE.as_posix()]
tick=time.monotonic()
with temp.open('wb') as stream:child=subprocess.run(command,cwd=str(ROOT),stdout=stream,stderr=subprocess.STDOUT)
for label,log,receipt in pending:write(RUN/(label+'.log'),log.read_bytes());write(RUN/(label+'-exit.json'),receipt)
write(RUN/'site-build-v1.log',temp.read_bytes())
write(RUN/'site-build-v1-exit.json',dict(command=command,cwd=ROOT.as_posix(),actual_exit=child.returncode,seconds=time.monotonic()-tick,source_commit=head,actual_clean_at_site_start=True,log_sha256=sha(RUN/'site-build-v1.log'),applicable_combined_gate_sha256=sha(RUN/'combined-gates-inspected-v1.json'),deployed=False))
print('site-build-v1 actual exit',child.returncode,flush=True);assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
gate('registry-check-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
for label,base in [('candidate-contributor-stack-v1',BASE),('candidate-contributor-main-v1','origin/main')]:
    gate(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    log=(RUN/(label+'.log')).read_text('utf8');assert 'Contributor contract: N/A' not in log and PUBLIC.relative_to(ROOT).as_posix() in log
write(RUN/'candidate-contributor-gates-v1.json',dict(actual_head=head,both_nonempty_bases_cover_new_production=True,receipts=['candidate-contributor-stack-v1-exit.json','candidate-contributor-main-v1-exit.json'],FINAL_required=True,chapter_complete=False,goal_complete=False))
fixed()
print('Clean committed candidate/current Lean-verified LOCALsite/old registry/nonempty two-base contributor gates passed; FINAL pending.',flush=True)
