from common_body_v1 import *

integrated_fixed()
assert load(RUN/'combined-gates-v1.json')['actual_exit_codes']==[0,0,0]
assert load(RUN/'candidate-other-gates-v1.json')['both_contributor_bases_actual_exit0']
stage=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),
    'BanditRLProof.lean','Tests.lean','MANIFEST.md','runs/lifecycle_sessions.jsonl',
    CONTRACT.relative_to(ROOT).as_posix(),RUN.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix(),
    *[p.relative_to(ROOT).as_posix() for p in READERS],
    *[d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']]]
gate('candidate-stage-checkpoint-v2','git','add',*stage)
code=gate('candidate-full-diff-check-v2','git','diff','--cached','--check',required=False)
excluded=[]
if code:
    for line in (RUN/'candidate-full-diff-check-v2.log').read_text(encoding='utf8').splitlines():
        if ': trailing whitespace.' not in line and ': new blank line at EOF.' not in line:
            continue
        path=line.split(':',1)[0]
        assert path.startswith(RUN.relative_to(ROOT).as_posix()+'/') and Path(path).suffix in ['.log','.raw'],path
        if path not in excluded:
            excluded.append(path)
    assert excluded
    gate('candidate-scoped-diff-check-v2','git','diff','--cached','--check','--','.',
        *[':(exclude)'+p for p in excluded])
write(RUN/'candidate-diff-audit-v1.json',dict(actual_full_exit=code,
    retained_exact_RAW_log_snapshot_exceptions=rows([ROOT/p for p in excluded]),
    production_Test_reader_contract_exemptions=False,scoped_gate_passed=True,
    full_unexcluded_gate_zero=(code==0),
    reason='Exact raw compiler logs/baselines retained byte-for-byte; SHA-bound exceptions require FINAL review.'))
# Keep the final staging/commit receipt outside tracked scope until the clean site capture.
# The retained unexecuted v1 would create tracked log deltas after its commit.
pending=[]
for label,command in [('candidate-stage-final-v2',['git','add',*stage]),
    ('candidate-commit-v2',['git','commit','-m','Prove actual FTL fixed-comparator ordinary-limit criterion'])]:
    log=ROOT/'tmp'/(TASK+'-'+label+'.log')
    assert not log.exists()
    tick=time.monotonic()
    with log.open('wb') as stream:
        child=subprocess.run(command,cwd=str(ROOT),stdout=stream,stderr=subprocess.STDOUT)
    receipt=dict(command=command,cwd=ROOT.as_posix(),actual_exit=child.returncode,
        seconds=time.monotonic()-tick,log_sha256=sha(log))
    pending.append((label,log,receipt))
    print(label,'actual exit',child.returncode,flush=True)
    assert child.returncode==0
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
write(ROOT/'tmp/online-ftl-limit-candidate-head-v1.json',dict(actual_head=head,base=BASE,
    scope='Five derived actualFTL proofs/twelve binary canaries; separate FINAL acceptance pending',
    chapter_complete=False,goal_complete=False))
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
g=load(RUN/'combined-gates-v1.json')
assert sha(PUBLIC)==g['public_sha256'] and sha(CANARY)==g['canary_sha256']
assert not SITE.exists()
temp=ROOT/'tmp/online-ftl-limit-site-build-v1.log'
assert not temp.exists()
command=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE.as_posix()]
tick=time.monotonic()
with temp.open('wb') as stream:
    child=subprocess.run(command,cwd=str(ROOT),stdout=stream,stderr=subprocess.STDOUT)
for label,log,receipt in pending:
    write(RUN/(label+'.log'),log.read_bytes())
    write(RUN/(label+'-exit.json'),receipt)
write(RUN/'site-build-v1.log',temp.read_bytes())
write(RUN/'site-build-v1-exit.json',dict(command=command,cwd=ROOT.as_posix(),actual_exit=child.returncode,
    seconds=time.monotonic()-tick,source_commit=head,actual_clean_at_site_start=True,
    log_sha256=sha(RUN/'site-build-v1.log'),applicable_combined_gate_sha256=sha(RUN/'combined-gates-v1.json'),deployed=False))
assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
gate('registry-check-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
integrated_fixed()
print('Actual clean candidate commit/local verified site checked; FINAL/native/delivery pending.',flush=True)
