from commit_owned_v1 import *
import re
assert load(RUN/'combined-gates-v1.json')['actual_exit_codes']==[0,0,0]
fixed_integrated()
stage_owned()
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol',
    'diff','--cached','--check',BASE]
log=RUN/'source-full-diff-v1.log'
assert not log.exists()
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(log,child.stdout)
write(RUN/'source-full-diff-v1-exit.json',dict(command=command,actual_exit=child.returncode,
    log_sha256=sha(log),full_unexcluded_passed=child.returncode==0))
assert child.returncode in [0,2],child.returncode
bad=set(re.findall(r'^([^\r\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab)',
    child.stdout.decode('utf8',errors='replace'),re.M))
exceptions=[]
if child.returncode:
    assert bad,'Unrecognized diff diagnostics require explicit repair'
    # Only exact own raw command stdout logs may be exempt; every semantic/executable file is checked.
    for p in sorted(bad):
        assert p.startswith(RUN.relative_to(ROOT).as_posix()+'/') and p.endswith('.log'),p
        receipt_candidates=list(RUN.glob(Path(p).stem+'*exit.json'))
        assert receipt_candidates,p
        exceptions.append(dict(path=p,sha256=sha(p),reason='Exact raw executed-command stdout; not normalized',
            actual_diff_diagnostic=True))
    exceptions.append(dict(path=log.relative_to(ROOT).as_posix(),sha256=sha(log),
        reason='Exact raw executed Git diff diagnostics repeats original stdout whitespace',actual_diff_diagnostic=False))
write(RUN/'diff-raw-bound-exceptions-v1.json',dict(exceptions=exceptions,
    full_unexcluded_actual_exit=child.returncode,full_unexcluded_passed=child.returncode==0,
    production_Test_reader_contract_or_executable_exceptions=0))
stage_owned()
for e in exceptions: assert sha(e['path'])==e['sha256']
scoped=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol',
    'diff','--cached','--check',BASE,'--','.',*[':(exclude)'+e['path'] for e in exceptions]]
gate('scoped-diff-candidate-v1',*scoped)
write(RUN/'scoped-diff-candidate-v1.json',dict(command=scoped,actual_exit=0,
    exact_raw_byte_exceptions=exceptions,full_unexcluded_actual_exit=child.returncode,
    full_unexcluded_passed=child.returncode==0,
    production_Test_reader_contract_and_helpers_checked=True,executable_exceptions=0,
    package_accepted=False,chapter_complete=False,goal_complete=False))
commit_owned('Online Learning C1: IID success criterion and actual mean learner convergence')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
write(RUN/'candidate-source-commit-v1.json',dict(commit=head,stacked_base=BASE,branch=BRANCH,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),source_clean_at_commit=True,
    note='This new evidence receipt itself is untracked until next evidence commit; source clean refers pre-receipt commit moment',
    FINAL_site_native_delivery_pending=True,chapter_complete=False,goal_complete=False))
gate('contributor-candidate-committed-v1',sys.executable,'-B','-X','utf8',
    'tools/check_contributor_contract.py','--base',BASE)
fixed_integrated()
print('Scopedcandidate committed andnonvacuous actual committed-basecontributor passed; FINAL/site/acceptance/delivery remainpending.')
