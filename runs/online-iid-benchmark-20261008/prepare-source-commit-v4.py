from common_integrated_v2 import *
fixed_integrated()
for label in ['combined-root-v2','combined-Tests-v2','full-harness-v2']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0
assert load(RUN/'pre-source-full-diff-v3-exit.json')['actual_exit_code']==2
diagnostics=(RUN/'pre-source-full-diff-v3.log').read_text(encoding='utf8')
paths=set(re.findall(r'(?m)^(runs/[^:]+):\d+:',diagnostics))
expected={str(RUN.relative_to(ROOT)/n).replace('\\','/') for n in ['blind-reconstruction-v1.md','combined-root-v2.log','combined-Tests-v2.log','full-harness-v2.log','common_v1.py','common_reviewed_v2.py']}
assert paths==expected,paths
for name in ['common_v1.py','common_reviewed_v2.py']:
    matches=re.findall(r'(?m)^'+re.escape((RUN.relative_to(ROOT)/name).as_posix())+r':\d+: ([^\n]+)',diagnostics)
    assert matches==['new blank line at EOF.'],(name,matches)
exceptions=[]
for name,reason in [
    ('blind-reconstruction-v1.md','Exact independent historical v1 decoder output: blank EOF, immutable CONTRACT/BODY hashes.'),
    ('combined-root-v2.log','Exact actual Lean verifier stdout contains quoted whitespace; preserve evidence.'),
    ('combined-Tests-v2.log','Exact actual Lean verifier stdout contains quoted whitespace; preserve evidence.'),
    ('full-harness-v2.log','Exact actual harness/Lean stdout contains quoted whitespace; preserve evidence.'),
    ('common_v1.py','Exact reviewed protocol helper; ONLY frozen EOF blank-line finding, no executable content defect or edit. Literal CONTRACT/BODY raw binding retained.'),
    ('common_reviewed_v2.py','Exact reviewed protocol header/hash helper; ONLY frozen EOF blank-line finding, no executable content defect or edit. Literal BODY raw binding retained.'),
    ('pre-source-full-diff-v3.log','Exact failed full-whitespace-check stdout quotes original whitespace; preserve failure.')]:
    p=RUN/name
    exceptions.append(dict(path=p.relative_to(ROOT).as_posix(),sha256=sha(p),reason=reason))
write(RUN/'diff-raw-bound-exceptions-v4.json',dict(exceptions=exceptions,
    scope='Seven individually bound files only; two frozen protocol helper exceptions at EOF explicitly disclosed for FINAL review; no production/test/reader/contract or other helper exemption.',
    unexcluded_diff_check_exit=2,source_package_accepted=False,chapter_complete=False,goal_complete=False))
write(RUN/'diff-check-repair-v4.json',dict(actual_initial_stage_race_exit=1,actual_full_diff_exit=2,
    actual_failed_log_sha256=sha(RUN/'pre-source-full-diff-v3.log'),immutable_CONTRACT_BODY_rows_preserved=True,
    exact_exceptions=exceptions,does_not_claim_unexcluded_diff_pass=True,no_source_proof_reader_change=True,
    FINAL_must_review_two_frozen_helper_EOF_exceptions=True,package_accepted=False,chapter_complete=False,goal_complete=False))
gate('scope-before-source-commit-v4',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v2.py','before-source-commit-v4')
status=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True)
paths=sorted(set(line[3:] for line in status.splitlines()))
assert all(p in load(RUN/'owned-paths-before-source-commit-v4.json')['paths'] or p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in paths)
globals=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']
owned=[p for p in paths if p not in globals]
for offset in range(0,len(owned),48):
    child=subprocess.run(['git','-c','core.autocrlf=false','add','--']+owned[offset:offset+48],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert child.returncode==0,child.stdout.decode('utf8',errors='replace')
changed=[p for p in paths if p in globals]
if changed:
    child=subprocess.run(['git','add','--']+changed,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert child.returncode==0
for p in owned: assert subprocess.check_output(['git','show',':'+p])==Path(p).read_bytes(),p
for p in changed: assert subprocess.check_output(['git','show',':'+p]).startswith(subprocess.check_output(['git','show',BASE+':'+p])),p
gate('scoped-diff-pre-source-v4',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v4.py','pre-source-v4')
# Stage every tail AFTER both scope and diff helpers have closed their own output receipts.
tails=[line[3:] for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).splitlines()
    if line.startswith('??') or line[:2]=='AM']
assert all(p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in tails),tails
for offset in range(0,len(tails),48):
    child=subprocess.run(['git','-c','core.autocrlf=false','add','--']+tails[offset:offset+48],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert child.returncode==0
for p in tails: assert subprocess.check_output(['git','show',':'+p])==Path(p).read_bytes(),p
child=subprocess.run(['git','commit','-m','Produce the expected fixed minimum and actual causal IID square-loss core'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
sys.stdout.write('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[:4])+'\n')
assert child.returncode==0
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
print('Actual clean scoped source commit',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
