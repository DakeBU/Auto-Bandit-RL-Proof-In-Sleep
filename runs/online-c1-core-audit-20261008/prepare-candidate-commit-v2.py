from commit_owned_v1 import *
import re
fixed_integrated()
g=load(RUN/'combined-gates-v1.json')
assert g['actual_exit_codes']==[0,0,0]
assert g['canary_sha256']==sha(CANARY) and g['public_files_sha256']=={p.as_posix():sha(p) for p in MODULES}
assert all(sha(p)==h for p,h in g['source_pins'].items())
stage_owned()
rows=[]
for p in MODULES:
    blob=subprocess.check_output(['git','show',':'+p.as_posix()])
    base=subprocess.check_output(['git','show',BASE+':'+p.as_posix()])
    assert blob.replace(PLAN[p.as_posix()]['comment_utf8'].encode('utf8'),b'',1)==base
    rows.append(dict(path=p.as_posix(),live_raw_sha256=sha(p),Git_index_LF_sha256=hashlib.sha256(blob).hexdigest(),
        Git_base_LF_sha256=hashlib.sha256(base).hexdigest(),local_raw_original_sha256=hashlib.sha256(baseline(p)).hexdigest(),
        raw_proof_body_bytes_unchanged=True,Git_LF_proof_body_bytes_unchanged=True,
        conversion='Git normalizes CRLF to LF for source staging; local review-bound bytes unchanged, no JSON serialization or silent SHA substitution.'))
write(RUN/'candidate-RAW-Git-source-bindings-v2.json',dict(rows=rows,exact_reviewed_raw_comment_results=True,
    original_Git_body_bytes_preserved=True,source_root_unmodified=True,chapter_complete=False,goal_complete=False))
stage_owned()
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--cached','--check',BASE]
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'source-full-diff-v2.log',child.stdout)
write(RUN/'source-full-diff-v2-exit.json',dict(command=command,actual_exit=child.returncode,
    log_sha256=sha(RUN/'source-full-diff-v2.log'),full_unexcluded_passed=child.returncode==0))
assert child.returncode in [0,2]
bad=set(re.findall(r'^([^\r\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab)',child.stdout.decode('utf8',errors='replace'),re.M))
exceptions=[]
bound_hashes={r['sha256'] for r in load(RUN/'body-review-inputs-v1.json')['rows']}|{r['sha256'] for r in load(RUN/'source-contract-review-inputs-v1.json')['rows']}
if child.returncode:
    assert bad,'Unknown diff diagnostic requires explicit repair'
    for p in sorted(bad):
        assert p.startswith(RUN.relative_to(ROOT).as_posix()+'/'),p
        if p.endswith('.log'): assert list(RUN.glob(Path(p).stem+'*exit.json')),p
        else:
            assert '/snapshots/' in p and sha(p) in bound_hashes,p
        exceptions.append(dict(path=p,sha256=sha(p),reason='Exact bound raw command stdout or immutable independently reviewed source baseline; preserve original bytes',actual_diff_diagnostic=True))
    p=RUN/'source-full-diff-v2.log'
    exceptions.append(dict(path=p.relative_to(ROOT).as_posix(),sha256=sha(p),reason='Exact raw executed diff diagnostic preserving original source/log whitespace',actual_diff_diagnostic=False))
write(RUN/'diff-raw-bound-exceptions-v2.json',dict(exceptions=exceptions,full_unexcluded_actual_exit=child.returncode,
    full_unexcluded_passed=child.returncode==0,production_Test_reader_contract_or_executable_exceptions=0))
stage_owned()
for e in exceptions: assert sha(e['path'])==e['sha256']
scoped=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol',
    'diff','--cached','--check',BASE,'--','.',*[':(exclude)'+e['path'] for e in exceptions]]
gate('scoped-diff-candidate-v2',*scoped)
write(RUN/'scoped-diff-candidate-v2.json',dict(command=scoped,actual_exit=0,exact_raw_byte_exceptions=exceptions,
    full_unexcluded_actual_exit=child.returncode,full_unexcluded_passed=child.returncode==0,
    production_Test_reader_contract_and_helpers_checked=True,executable_exceptions=0,
    source_audits_still_pending_FINAL_native=True,chapter_complete=False,goal_complete=False))
commit_owned('Online Learning C1: audit five legacy core modules and exact assumptions')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
write(RUN/'candidate-source-commit-v2.json',dict(commit=head,stacked_base=BASE,basePR=196,branch=BRANCH,
    raw_source_bindings_sha256=sha(RUN/'candidate-RAW-Git-source-bindings-v2.json'),canary_sha256=sha(CANARY),
    source_clean_at_commit=True,receipt_itself_untracked_until_next_commit=True,
    FINAL_site_native_delivery_pending=True,chapter_complete=False,goal_complete=False))
gate('contributor-candidate-stacked-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('contributor-candidate-origin-main-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
fixed_integrated()
print('Scoped source candidate committed; actual stacked AND origin/main contributor gates passed. FINAL/site/native/delivery still pending.')
