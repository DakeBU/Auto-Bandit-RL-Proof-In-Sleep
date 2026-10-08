from commit_owned_v1 import *
import re
fixed_integrated()
g=load(RUN/'combined-gates-v1.json')
assert g['actual_exit_codes']==[0,0,0]
assert sha(PUBLIC)==g['public_sha256'] and sha(CANARY)==g['canary_sha256']
assert all(sha(ROOT/p)==h for p,h in g['source_pins'].items())
stage_owned()
bindings=[]
for p in [PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean']:
    rel=p.relative_to(ROOT).as_posix()
    blob=subprocess.check_output(['git','show',':'+rel])
    assert blob==p.read_bytes().replace(b'\r\n',b'\n')
    bindings.append(dict(path=rel,raw_sha256=sha(p),Git_index_LF_sha256=hashlib.sha256(blob).hexdigest(),
        conversion='Git CRLF-to-LF staging; frozen reviewed raw bytes remain unchanged.'))
write(RUN/'candidate-RAW-Git-bindings-v1.json',dict(rows=bindings,public_and_canary_frozen_raw_unchanged=True,
    chapter_complete=False,goal_complete=False))
stage_owned()
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--cached','--check',BASE]
gate('candidate-full-diff-v1',*command,required=False)
diag=(RUN/'candidate-full-diff-v1.log').read_text(encoding='utf8')
actual=load(RUN/'candidate-full-diff-v1-exit.json')['actual_exit']
assert actual in [0,2]
bad=set(re.findall(r'^([^\r\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab)',diag,re.M))
exceptions=[]
bound={x['sha256'] for x in load(RUN/'body-review-inputs-v1.json')['rows']}
bound.update(x['sha256'] for x in load(RUN/'source-contract-review-inputs-v1.json')['rows'])
bound.update(x['sha256'] for x in load(RUN/'draft-baseline-v1.json')['rows'])
if actual:
    assert bad,'Unknown raw diff failure needs diagnosis'
    for rel in sorted(bad):
        assert rel.startswith(RUN.relative_to(ROOT).as_posix()+'/'),rel
        p=ROOT/rel
        if p.suffix=='.log':
            assert list(RUN.glob(p.stem+'*exit.json')) or rel.startswith(RUN.relative_to(ROOT).as_posix()+'/stacked-base-current-'),rel
        else:
            assert p.suffix=='.raw' and sha(p) in bound,rel
        exceptions.append(dict(path=rel,sha256=sha(p),reason='Exact raw command output or immutable review-bound snapshot; no executable/production/test/reader/contract exemption.'))
    exceptions.append(dict(path=(RUN/'candidate-full-diff-v1.log').relative_to(ROOT).as_posix(),
        sha256=sha(RUN/'candidate-full-diff-v1.log'),reason='Actual raw whitespace diagnostics preserve the offending raw evidence bytes.'))
write(RUN/'candidate-diff-raw-exceptions-v1.json',dict(full_unexcluded_actual_exit=actual,
    full_unexcluded_passed=actual==0,exceptions=exceptions,production_Test_reader_contract_executable_exceptions=0))
stage_owned()
for e in exceptions:assert sha(ROOT/e['path'])==e['sha256']
scoped=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--cached','--check',BASE,'--','.',
    *[':(exclude)'+e['path'] for e in exceptions]]
gate('candidate-scoped-diff-v1',*scoped)
write(RUN/'candidate-scoped-diff-v1.json',dict(actual_exit=0,command=scoped,
    exact_raw_exceptions=exceptions,full_unexcluded_actual_exit=actual,full_unexcluded_passed=actual==0,
    public_test_readers_contracts_and_executable_helpers_checked=True,chapter_complete=False,goal_complete=False))
commit_owned('Online Learning C1: construct completed-information real versions')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
write(RUN/'candidate-source-commit-v1.json',dict(commit=head,branch=BRANCH,stacked_base=BASE,basePR=198,
    actual_clean_at_commit=True,receipt_untracked_until_next_commit=True,
    FINAL_site_native_delivery_pending=True,chapter_complete=False,goal_complete=False))
gate('contributor-candidate-stacked-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('contributor-candidate-origin-main-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
fixed_integrated()
print('Scoped candidate source committed and both contributor bases checked; site/FINAL/native pending.',flush=True)
