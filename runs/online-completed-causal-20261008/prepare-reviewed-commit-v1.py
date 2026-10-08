from common_accepted_v1 import *
from commit_owned_v1 import stage_owned,commit_owned
import re

accepted_fixed()
post=load(RUN/'post-native-receipt-v1.json')
assert post['verdict'] in ['accepted','accepted-with-explicit-delta']
assert post['inputs_unchanged'] and not post['required_blocking_repairs']
assert post['report_sha256']==sha(RUN/'post-native-review-v1.md')
assert all(sha(r['path'])==r['sha256'] for r in load(RUN/'post-native-review-inputs-v1.json')['rows'])
stage_owned()
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--cached','--check',BASE]
gate('accepted-full-diff-v1',*command,required=False)
code=load(RUN/'accepted-full-diff-v1-exit.json')['actual_exit'];assert code in [0,2]
diag=(RUN/'accepted-full-diff-v1.log').read_text(encoding='utf8')
bad=set(re.findall(r'^([^\r\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab)',diag,re.M))
bound={r['sha256'] for r in load(RUN/'FINAL-review-inputs-v1.json')['rows']}
exceptions=[]
for rel in sorted(bad):
    p=ROOT/rel;assert rel.startswith(RUN.relative_to(ROOT).as_posix()+'/'),rel
    assert sha(p) in bound,rel
    assert p.suffix in ['.log','.raw'],rel
    if p.suffix=='.log':assert list(RUN.glob(p.stem+'*exit.json')) or p.name=='candidate-full-diff-v1.log',rel
    exceptions.append(dict(path=rel,sha256=sha(p),reason='Exact review-bound raw stdout or immutable raw snapshot only'))
if code:
    assert bad
    exceptions.append(dict(path=(RUN/'accepted-full-diff-v1.log').relative_to(ROOT).as_posix(),
        sha256=sha(RUN/'accepted-full-diff-v1.log'),reason='Actual raw whitespace diagnostics, unchanged evidence bytes'))
write(RUN/'accepted-diff-raw-exceptions-v1.json',dict(full_unexcluded_actual_exit=code,
    full_unexcluded_passed=code==0,exceptions=exceptions,production_Test_reader_contract_executable_exceptions=0))
stage_owned()
for r in exceptions:assert sha(ROOT/r['path'])==r['sha256']
gate('accepted-scoped-diff-v1',*command,'--','.',*[':(exclude)'+r['path'] for r in exceptions])
gate('contributor-accepted-stacked-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('contributor-accepted-origin-main-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
accepted_fixed()
commit_owned('Record Completed causal acceptance and current shared reader evidence')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
write(RUN/'accepted-source-commit-v1.json',dict(commit=head,branch=BRANCH,stacked_base=BASE,basePR=198,
    actual_clean_at_commit=True,receipt_untracked_until_next_evidence_commit=True,
    actual_native_acceptance=True,actual_post_native_review=True,draft_delivery_pending=True,
    chapter_complete=False,goal_complete=False,merged=False,live=False))
print('Actual reviewed scoped acceptance commit:',head,'draft delivery pending.',flush=True)
