from common_nonsmooth_publication_v2 import *

fixed()
full=load(RUN/'nonsmooth-full-harness-inspected-v1.json')
assert full['actual_exit']==0 and full['actual_check_passed'] and full['actual_ProofGraphExport_compile_present']
pre=load(RUN/'nonsmooth-contributor-stack-v1.json')
import base64
out=base64.b64decode(pre['stdout_base64']).decode('utf8')
assert pre['actual_exit']==0 and 'Contributor contract: N/A' in out
write(RUN/'nonsmooth-precommit-contributor-classification-v1.json',dict(
    actual_receipt_sha256=sha(RUN/'nonsmooth-contributor-stack-v1.json'),
    actual_command_exit=0,wrapper_assertion_exit=1,
    classification='precommit-git-range-N-A-not-a-contributor-pass',
    cause='The checker uses git diff BASE...HEAD. All candidate edits were still uncommitted; its actual changed-path set was empty.',
    repair='Commit only this bounded reviewed candidate, then run both stacked-base and origin/main contributor gates and require the new production path plus non-N/A output.',
    mathematical_statement_or_proof_repair=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
m=load(CONTRIBUTION)
m['verification']['bandit_check']='Actual applicable combined root9106/Tests9272 cached-inclusive compiler jobs; full tools/bandit.py check exit0,472 tests passed/7 skipped, actual exporter compilation and check-passed markers inspected. Evidence: runs/online-ch2-chapter-audit-20261009/nonsmooth-full-harness-inspected-v1.json. Job counts are not new theorem counts.'
CONTRIBUTION.write_text(json.dumps(m,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
index=ROOT/'research-wiki/retrieval-index/ONLINE-CH2-NONSMOOTH-20261009.md'
with index.open('a',encoding='utf8') as f:
    f.write('\nCheckpoint update: actual current full harness passed,472 tests/7 skips, exporter compiled; own frontier-shadow mismatches[]/would_mutatefalse. Precommit contributor was N/A and is explicitly not a pass; postcommit nonempty two-base gates, shared registry/site/pixels, FINAL/native/delivery remain pending. No Chapter2 or whole-Goal completion.\n')
stage=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'BanditRLProof.lean','Tests.lean',
    CONTRACT.relative_to(ROOT).as_posix(),RUN.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix(),
    'research-wiki/retrieval-index/ONLINE-CH2-NONSMOOTH-20261009.md',
    'website/content/chapters.json','website/content/highlights.json','website/content/readings.json',
    *[d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']]]
allowed=set(stage)
for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines():
    p=line[3:]
    assert p in allowed or p.startswith(CONTRACT.relative_to(ROOT).as_posix()+'/') or p.startswith(RUN.relative_to(ROOT).as_posix()+'/'),p
capture('nonsmooth-candidate-stage-v1','git','add',*stage)
code,out=capture('nonsmooth-candidate-full-diff-check-v1','git','diff','--cached','--check',required=False)
write(RUN/'nonsmooth-candidate-stage-plan-v1.json',dict(stage=stage,actual_full_diff_exit=code,
    full_diff_stdout=out,commit_still_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Scoped staging and actual full whitespace audit captured; candidate commit remains pending.')
