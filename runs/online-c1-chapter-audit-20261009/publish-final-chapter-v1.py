from common_final_v9 import *
import base64
fixed()
def encoded(path,args,required=True):
 p=subprocess.run(args,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 write(path,dict(command=args,cwd=ROOT.as_posix(),actual_exit=p.returncode,stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
 if required:assert p.returncode==0,(args,p.returncode)
 return p
body=(RUN/'PR-BODY-post-native-v2.md').read_text('utf8')
body=body.replace('This does not yet constitute Chapter 1 acceptance: the separate post-native/status-site and published-delivery review is pending.',
 'The separate post-native/current-status-reader and observed published-head delivery review also accepted with explicit deltas. The seventeen-object Chapter 1 scope is accepted locally with explicit source correction. Final metadata/evidence delivery is separately checked against the actual remote head; its short distinct review receipt is retained locally at tmp/online-c1-chapter-audit-final-delivery-review-v1.json to avoid recursively committing that receipt.')
body=body.replace('Thirteen exceptions were accepted at source FINAL; the additional raw successful-push log awaits post-native adjudication.',
 'All fourteen exact exceptions were accepted by the distinct source/post-native reviewer; there is no production, Test, reader, contract or helper exemption.')
body=body.replace('No chapter acceptance, whole-book completion, merge, deployment or main/live update is claimed by this description.',
 'Chapter 1 acceptance is confined to the seventeen reviewed main-text objects and explicit source correction. No whole-book completion, merge, deployment or main/live update is claimed.')
body=body.replace('`post-FINAL-shadow-gate-v1.json`.','`post-FINAL-shadow-gate-v1.json`; post-native: `post-native-review-v1.md`, `post-native-receipt-v1.json`; final status: `chapter-one-accepted-v6.json` in the contract directory and `final-chapter-field-suffix-audit-v1.json` in the run directory.')
assert 'review is pending' not in body and 'awaits post-native' not in body
write(RUN/'PR-BODY-final-v3.md',body)
for label,base in [('final-chapter-contributor-stack-v1',BASE),('final-chapter-contributor-main-v1','origin/main')]:
 gate(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
 text=(RUN/(label+'.log')).read_text('utf8');assert 'Contributor contract: N/A' not in text and PUBLIC.relative_to(ROOT).as_posix() in text
write(RUN/'final-chapter-delivery-review-packet-v1.md','''# Short distinct actual-head Chapter1 metadata delivery review

After publish-final-chapter-v1.py actual success, review tmp/online-c1-chapter-audit-final-delivery-state-v1.json and tmp/online-c1-chapter-audit-final-delivery-inputs-v1.json. Hash every fixed current row before/after; examine actual commit/rawdiff/status/non-forcepush/API body-title/base/draft/unmerged, exact field audit and historical1264sixchange snapshot resolution. Reuse accepted source/BODY/post-native/site analysis with exact hashes; no recompile/re-render claim. Verify no website JSON, math, source, roots/Tests/pins/global/unrelated changes since your post-native review. Inspect actual new ledger/C1coverage/OWNdocs/contribution semantic/verification/progress/trial/frontier/memory/helper/prose. Last family convenience table now contains four already compiled names; no new target. Current three website JSON/SITE4 remain unchanged. WholeGoalACTIVE/C2partial/C3-16unenumerated/null/appendixdependencies required/mainliveunchanged. All14RAW exceptions exactbound full2/scoped0; no unexcludedclean or CIbuildpass claimed.

Only write tmp/online-c1-chapter-audit-final-delivery-review-v1.md and .json (both ignored). This avoids another publication/receipt cycle. Do not change tracked flags or other files. Verdict accepted|accepted-with-explicit-delta|rejected, scope the actual finalhead/metadata delivery, list repairs, bind index/report/currenthead and reused receipts. If favorable explicitly certify the scoped Chapter1 local gate and final published metadata delivery, allowing next Chapter2 proof task; never complete wholeGoal or certify merge/live. Runtime-model/human/external/absoluteblind claims prohibited. Requested GPT6Astra/medium. Can use actual live GitHub read-only API to verify head/body if desired; don't send messages/comments. Keep all input rows immutable.
''')
stage=[RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix(),
 'docs/contracts/online-book-v1/coverage.json',*[d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']]]
encoded(RUN/'final-chapter-stage-v1.json',['git','add','--',*stage])
exceptions=load(RUN/'post-native-RAW-exception-addendum-v5.json')['exact_RAW_exceptions'];allowed={Path(r['path']).relative_to(ROOT).as_posix() for r in exceptions}
command=['git','diff','--cached',BASE,'--check'];p=encoded(RUN/'final-chapter-full-diff-v1.json',command,False)
observed={s.split(':',1)[0] for s in p.stdout.decode('utf8').splitlines() if ': trailing whitespace.' in s or ': new blank line at EOF.' in s}
assert observed==allowed and p.returncode==2,(observed-allowed,allowed-observed,p.returncode)
for r in exceptions:assert sha(r['path'])==r['sha256']
encoded(RUN/'final-chapter-scoped-diff-v1.json',command+['--','.',*[':(exclude)'+f for f in sorted(allowed)]])
write(RUN/'final-chapter-checks-v1.json',dict(exact_RAW_exceptions=exceptions,actual_full_diff_exit=2,actual_scoped_diff_exit=0,both_contributor_bases_nonempty=True,
 own_shadow_passed=True,source_math_root_Tests_pins_three_website_JSONs_unchanged=True,site4_and_combined_gate_remain_applicable=True,whole_Goal_status='ACTIVE',final_exact_head_review_required=True))
encoded(RUN/'final-chapter-stage-final-v1.json',['git','add','--',*stage])
out=ROOT/'tmp'
assert subprocess.check_output(['git','check-ignore','tmp/online-c1-chapter-audit-final-delivery-state-v1.json'],encoding='utf8').strip()
before=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip();assert before=='14567d019c31f8f307ac5ab765144ae7d71f1ea1'
encoded(out/'online-c1-chapter-audit-final-delivery-commit-v1.json',['git','commit','-m','Accept scoped Chapter1 source reconciliation with delivery evidence'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert subprocess.check_output(['git','rev-parse','HEAD^'],encoding='utf8').strip()==before
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
fixed()
encoded(out/'online-c1-chapter-audit-final-delivery-push-v1.json',['git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','origin',BRANCH])
beforepr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/203'],encoding='utf8'))
encoded(out/'online-c1-chapter-audit-final-delivery-body-v1.json',['gh','pr','edit','203','--body-file',str(RUN/'PR-BODY-final-v3.md')])
pr=json.loads(encoded(out/'online-c1-chapter-audit-final-delivery-PR203-API-v1.json',['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/203']).stdout.decode('utf8'))
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['sha']==head and pr['base']['sha']==BASE and pr['base']['ref']=='codex/research-online-ftl-obstruction'
assert pr['title']==beforepr['title'] and pr['body'].strip()==body.strip()
remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BRANCH],encoding='utf8').split()[0];assert remote==head
canonical=subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','HEAD'],encoding='utf8').strip()
assert canonical==subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip()=='6847b678a73db68dee5101d6f05c2453c1405afc'
assert not subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf8').strip()
encoded(out/'online-c1-chapter-audit-final-delivery-diff-v1.json',['git','diff',before,head,'--'])
checks=encoded(out/'online-c1-chapter-audit-final-delivery-CI-v1.json',['gh','pr','checks','203','--json','name,state,link'],False)
state=dict(PR_url=pr['html_url'],actual_local_head=head,actual_remote_head=remote,previous_published_source_head=before,
 stack_base=BASE,stack_base_branch=pr['base']['ref'],title=pr['title'],draft=True,state='open',merged=False,
 published_body_sha256=sha(RUN/'PR-BODY-final-v3.md'),actual_published_body_matches=True,canonical_main=canonical,canonical_dirty=False,
 worktree_dirty=False,worktree_preserved_active=True,three_website_JSONs_unchanged=True,source_math_roots_Tests_pins_unchanged=True,
 actual_commit_push_success=True,whole_Goal_status='ACTIVE',final_distinct_exact_head_review_pending=True,main_live_updated=False,deployed=False,
 source_FINAL_sha256=sha(RUN/'FINAL-receipt-v1.json'),post_native_sha256=sha(RUN/'post-native-receipt-v1.json'),CI_not_certified=True)
write(out/'online-c1-chapter-audit-final-delivery-state-v1.json',state)
paths={Path(r['path']) for r in load(RUN/'post-native-inputs-v1.json')['rows']}
paths.update(p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.update(p for p in out.glob('online-c1-chapter-audit-final-delivery-*.json') if p.is_file())
assert all(p.is_file() for p in paths)
write(out/'online-c1-chapter-audit-final-delivery-inputs-v1.json',dict(phase='short distinct actual final-head/metadata delivery review',rows=rows(paths),actual_head=head,whole_Goal_status='ACTIVE',proof_total=None))
print('Final metadata/evidence actual commit/push/body verified:',head,'; clean checkout; short distinct exact-head review next.',flush=True)
