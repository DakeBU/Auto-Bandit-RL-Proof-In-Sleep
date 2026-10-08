from commit_owned_v3 import *

accepted_fixed()
post=load(RUN/'post-native-receipt-v1.json')
assert post['actor']['task']=='/root/source_reviewer'
assert post['verdict'] in ['accepted','accepted-with-explicit-delta'] and post['inputs_unchanged']
assert post['before_after_raw_hashes_match'] and not post['required_blocking_repairs']
assert sha(post['report'])==post['report_sha256']
index=load(RUN/'post-native-review-inputs-v1.json')
reviewed={Path(x['path']).resolve().as_posix():x.get('sha256',x.get('sha256_raw_bytes')) for x in post['reviewed_files']}
assert post['fixed_input_count']==len(index['rows'])==index['fixed_input_count']
for row in index['rows']:
    assert sha(row['path'])==row['sha256']==reviewed[Path(row['path']).resolve().as_posix()]
exceptions=load(RUN/'diff-raw-bound-exceptions-v2.json')['exceptions']
assert len(exceptions)==11
for e in exceptions: assert sha(e['path'])==e['sha256']
stage_owned()
gate('accepted-scoped-diff-v1','git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol',
    'diff','--cached','--check',BASE,'--','.',*[':(exclude)'+e['path'] for e in exceptions])
commit_owned('Accept bounded IID success proofs after separate source, reader and native audits')
gate('contributor-accepted-committed-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
write(RUN/'accepted-commit-v1.json',dict(commit=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),
    branch=BRANCH,base_head=BASE,base_PR=195,source_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    applicable_site_commit=load(RUN/'registry-v1.json')['source_commit'],
    final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),post_native_receipt_sha256=sha(RUN/'post-native-receipt-v1.json'),
    actual_contributor_exit=0,PR_delivery_pending=True,chapter_complete=False,goal_complete=False))
commit_owned('Record bounded IID success accepted commit and contributor evidence')
accepted_fixed()
print('Reviewed bounded package committed, current own worktree clean; actual push/draft delivery pending.')
