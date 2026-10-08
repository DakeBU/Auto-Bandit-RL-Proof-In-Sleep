from common_accepted_v4 import *
from importlib.machinery import SourceFileLoader

accepted_fixed()
delivery = SourceFileLoader('deliver_reviewed_v4',str(RUN/'deliver-reviewed-v4.py')).load_module()
assert load(RUN/'scoped-diff-delivery-v4-exit.json')['exit_code'] == 1
assert load(RUN/'branch-push-v4-exit.json')['exit_code'] == 0
old = load(RUN/'diff-raw-bound-exceptions-v7.json')['exceptions']
assert len(old) == 12
for row in old:
    assert sha(row['path']) == row['sha256']
new = [dict(path=(RUN.relative_to(ROOT)/name).as_posix(),sha256=sha(RUN/name),
    reason='Exact post-publication GitHub remote/failure-check stdout; only quoted trailing whitespace. Preserve actual delivery failure, no code exemption.')
    for name in ['branch-push-v4.log','scoped-diff-delivery-v4.log']]
write(RUN/'diff-raw-bound-exceptions-v5-delivery.json',dict(exceptions=old+new,
    original_FINAL_reviewed_12_unchanged=True,post_publication_raw_stdout_files=2,full_unexcluded_diff_passed=False,
    original_FINAL_acceptance_math_reader_inputs_unchanged=True,distinct_delivery_metadata_review_pending=True,
    no_production_test_reader_contract_other_helper_exception=True,chapter_complete=False,goal_complete=False))
text=(RUN/'check-scoped-diff-v7.py').read_text(encoding='utf8')
text=text.replace('diff-raw-bound-exceptions-v7.json','diff-raw-bound-exceptions-v5-delivery.json').replace('len(exceptions) == 12','len(exceptions) == 14')
text=text.replace("'overflow-diagnostic-helper-v5.log', 'pre-FINAL-full-diff-v7.log'}", "'overflow-diagnostic-helper-v5.log', 'pre-FINAL-full-diff-v7.log', 'branch-push-v4.log', 'scoped-diff-delivery-v4.log'}")
write(RUN/'check-scoped-diff-delivery-v5.py',text)
write(RUN/'delivery-evidence-repair-v5.json',dict(actual_delivery_checker_exit_code=1,underlying_git_diff_check_exit_code=2,
    actual_cause='GitHub first push remote: stdout includes its own trailing spaces; failed checker stdout repeats them.',
    repair='Retain two new exact raw stdout files, extend individually hashed exceptions12->14 for delivery metadata only; no production/source/reader edit.',
    draft_PR=194,PR_state='OPENdraft-unmerged-appattached',native_mathematical_acceptance_unchanged=True,
    original_FINAL_reader_package_accepted=True,distinct_delivery_review_pending=True,chapter_complete=False,goal_complete=False))
delivery.stage_owned()
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE,'--','.']
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert child.returncode == 2
output=child.stdout.decode('utf8',errors='strict')
findings={line.split(':',1)[0] for line in output.splitlines() if line.startswith(RUN.relative_to(ROOT).as_posix()+'/') and ': ' in line}
assert findings == {row['path'] for row in old+new},findings
write(RUN/'delivery-full-unexcluded-diff-v5.json',dict(command=command,actual_exit_code=child.returncode,stdout=output,
    stdout_stored_as_exact_JSON_string_not_normalized=True,actual_individually_bound_files=14,passed=False))
gate('scoped-diff-delivery-repair-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-delivery-v5.py','delivery-repair-v5')
write(RUN/'prospective-pr-body-v5.md',(RUN/'prospective-pr-body-v4.md').read_text(encoding='utf8')+'''
Delivery evidence update: after creating this draft, GitHub's successful first-push stdout and the resulting failed whitespace-check stdout added two raw evidence files. The original twelve FINAL-reviewed exceptions remain unchanged; delivery uses fourteen individually SHA-bound files and a separately passing scoped check. Full unexcluded diff remains exit2. This update changes no Lean statement/proof, reader, source assumption or chapter/program boundary; both the failure and subsequent distinct metadata review are preserved in the same run.
''')
write(RUN/'delivery-reader-packet-v5.md','''# Required limited post-publication delivery evidence review

Same distinct /root/source_reviewer/requested Astra medium; no escalation or external/runtime attestation. Rehash every delivery-reader-inputs-v5 row before/after. Actual FINALv4 accepted876/native8->0 is unchanged, all earlier rejected reports retained. Current PR194 OPENdraft/unmerged/appattached exact initial head a33dff145f5aef135170b141cc195bec9133a688 on exact PR193 basebf9f896...; final metadata commit/push/DIRECT stillpending. Successful first push log has GitHub remote trailing spaces; actual close-delivery check exited1 because underlying unexcluded whitespace exit2. Two individually SHA-bound RAW STDOUT entries ONLY extend old12 exceptions to14; failedstdout also quotes rawspaces. All original12 exacthashes remain, twofrozenhelperEOFexceptions alreadyjudged; no production/test/reader/contract/other-helper exemption. Fresh full unexcluded actual14finding set stored as exact JSON string (no stdout normalization), stillexit2; newscoped gate actualexit0. Original math/reader/FINAL876 inputs resolve only original10ownedacceptedmetadata; verify accepted_fixed and no proof/site changes. Sharedsite/current14pixels rehashed; earlier actual ROOT+your original v9views reused, no new render/canary/Leangate claimed.

Review prepared check-scoped-diff-delivery-v5.py/repair-v5 evidence and prospective-pr-body-v5: immutable body-v4 is initial acceptedprose; v5 adds ONLY one explicitly post-publication paragraph qualifying original12 vsdelivery14 and failure. If accepted, future permitted action is ONLY update OWN draft PR194 body via exactbody-v5 --body-file, commit own delivery evidence/appends and push, then actual clean/remote/REST/raw DIRECT audit. Title, code/readers/source/branch/base/goal boundaries unchanged. Earlier operative publicationv4 remains immutable history for creation; accepted deliveryv5 governs this evidence-only body update. No merge/deploy/retirement/chapter/Goalcomplete. Userauthorization persists for own draft PR/evidence; no new humanpermission needed. Do not certify final push alreadyhappened.

Write ONLY delivery-reader-review-v5.md and delivery-reader-receipt-v5.json with actor.task/verdict/report+SHA/fixed_input_count/ALL rows+inputmanifest+report bound, before_after_raw_hashes_match,required_repairs/required_mathematical_repairs/required_metadata_repairs/required_blocking_reader_repairs arrays. Judge original12 preserved/new2rawonly/helper and no other exemption; exactsingleparagraph bodydiff permitted, source/native acceptance unchanged, chapter/Goalfalse. No other edits.
''')
paths=[RUN/name for name in ['final-reader-review-v4.md','final-reader-receipt-v4.json','final-reader-inputs-v4.json',
    'native-acceptance-overlay-v4.json','accepted-decision-v4.json','diff-raw-bound-exceptions-v7.json',
    'diff-raw-bound-exceptions-v5-delivery.json','check-scoped-diff-delivery-v5.py','delivery-evidence-repair-v5.json',
    'delivery-full-unexcluded-diff-v5.json','scoped-diff-delivery-v4.log','scoped-diff-delivery-v4-exit.json',
    'scoped-diff-delivery-repair-v5.log','scoped-diff-delivery-repair-v5-exit.json','scoped-diff-delivery-repair-v5.json',
    'branch-push-v4.log','branch-push-v4-exit.json','created-PR-v4.json','app-attach-v4.json','PR-payload-v4.json',
    'prospective-pr-title-v4.txt','prospective-pr-body-v4.md','prospective-pr-body-v5.md','proposed-publication-v4.md',
    'delivery-reader-packet-v5.md','prepare-delivery-evidence-repair-v5.py','delivery-obligations-overlay-v4.json','delivery-handoff-v4.md',
    'common_accepted_v4.py','registry-v9.json','pixel-review-v9.json']]
paths += [Path(x['path']) for x in old+new]+[PUBLIC,CANARY,MANIFEST,Path('BanditRLProof.lean'),Path('Tests.lean')]
paths += [Path(row['path']) for row in load(RUN/'formula-render-v9.json')['images']]
rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in dict.fromkeys(paths)]
write(RUN/'delivery-reader-inputs-v5.json',dict(rows=rows,fixed_input_count=len(rows),package_math_native_accepted=True,
    delivery_evidence_review_pending=True,chapter_complete=False,goal_complete=False))
accepted_fixed()
print('Limited delivery evidence review actual rows:',len(rows),'; no original acceptance/source/reader change.')
