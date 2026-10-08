from common_accepted_v3 import *

accepted_fixed()
post=load(RUN/'post-native-receipt-v2.json')
assert post['verdict']=='accepted-with-explicit-delta' and post['inputs_unchanged'] and not post['required_blocking_repairs']
assert sha(RUN/'post-native-review-v2.md')==post['report_sha256']
delivery=load(RUN/'actual-draft-delivery-v3.json')
assert delivery['PR']==198 and delivery['exact_base']==BASE and not delivery['merged'] and not delivery['live']
assert not load(RUN/'official-app-attachment-v3.json')['actual_isError']
assert load(RUN/'reviewed-draft-remote-v3.log')['headRefOid']==delivery['verified_delivery_head']
files=['common_accepted_v3.py','prepare-reviewed-commit-v3.py','deliver-reviewed-draft-v3.py',
    'accepted-source-commit-v3.json','accepted-diff-raw-exceptions-v3.json',
    'accepted-full-diff-v3.log','accepted-full-diff-v3-exit.json','accepted-scoped-diff-v3.log','accepted-scoped-diff-v3-exit.json',
    'contributor-accepted-stacked-v5.log','contributor-accepted-stacked-v5-exit.json',
    'contributor-accepted-origin-main-v5.log','contributor-accepted-origin-main-v5-exit.json',
    'reviewed-draft-push-v3.log','reviewed-draft-push-v3-exit.json',
    'reviewed-draft-create-v3.log','reviewed-draft-create-v3-exit.json',
    'reviewed-draft-remote-v3.log','reviewed-draft-remote-v3-exit.json','actual-draft-delivery-v3.json',
    'official-app-attachment-v3.json','post-native-review-v2.md','post-native-receipt-v2.json',
    'prospective-PR-title-v2.txt','prospective-PR-body-v2.md','delivery-base-verification-v5.json',
    'future-completion-api-v1.lean','future-completion-api-v1.log','future-completion-api-v1-exit.json','future-completion-api-result-v1.json']
rows=raw_index([RUN/p for p in files]+[PUBLIC,CANARY])
write(RUN/'delivery-review-inputs-v3.json',dict(phase='Actual scoped commit/push/OPEN draft198/app attachment delivery',rows=rows,
    fixed_input_count=len(rows),native_post_review_accepted=True,exact_creation_head=delivery['verified_delivery_head'],
    exact_stacked_base=BASE,basePR=197,ownPR=198,remote_CI_verified=False,
    chapter_complete=False,goal_complete=False,main_or_live_updated=False))
write(RUN/'delivery-review-packet-v3.md',
    'Independently hash this fixed delivery index before/after and audit actual scoped commits14cd/382621, contributor5 passes, precise raw whitespace exceptions (full check2, scoped0), push/create/view actual0 and official app attachment result. Verify actual remote creation title/body exactly reviewed v2 after AE-unit F1 repair, actual head382621, OPENdraft198 stackedon197exact4ca, no merge/live/deploy. Source/native/post-native receipts remain frozen via accepted_fixed; public/canary/root/readers/pins unchanged.\n\n'
    'Future-completion-api-v1 is only a read-only named declaration/type probe actualLean0, no proof/body/targetfreeze/mathematicalprogress; it does not close required completion/kernel. Inspect it as delivery evidence, not a new chapter result. A later scoped delivery-evidence commit/push may advance PR head while changing only own RUN evidence; no production/reader/contract/journal changes authorized by that suffix. Remote CI currently unverified, do not certify it. Only3derivedAEobligations accepted; full16sourceGoal active. Return ONLY delivery-review-v3.md / delivery-receipt-v3.json with fixed count, actual before/after/raw hashes/reportSHA, verdict/blockers and permitted future evidence-only commit/push boundary. Reused distinct automated actor disclosed; Astra/medium requested, no human/external/runtime attestation.\n')
print('Delivery fixed RAW input count:',len(rows),'actual OPENdraft198, remote CI unverified.',flush=True)
