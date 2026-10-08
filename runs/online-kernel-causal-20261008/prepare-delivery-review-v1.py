from common_accepted_v1 import *

accepted_fixed()
post=load(RUN/'post-native-receipt-v1.json')
assert post['verdict'] in ['accepted','accepted-with-explicit-delta']
assert post['inputs_unchanged'] and not post['required_blocking_repairs']
assert post['report_sha256'] == sha(RUN/'post-native-review-v1.md')
assert all(sha(x['path']) == x['sha256'] for x in load(RUN/'post-native-review-inputs-v1.json')['rows'])
delivery=load(RUN/'actual-draft-delivery-v1.json')
assert delivery['basePR'] == 199 and delivery['exact_base'] == BASE
assert not delivery['merged'] and not delivery['live']
assert not load(RUN/'official-app-attachment-v1.json')['actual_isError']
assert load(RUN/'reviewed-draft-remote-v1.log')['headRefOid'] == delivery['verified_delivery_head']
gate('delivery-base-PR199-v1','gh','pr','view','199','--json','number,url,state,isDraft,headRefOid,headRefName,mergedAt')
base=load(RUN/'delivery-base-PR199-v1.log')
assert base['headRefOid'] == BASE and base['headRefName'] == 'codex/research-online-completed-causal'
assert base['state'] == 'OPEN' and base['isDraft'] and base['mergedAt'] is None
write(RUN/'delivery-base-verification-v1.json',dict(actual_base=base,exact_stacked_base=BASE,basePR=199,
    ownPR=delivery['PR'],source_commit=delivery['verified_delivery_head'],merged=False,live=False,chapter_complete=False,goal_complete=False))
files=['common_accepted_v1.py','prepare-reviewed-commit-v1.py','deliver-reviewed-draft-v1.py',
    'prepare-delivery-review-v1.py','finish-delivery-evidence-v1.py','accepted-source-commit-v1.json',
    'accepted-diff-raw-exceptions-v1.json','accepted-full-diff-v1.log','accepted-full-diff-v1-exit.json',
    'accepted-scoped-diff-v1.log','accepted-scoped-diff-v1-exit.json',
    'contributor-accepted-stacked-v1.log','contributor-accepted-stacked-v1-exit.json',
    'contributor-accepted-origin-main-v1.log','contributor-accepted-origin-main-v1-exit.json',
    'reviewed-draft-push-v1.log','reviewed-draft-push-v1-exit.json',
    'reviewed-draft-create-v1.log','reviewed-draft-create-v1-exit.json',
    'reviewed-draft-remote-v1.log','reviewed-draft-remote-v1-exit.json',
    'actual-draft-delivery-v1.json','official-app-attachment-v1.json',
    'post-native-review-v1.md','post-native-receipt-v1.json','prospective-PR-title-v1.txt','prospective-PR-body-v1.md',
    'delivery-base-PR199-v1.log','delivery-base-PR199-v1-exit.json','delivery-base-verification-v1.json']
rows=raw_index([RUN/p for p in files]+[PUBLIC,CANARY])
write(RUN/'delivery-review-inputs-v1.json',dict(rows=rows,fixed_input_count=len(rows),
    phase='Actual causal-kernel scoped commit/push/OPEN draft/official attachment delivery',
    exact_creation_head=delivery['verified_delivery_head'],exact_stacked_base=BASE,basePR=199,ownPR=delivery['PR'],
    remote_CI_verified=False,chapter_complete=False,goal_complete=False,main_or_live_updated=False))
write(RUN/'delivery-review-packet-v1.md',
    'Independently hash every exact current delivery RAW input before/after. Audit actual acceptance/evidence commits, both contributor gates, RAW whitespace exceptions(unexcluded2/scoped0), push/create/view0, OPENdraft head/base/title/body exactness and official app attachment. Actual basePR199 remains OPENdraft exact4db37e090143760d99b9aedd026a72fa0f1f09ac. Existing source/FINAL/native/post-native bindings remain strict through accepted_fixed; no source/reader/pin changes. Remote CI remains unverified.\n\n'
    'Review prospective finish-delivery-evidence-v1.py as an evidence-only commit/push helper. Every changed/untracked path must belong to THIS RUN; bind favorable report/receipt and exact current inputs; whitespace exemptions only exact reviewed RAW command logs, no executable exception; nonforce push exactly once; bounded subsequent READONLY head polling up to3 without repeating push. Actual final head/remote/clean receipts saved only under ignored tmp to avoid self-reference. No source/reader/contract/journal edits, merge/deploy or chapter/Goal acceptance. Only5derived obligations accepted; original16/null/arbitrary-protocol/other required C1C2/C3-16/appendices remain, whole Goal ACTIVE. Return ONLY delivery-review-v1.md/delivery-receipt-v1.json with count/beforeafter/reportSHA/verdict/blockers and exact permitted next evidence-only scope. Reused distinct automated actor Astra/medium; no human/external/absolute-blind/runtime attestation.\n')
print('Actual delivery fixed RAW count:',len(rows),'OPEN draft',delivery['PR'],flush=True)
