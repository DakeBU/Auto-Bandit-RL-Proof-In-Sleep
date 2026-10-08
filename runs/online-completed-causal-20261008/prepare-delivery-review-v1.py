from common_accepted_v5 import *

accepted_fixed()
post = load(RUN / 'post-native-receipt-v1.json')
assert post['verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert post['inputs_unchanged'] and not post['required_blocking_repairs']
assert post['report_sha256'] == sha(RUN / 'post-native-review-v1.md')
assert all(sha(r['path']) == r['sha256'] for r in load(RUN / 'post-native-review-inputs-v1.json')['rows'])
delivery = load(RUN / 'actual-draft-delivery-v1.json')
assert delivery['PR'] == 199 and delivery['basePR'] == 198 and delivery['exact_base'] == BASE
assert not delivery['merged'] and not delivery['live']
assert not load(RUN / 'official-app-attachment-v1.json')['actual_isError']
assert load(RUN / 'reviewed-draft-remote-v1.log')['headRefOid'] == delivery['verified_delivery_head']
gate('delivery-base-PR198-v1', 'gh', 'pr', 'view', '198', '--json',
     'number,url,state,isDraft,headRefOid,headRefName,mergedAt')
base_remote = load(RUN / 'delivery-base-PR198-v1.log')
assert base_remote['headRefOid'] == BASE
assert base_remote['headRefName'] == 'codex/research-online-ae-causal'
assert base_remote['state'] == 'OPEN' and base_remote['isDraft'] and base_remote['mergedAt'] is None
write(RUN / 'delivery-base-verification-v1.json', dict(actual_base=base_remote,
      exact_stacked_base=BASE, basePR=198, source_commit=delivery['verified_delivery_head'],
      ownPR=199, merged=False, live=False, chapter_complete=False, goal_complete=False))
files = ['common_accepted_v5.py', 'prepare-reviewed-commit-v5.py', 'deliver-reviewed-draft-v5.py',
         'prepare-delivery-review-v1.py', 'finish-delivery-evidence-v1.py',
         'accepted-source-commit-v1.json', 'accepted-diff-raw-exceptions-v1.json',
         'accepted-full-diff-v1.log', 'accepted-full-diff-v1-exit.json',
         'accepted-scoped-diff-v1.log', 'accepted-scoped-diff-v1-exit.json',
         'contributor-accepted-stacked-v1.log', 'contributor-accepted-stacked-v1-exit.json',
         'contributor-accepted-origin-main-v1.log', 'contributor-accepted-origin-main-v1-exit.json',
         'reviewed-draft-push-v1.log', 'reviewed-draft-push-v1-exit.json',
         'reviewed-draft-create-v1.log', 'reviewed-draft-create-v1-exit.json',
         'reviewed-draft-remote-v1.log', 'reviewed-draft-remote-v1-exit.json',
         'actual-draft-delivery-v1.json', 'official-app-attachment-v1.json',
         'post-native-review-v1.md', 'post-native-receipt-v1.json',
         'prospective-PR-title-v1.txt', 'prospective-PR-body-v1.md',
         'delivery-base-PR198-v1.log', 'delivery-base-PR198-v1-exit.json',
         'delivery-base-verification-v1.json']
rows = raw_index([RUN / p for p in files] + [PUBLIC, CANARY])
write(RUN / 'delivery-review-inputs-v1.json', dict(
    phase='Actual scoped acceptance commit/push/OPEN draft199/official app attachment delivery',
    rows=rows, fixed_input_count=len(rows), exact_creation_head=delivery['verified_delivery_head'],
    exact_stacked_base=BASE, basePR=198, ownPR=199, remote_CI_verified=False,
    chapter_complete=False, goal_complete=False, main_or_live_updated=False))
write(RUN / 'delivery-review-packet-v1.md',
      'Independently hash this exact delivery index before/after. Audit actual scoped acceptance/source-evidence commits, both contributor passes, exact RAW whitespace exceptions (unexcluded2/scoped0), actual push/create/view0 and official app attachment. Verify PR199 OPENdraft unmerged, exact reviewed title/body v1, creation headdfbdedc520850fb1f6fe736462810accfab3ab0b, stacked base PR198 exact8dcdf1e5d74b79ee90d2dd27a48569e9cb4f7fe6 and actual current remote base capture. Existing source/native/post-native bindings remain frozen through accepted_fixed; production/canary/root/readers/pins unchanged.\n\n'
      'Review finish-delivery-evidence-v1.py as a prospective evidence-only commit/push helper. It must restrict every changed/untracked path to THIS RUN, bind your favorable report/receipt and unchanged delivery inputs, preserve exact RAW output only with explicit hash exceptions, push without force, save authoritative final head/remote/clean receipt ONLY under ignored tmp to avoid self-referential hash claims. No source/reader/contract/journal edits or merge/deploy authorized. Remote CI is unverified here and must not be certified. Only4derivedproof obligations accepted; original16 source objects/proof-totalnull/general causal kernel and all other required source/chapter/appendix gaps preserved; whole Goal ACTIVE. Return ONLY delivery-review-v1.md / delivery-receipt-v1.json with actual count/RAWbeforeafter/reportSHA/verdict/required_blocking_repairs and exact permitted next evidence-only boundary. Disclose reused distinct automated actor; requested Astra/medium, no absolute-blind/human/external/runtime attestation.\n')
print('Delivery fixed RAW input count:', len(rows), 'actual OPENdraft199, remote CI unverified.', flush=True)
