from commit_owned_v1 import *

post_fixed()
d=load(RUN/'actual-draft-delivery-v1.json')
assert d['exact_base']==BASE and d['basePR']==201
assert not d['merged'] and not d['live'] and d['official_app_attachment_completed']
assert not load(RUN/'official-app-attachment-v1.json')['actual_isError']
files=['common_accepted_v1.py','commit_owned_v1.py','prepare-reviewed-commit-v1.py','deliver-reviewed-draft-v1.py',
    'verify-actual-delivery-v1.py','finish-delivery-evidence-v1.py','prepare-delivery-review-v1.py',
    'accepted-source-commit-v1.json','accepted-commit-v1.log',
    'accepted-full-diff-v1.log','accepted-full-diff-v1-exit.json',
    'accepted-scoped-diff-v1.log','accepted-scoped-diff-v1-exit.json','accepted-diff-raw-exceptions-v1.json',
    'reviewed-draft-push-v1.log','reviewed-draft-push-v1-exit.json',
    'reviewed-draft-create-v1.log','reviewed-draft-create-v1-exit.json',
    'reviewed-draft-remote-v1.log','reviewed-draft-remote-v1-exit.json',
    'actual-draft-created-v1.json','actual-draft-delivery-v1.json','official-app-attachment-v1.json',
    'post-native-review-v1.md','post-native-receipt-v1.json','prospective-PR-title-v1.txt','prospective-PR-body-v1.md',
    'delivery-base-PR201-v1.log','delivery-base-PR201-v1-exit.json','delivery-base-verification-v1.json',
    'candidate-contributor-stack-v1.log','candidate-contributor-stack-v1-exit.json',
    'candidate-contributor-main-v1.log','candidate-contributor-main-v1-exit.json',
    'contributor-accepted-stack-v1.log','contributor-accepted-stack-v1-exit.json',
    'contributor-accepted-main-v1.log','contributor-accepted-main-v1-exit.json']
indexed=rows([RUN/p for p in files]+[PUBLIC,CANARY])
write(RUN/'delivery-review-inputs-v1.json',dict(rows=indexed,fixed_input_count=len(indexed),
    actual_PR=d['PR'],creation_head=d['verified_delivery_head'],exact_base=BASE,basePR=201,
    remote_CI_certified=False,chapter_complete=False,goal_complete=False,main_or_live_updated=False))
write(RUN/'delivery-review-packet-v1.md',
    'Independent actual delivery review: hash EVERY current indexed RAW input before/after. Audit actual candidate and accepted/evidence commits, full-diff/scoped-diff exact RAW exceptions, nonempty both-base contributor checks, actual push/create/remote exits0 and OPEN draft PR'+str(d['PR'])+' exact creation head '+d['verified_delivery_head']+', stacked base codex/research-online-c1-source-reconcile exact224927197e78e1330c4c93e84f9c69388d3027a7 PR201 OPEN draft unmerged, exact reviewed title/body, official app attachment actual tool result isError false. FINAL493/post-native/accepted bindings remain enforced; no proof/reader/pin change. Remote CI unverified, main/live unchanged, Goal ACTIVE.\n\n'
    'Inspect future finish-delivery-evidence-v1.py. Permit only THIS RUN evidence files commit/nonforce push, require favorable report/receipt/all fixed current hashes, no source/reader/contract/task/journal edits. Exact reviewed RAW command-output exceptions only; no executable/source exemption. Final clean/head/remote checks saved in ignored tmp to avoid self-reference. No repeated push while polling; at most three bounded READONLY remote snapshots. No merge/deploy/retire/chapter/Goal completion. Four DERIVED terminals only; original16/null fullChapter1 reconciliation and remaining book/appendix obligations stay required.\n\n'
    'Outputs ONLY delivery-review-v1.md and delivery-receipt-v1.json: verdict/fixed_input_count/reviewed_files(include index hash)/raw_input_checks(path,before_sha256,after_sha256,unchanged)/inputs_unchanged/report_sha256/required_blocking_repairs/permitted_next_evidence_only_scope. Reused distinct automated actor requested Astra/medium not runtime-attested. No input/native/git/site mutations.\n')
print('Actual delivery fixed RAW count:',len(indexed),flush=True)
