from commit_owned_v1 import *
post_fixed()
d=load(RUN/'actual-draft-delivery-v1.json')
assert d['PR']==201 and d['exact_base']==BASE and d['basePR']==200
assert not d['merged'] and not d['live'] and d['official_app_attachment_completed']
assert not load(RUN/'official-app-attachment-v1.json')['actual_isError']
files=['common_accepted_v2.py','commit_owned_v1.py','prepare-reviewed-commit-v1.py','deliver-reviewed-draft-v1.py',
    'finish-delivery-evidence-v1.py','prepare-delivery-review-v1.py','accepted-source-commit-v1.json','accepted-commit-v1.log',
    'accepted-full-diff-v1.log','accepted-full-diff-v1-exit.json','accepted-scoped-diff-v1.log','accepted-scoped-diff-v1-exit.json',
    'accepted-diff-raw-exceptions-v1.json','reviewed-draft-push-v1.log','reviewed-draft-push-v1-exit.json',
    'reviewed-draft-create-v1.log','reviewed-draft-create-v1-exit.json','reviewed-draft-remote-v1.log','reviewed-draft-remote-v1-exit.json',
    'actual-draft-created-v1.json','actual-draft-delivery-v1.json','official-app-attachment-v1.json',
    'post-native-review-v1.md','post-native-receipt-v1.json','prospective-PR-title-v1.txt','prospective-PR-body-v1.md',
    'delivery-base-PR200-v1.log','delivery-base-PR200-v1-exit.json','delivery-base-verification-v1.json',
    'candidate-contributor-stack-v2.log','candidate-contributor-stack-v2-exit.json',
    'candidate-contributor-main-v2.log','candidate-contributor-main-v2-exit.json',
    'contributor-accepted-stack-v1.log','contributor-accepted-stack-v1-exit.json',
    'contributor-accepted-main-v1.log','contributor-accepted-main-v1-exit.json']
indexed=rows([RUN/p for p in files]+[PUBLIC,CANARY])
write(RUN/'delivery-review-inputs-v1.json',dict(rows=indexed,fixed_input_count=len(indexed),
    actual_PR=201,creation_head=d['verified_delivery_head'],exact_base=BASE,basePR=200,
    remote_CI_certified=False,chapter_complete=False,goal_complete=False,main_or_live_updated=False))
write(RUN/'delivery-review-packet-v1.md',
    'Independent actual delivery review: hash EVERY current indexed RAW input before/after. Audit actual candidate and accepted/evidence commits, original full-diff2/scoped0 exact RAW-log exceptions, repaired/nonempty both-base contributor checks, push/create/remote0 and OPENdraft PR201 exact4d98e1aa6051cee62c032c550fbe4502d11ea8aa creation head, base codex/research-online-kernel-causal exact71c PR200 OPENdraft unmerged, exact reviewed title/body, official app attachment tool resultisErrorfalse. Source/native/FINAL-v2/post-native exact bindings remain enforced; no proof/reader/pin change. Remote CI unverified, main/live unchanged, GoalACTIVE.\n\n'
    'Inspect future finish-delivery-evidence-v1.py. Permit only THIS RUN evidence files commit/nonforce push, require favorable report/receipt/all fixed current hashes, no source/reader/contract/task/journal edits. Exact reviewed RAW command-output exceptions only, no executable/source exception. Final clean/head/remote checks saved in ignored tmp to avoid self-reference. No repeated push while polling; at most three bounded READONLY remote snapshots. No merge/deploy/retire/chapter/Goal completion. Five derived hinges only; boundedoscillation/allcomparatorconverse/original16/null/remainingbook obligations required.\n\n'
    'Outputs ONLY delivery-review-v1.md and delivery-receipt-v1.json: verdict/fixed_input_count/reviewed_files(include index hash)/raw_input_checks(path,before_sha256,after_sha256,unchanged)/inputs_unchanged/report_sha256/required_blocking_repairs/permitted_next_evidence_only_scope. Reused distinct automated actor requested Astra/medium not runtime-attested. No input/native/git/site mutations.\n')
print('Actual delivery fixed RAW count:',len(indexed),flush=True)
