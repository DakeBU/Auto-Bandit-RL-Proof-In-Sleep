from common_accepted_v3 import *
from commit_owned_v2 import stage_owned, commit_owned

accepted_fixed()
r = reviewer_receipt('delivery-raw-receipt-v4.json')
inputs = load(RUN/'delivery-raw-review-inputs-v4.json')
assert r['inputs_unchanged'] and r['fixed_input_count'] == len(inputs['rows']) == 28
reviewed = {Path(x['path']).resolve().as_posix():x.get('sha256',x.get('sha256_raw_bytes')) for x in r['reviewed_files']}
for row in inputs['rows']:
    assert sha(row['path']) == reviewed[Path(row['path']).resolve().as_posix()] == row['sha256']
proposal = load(RUN/'proposed-publication-delivery-v4.json')
for key in ['title','body']:
    assert sha(proposal[key+'_path']) == proposal[key+'_sha256']
request = dict(title=Path(proposal['title_path']).read_text(encoding='utf8').rstrip('\n'),
    body=Path(proposal['body_path']).read_text(encoding='utf8'))
write(RUN/'PR195-reviewed-body-update-input-v4.json',request)
gate('actual-PR195-reviewed-body-update-v4','gh','api','--method','PATCH',
    'repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/195','--input',RUN/'PR195-reviewed-body-update-input-v4.json')
actual = load(RUN/'actual-PR195-reviewed-body-update-v4.log')
assert actual['title'] == request['title'] and actual['body'] == request['body']
assert actual['state'] == 'open' and actual['draft'] and not actual['merged'] and actual['merged_at'] is None
assert actual['base']['sha'] == BASE and actual['base']['ref'] == BASE_BRANCH
assert actual['head']['sha'] == load(RUN/'publication-source-head-v3.json')['head']
write(RUN/'delivery-PR195-exact-body-update-v4.json',dict(PR=195,actual_title_body_match_reviewed_v4=True,
    reviewed_body_sha256=proposal['body_sha256'],original_creation_body_v3_preserved=True,
    source_gate_RAW_exceptions=5,delivery_new_RAW_exceptions=2,complete_delivery_RAW_exceptions=7,
    executable_helper_exemptions=0,delivery_review_sha256=sha(RUN/'delivery-raw-receipt-v4.json'),
    state='OPEN',draft=True,merged=False,chapter_complete=False,goal_complete=False))
overlay = load(RUN/'delivery-obligations-overlay-v3.json')
overlay['exact_RAW_stdout_exceptions'] = 7
overlay['source_acceptance_RAW_stdout_exceptions'] = 5
overlay['new_delivery_RAW_stdout_exceptions'] = 2
overlay['exact_reviewed_title_and_body_bytes'] = 'Actual PATCH equals newly reviewed v4; creation matched original reviewed v3.'
overlay['actual_delivery_repair_review_sha256'] = sha(RUN/'delivery-raw-receipt-v4.json')
overlay['original_delivery_overlay_v3_sha256'] = sha(RUN/'delivery-obligations-overlay-v3.json')
write(RUN/'delivery-obligations-overlay-v4.json',overlay)
write(RUN/'delivery-handoff-v4.md', '''# Current bounded draft PR195 delivery

Use delivery-obligations-overlay-v4.json and delivery-PR195-exact-body-update-v4.json as the operative delivery records. Original v3 creation/body/overlay records remain historical. Exact source-frozen proof acceptance used five SHA-bound raw stdout exceptions; current complete delivery uses those unchanged five plus exactly Git remote stdout and its failed-check stdout, separately source-reviewer accepted. Zero production/Test/reader/contract/helper exemptions. Full unexcluded whitespace remains failed; actual scoped delivery gate is separate from Lean compilation. The source/public/Test/readers and original1822/postnative56 bindings remain unchanged.

Draft PR195 remains OPEN/unmerged, stacked on PR194 exact b08f8312259ae10032b6318060e18911532d4610; official app attachment recorded. The body update was actual PATCH with exact approved v4 title/body. Initial publication source head c251450fc36a0903c25592cad8de98471e079a2a is separate from the evidence-only final commit. Actual final local/remote/PR head is directly verified after final push, avoiding a fabricated self-referential future commit hash.

Seven private-tape/subordinate-information finite producer terminals accepted and delivered, not whole C1. Original16/null/kernel/completed-field/AE-factorization coverage audit/asymptotic/five source-module audits/C1C2/3-16/appendices remain required; GoalACTIVE. Main/live/merge/deploy/retirement not performed. Shared E:/ABRL/research project, active E:/ABRL/worktrees/research-online-book retained for the next C1 stochastic successfulness equivalence. All original failed syntax/whitespace/credential/reader/proof trials are preserved with separate repairs. Global credential configuration unchanged.
''')
stage_owned()
gate('source-scope-draft-delivery-v5',sys.executable,'-B','-X','utf8',RUN/'audit-owned-scope-v2.py','draft-delivery-v5')
gate('scoped-diff-draft-delivery-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-delivery-diff-v4.py','delivery-v5')
commit_owned('Record reviewed exact PR195 delivery and seven raw-byte stdout exceptions')
head = subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
accepted_fixed()
print('Actual clean delivery-evidence head:',head)
print('Use per-command gh credential helper for final push, then verify exact local/remote/PR heads without creating tracked audit files.')
