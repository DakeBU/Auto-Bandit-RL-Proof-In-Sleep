from common_accepted_v1 import *

accepted_fixed()
bindings=load(RUN/'accepted-metadata-bindings-v1.json')
for row in bindings['rows']:
    assert sha(row['path'])==row['current_sha256']
    assert sha(row['original_snapshot'])==row['original_sha256']
old=load(CONTRACT/'chapter-one-source-ledger-draft-v1.json')
new=load(CONTRACT/'chapter-one-source-ledger-accepted-v2.json')
assert len(new['maintext_items'])==16 and old['maintext_items']==new['maintext_items']
assert new['required_proof_leaf_total'] is None
for label in ['accepted-reviewer-trial','accepted-lifecycle','accepted-frontier-refresh',
              'accepted-frontier-shadow','accepted-memory-record','accepted-retrieval-record']:
    assert load(RUN/(label+'-v1-exit.json'))['exit_code']==0
shadow=load(RUN/'accepted-frontier-shadow-v1.log')
assert not shadow['mismatches'] and not shadow['would_mutate']
write(RUN/'actual-post-native-audit-v1.json',dict(status='actual-guard-and-native-gates-passed',
    exact_metadata_bindings_sha256=sha(RUN/'accepted-metadata-bindings-v1.json'),
    immutable_FINAL_inputs_rechecked=load(RUN/'FINAL-review-inputs-v1.json')['fixed_input_count'],
    native_overlay_sha256=sha(RUN/'native-acceptance-overlay-v1.json'),
    original16_source_objects_unchanged=True,required_proof_total_null=True,globalSGB_unchanged=True,
    distinct_suffix_review_pending=True,PR_delivery_pending=True,chapter_complete=False,goal_complete=False))
write(RUN/'post-native-review-packet-v1.md','''# Separate audit of actual permitted metadata and native operations

Reuse distinct /root/source_reviewer, requested Astra/medium. Original FINAL511 unchanged binding checks are re-run with exact immutable original snapshots for only the expressly permitted metadata mutations. This does not rerun or widen mathematical acceptance. Inspect common_accepted_v1.py, record-acceptance-v1.py, actual-post-native-audit-v1.json, accepted-metadata-bindings-v1.json and actual six CLI exit/log/output records. Ensure guards do not treat arbitrary suffixes or new arbitrary fields as permission: six manifest fields only, exact byte/SHA-bound own TASK status append, exact own journal entries. Current readers/public/canary/old source files are unchanged. New ledger keeps all original16 source objects and required proof total null. Global SGB unchanged; accepted progress4->0 is bounded to four frozen terminals only. Native memory/retrieval output is task-owned RUN evidence; no user's global memory edits or review invention. Scoped accepted frontier/shadow actual evidence is separate from global frontier and mathematical proof.

Check retained helper errors are disclosed rather than weakened assertions. Recheck actual independent original FINAL report/receipt hashes, manifest roundtrip fields, source scope and remaining requirements. Prospective title/body bytes remain exactly FINAL reviewed; publishing will occur only after this audit and scoped commits. Do not claim PR, merge, deployment, full source strategy representation or chapter/program completion happened.

Write ONLY post-native-review-v1.md and post-native-receipt-v1.json in this RUN. Include actor=/root/source_reviewer, verdict accepted|accepted-with-explicit-delta|rejected, report path/rawSHA, all indexed reviewed_files with raw hashes, fixed_input_count, before_after_raw_hashes_match/inputs_unchanged, required_blocking_repairs array, actual six manifest fields and every changed metadata row accepted or objected with exact scope, old source16/null/globalSGB invariant verdicts, prospective publication title/body SHA unchanged, remaining required scope. No other file edits/state promotions. Return hashes.
''')
paths=[RUN/'common_accepted_v1.py',RUN/'record-acceptance-v1.py',RUN/'prepare-post-native-review-v1.py',
    RUN/'actual-post-native-audit-v1.json',RUN/'accepted-metadata-bindings-v1.json',RUN/'post-native-review-packet-v1.md',
    RUN/'FINAL-review-inputs-v1.json',RUN/'FINAL-metadata-snapshots-v1.json',RUN/'final-reader-review-v1.md',RUN/'final-reader-receipt-v1.json',
    RUN/'proposed-publication-v1.json',RUN/'prospective-PR-title-v1.txt',RUN/'prospective-PR-body-v1.md',
    PUBLIC,CANARY,CONTRACT/'targets-v1.json',CONTRACT/'chapter-one-source-ledger-draft-v1.json',CONTRACT/'chapter-one-source-ledger-accepted-v2.json']
paths += [Path(row['path']) for row in bindings['rows']]+[Path(row['original_snapshot']) for row in bindings['rows']]
paths += [p for p in RUN.iterdir() if p.is_file() and (p.name.startswith('accepted-') or p.name.startswith('native-') or p.name.startswith('memory-digest-accepted') or p.name.startswith('retrieval-index-accepted') or p.name=='proof-obligations-accepted-v1.json')]
rows=[dict(path=p,sha256=sha(p)) for p in sorted({p.resolve().as_posix() for p in paths})]
write(RUN/'post-native-review-inputs-v1.json',dict(schema='abrl.review-inputs.v1',phase='post-native-bounded-metadata',
    fixed_input_count=len(rows),rows=rows,chapter_complete=False,goal_complete=False))
print('Actual native metadata audited; distinct post-native indexed inputs',len(rows),'; delivery pending.')
