from publication_guard_v4 import *
fixed()
assert load(RUN / 'FINAL-review-v1.json')['package_verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert load(RUN / 'post-native-root-audit-v1.json')['all_other_FINAL_inputs_unchanged']
write(RUN / 'post-native-packet-v1.md', '''# Actual OWN native closure and prospective scoped PR delivery

Independently review actual trial/lifecycle8->0 for ONLY eight frozen derived proof obligations, two exact definitions separately inventoried and four full public canaries. Verify native-scoped CLI actual receipts, exact before RAW snapshot, appended trial/session entry, event sequence/parent/state update, unchanged journal/globalSGB and accepted shadow mismatches[]/would_mutatefalse. Definitions are not counted as eight printed source theorems. No full source/Algorithm15.8/T15.30, Chapter6/15, all8Chapter2forwards or whole16Goal closure.

Independently rehash all current inputs before/after; trace every permitted transition from FINAL-inputs against pre-native-exact-bytes and root audit. Only exact three contribution fields and OWN task/proof/retrieval suffixes plus OWN trial/session/state may change; frozen production/Test/root/reader/source/contracts/pins/graphs/current22pixels unchanged. Current final site applies to source in clean-candidate-site-binding-v3, not later evidence/delivery head. Retained failed renders/browsercollision/catalogue/stalecountplan and exact repairs immutable.

Review prospective PR-plan/body and deliver-v1/collect-actual-delivery-v1/final-evidence-delivery-v1 helpers: exact scoped stages, full diff0/no exceptions, RAW/CRLF snapshots, nonempty contributor bases, exact OPENdraftunmerged parentPR210/base41f1fb26915b3bf7f84035393080991c38aeba64. Per-command credential helper only/no force/global credential edits. Actual scopedcommit/push/newdraftPR/officialattachment and durable actual delivery review next; no merge/deploy/retirement/main/live/CI claim. All source X/interior valid-run/sharp fixed-variable including mandatory fixed main-text exercise remain REQUIRED/OPEN, GoalACTIVE.

Create-only post-native-review-v1.md/json with verdict/native_verdict/metadata_verdict/prospective_publication_prose_verdict/delivery_helper_verdict/required_repairs/report/report_sha256/input_manifest_sha256/FINAL_sha256/raw_input_checks. No publishing/input edits. Distinct reused staged automated role/requestedAstra-medium/history disclosed, not human/external/absolute-blind/runtime attestation.
''')
paths = {p for d in [RUN, CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update(Path(r['path']) for r in load(RUN / 'FINAL-inputs-v1.json')['rows'])
write(RUN / 'post-native-inputs-v1.json', dict(rows=rows(paths), FINAL_sha256=sha(RUN / 'FINAL-review-v1.json'),
    scope='Actual OWN bounded native and metadata closure; prospective scoped delivery only', actual_delivery_PENDING=True,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
print('Actual postnative and prospective delivery packet ready for distinct review.')
