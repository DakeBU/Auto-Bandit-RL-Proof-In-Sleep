from common_accepted_v2 import *

accepted_fixed()
assert load(RUN/'native-acceptance-overlay-v2.json')['status'].startswith('actual native commands passed')
old={x['path']:x['sha256'] for x in load(RUN/'FINAL-review-inputs-v2.json')['rows']}
rows={}
def add(p):
    p=Path(p).resolve();rows[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for folder in [RUN,ROOT/CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts and p.resolve().as_posix() not in old:add(p)
for r in load(RUN/'accepted-metadata-bindings-v2.json')['rows']:
    add(r['path']);add(r['original_snapshot'])
for p in MODULES+READERS+[CANARY,Path('Tests.lean'),Path('BanditRLProof.lean'),Path('lean-toolchain'),Path('lakefile.lean'),Path('lake-manifest.json'),Path('runs/active_frontier.json')]:add(p)
index=dict(phase='Exact executed own native suffix and guard audit, not a new source/math acceptance',
    rows=sorted(rows.values(),key=lambda x:x['path']),approved_FINAL_receipt_sha256=sha(RUN/'final-reader-receipt-v2.json'),
    five_source_audit_obligations_before=5,five_source_audit_obligations_after=0,new_production_proofs=0,
    source16_and_null_total_preserved=True,reader_capture_candidate_status_preserved=True,
    chapter_complete=False,goal_complete=False,PR_delivery_completed=False)
write(RUN/'post-native-review-inputs-v2.json',index)
write(RUN/'post-native-review-packet-v2.md','''Audit the actual executed native metadata, not just an intended suffix. First/last RAW-check this index and the immutable FINAL504 inputs with only approved exact mutable snapshots/resolutions. Inspect actual reviewer accepted trial, lifecycle accepted event, scoped shadow, source_fact memory record and retrieval record. They close only five SOURCE-AUDIT obligations5->0 and create zero production proofs; original sixteen source objects/null proof total and full stochastic kernels/completed-information/AE-factorization/chapter obligations remain required. Verify all actual manifest changes are exactly six permitted fields, all four own task suffixes match recorded exact bytes, journal rows belong to this task/session, SGB/public proofs/canary/pins/readers unchanged, reader F1 stays corrected and no previous receipt/rejected finding/old input/image was rewritten. Inspect newly created active guards and acceptance helpers, plus unchanged prospective title/body v2, before allowing their scoped draft delivery. No publication has happened; no human/external review/runtime attestation. Return post-native-review-v2.md / post-native-receipt-v2.json with exact RAW before/after, verdict, required_blocking_repairs, explicit metadata/mathematical/future-publication boundary and own parsed findings. Do not change any indexed input or execute publication. Whole Goal ACTIVE.
''')
print('Post-native fixed RAW input count',len(index['rows']))
