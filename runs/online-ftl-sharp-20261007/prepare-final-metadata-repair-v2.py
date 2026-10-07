from common_v1 import *
fixed(proving=True, integrated=True)
old = load(RUN/'final-reader-receipt-v1.json')
assert old['verdict'] == 'rejected'
assert old['mathematical_verdict'] == old['current_reader_verdict'] == 'accepted-with-explicit-delta'
assert sha(old['report']) == old['report_sha256']
assert all(v['verdict'] == 'satisfied' for v in old['reader_requirement_verdicts'].values())
for x in load(RUN/'final-reader-inputs-v1.json')['rows']:
    assert sha(x['path']) == x['sha256'], x['path']
assert sha(PUBLIC) == load(RUN/'body-bindings-v1.json')['public_sha256']
assert sha(CANARY) == load(RUN/'body-bindings-v1.json')['canary_sha256']

delivery = (RUN/'prepare-delivery-v1.py').read_text(encoding='utf-8')
assert delivery.count("'registry-v1.json'") == 1
delivery = delivery.replace("'registry-v1.json'", "'registry-v2.json','final-metadata-repair-receipt-v2.json','final-metadata-repair-record-v2.json'")
delivery = delivery.replace('Original rejected metadata/enumeration review and all CLI/path/binding failures retained', 'Original rejected metadata/enumeration review, reader-scope pixel failure, FINAL M3 historical-registry binding rejection and all CLI/path/binding failures retained with separately reviewed versioned repairs')
write(RUN/'prepare-delivery-v2.py', delivery)

acceptance = (RUN/'record-acceptance-v1.py').read_text(encoding='utf-8')
acceptance = acceptance.replace('final-reader-receipt-v1.json', 'final-metadata-repair-receipt-v2.json').replace('final-reader-inputs-v1.json', 'final-metadata-repair-inputs-v2.json')
acceptance = acceptance.replace("audit=[]", """original_final=load(RUN/'final-reader-receipt-v1.json')
assert original_final['verdict']=='rejected' and original_final['mathematical_verdict']==original_final['current_reader_verdict']=='accepted-with-explicit-delta'
assert sha(original_final['report'])==original_final['report_sha256']
for x in load(RUN/'final-reader-inputs-v1.json')['rows']:assert sha(x['path'])==x['sha256'],x['path']
assert final['repair_of_receipt_sha256']==sha(RUN/'final-reader-receipt-v1.json')
assert final['metadata_repair_verdicts']['M3']['verdict']=='satisfied'
assert final['reader_requirement_verdicts']==original_final['reader_requirement_verdicts']
audit=[]""")
acceptance = acceptance.replace('all path/binding/CLI failures and actual repairs retained', 'reader-scope pixel failure, FINAL M3 delivery-registry rejection and all path/binding/CLI failures and separately reviewed repairs retained')
write(RUN/'record-acceptance-v2.py', acceptance)

publication = (RUN/'prepare-publication-v1.py').read_text(encoding='utf-8')
publication = publication.replace('Actual initial rejected metadata/enumeration CONTRACT and path/binding/fence/role invocation failures retained with separate actual repairs', 'Actual initial rejected metadata/enumeration CONTRACT, v1 initial-reader scope pixel failure, FINAL M3 historical-registry delivery-binding rejection and path/binding/fence/role invocation failures retained with separately reviewed versioned repairs; applicable registry-v2/site-v2 bind the delivered evidence')
write(RUN/'prepare-publication-v2.py', publication)
completion = (RUN/'complete-publication-v1.py').read_text(encoding='utf-8')
assert completion.count('prepare-publication-v1.py') == 1
write(RUN/'complete-publication-v2.py', completion.replace('prepare-publication-v1.py', 'prepare-publication-v2.py'))

write(RUN/'final-metadata-repair-record-v2.json', dict(
    repair_id='M3', original_rejected_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),
    original_report_sha256=old['report_sha256'], original_fixed_rows=557,
    mathematical_version=1, mathematical_statements_and_bodies_unchanged=True,
    original_v1_helpers_and_reviews_retained=True,
    applicable_registry=dict(path=(RUN/'registry-v2.json').as_posix(), sha256=sha(RUN/'registry-v2.json'), source_commit=load(RUN/'registry-v2.json')['source_commit']),
    historical_registry=dict(path=(RUN/'registry-v1.json').as_posix(), sha256=sha(RUN/'registry-v1.json'), role='Historical v1 site only; not the applicable delivery registry'),
    effective_helpers=[dict(path=(RUN/p).as_posix(), sha256=sha(RUN/p)) for p in ['record-acceptance-v2.py','prepare-publication-v2.py','complete-publication-v2.py','prepare-delivery-v2.py']],
    source_package_accepted=False, chapter_complete=False, goal_complete=False))
native('final-metadata-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,repair_id='M3',metadata_repair=(RUN/'final-metadata-repair-record-v2.json').as_posix(),mathematical_statements_and_bodies_unchanged=True,chapter_complete=False,goal_complete=False)))
native('final-metadata-candidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,metadata_repair=(RUN/'final-metadata-repair-record-v2.json').as_posix(),distinct_repair_review_pending=True,chapter_complete=False,goal_complete=False)))
write(RUN/'final-metadata-repair-packet-v2.md', '''# Separate FINAL metadata repair M3

Required reused /root/source_reviewer, requested GPT-6 Astra / medium. Prior staged history disclosed; no blind, human, external or runtime-model attestation. Preserve original rejected FINAL, report and all 557 frozen inputs; math and current reader already accepted-with-explicit-delta, all original R1–R8 satisfied. Your two predicted hash-helper concerns were tested and withdrawn, not repairs.

Rehash every final-metadata-repair-inputs-v2 fixed row, all original 557 rows and every original FINAL reviewed row; examine actual versioned helper diff. Only M3 is repaired: prepare-delivery-v2 binds applicable registry-v2, preserves registry-v1 as historical, includes original rejection and separate repair evidence. record-acceptance-v2 consumes the real repair receipt, checks original rejection/raw inputs and unchanged R1–R8, requires M3 satisfied, and retains actual CONTRACT/BODY audits. Publication-v2 explains the actual reader and M3 failures; completion-v2 routes publication-v2. Old v1 helpers remain unchanged and unused for acceptance/delivery. Two public proofs, six validation proofs, current reader inputs, source and statements remain frozen. No repeated kernel/site/pixel gate is claimed or needed for a metadata-only helper version; existing applicable evidence remains exact. Native acceptance/push/PR/app attachment are future actions, not done. Chapters/Goal/main/live boundaries unchanged.

Write ONLY final-metadata-repair-review-v2.md and final-metadata-repair-receipt-v2.json in this RUN. Receipt actor.task=/root/source_reviewer, verdict accepted|rejected|accepted-with-explicit-delta; report/report_sha256; reviewed_files EVERY fixed row plus actual report, fixed_input_count; repair_of_receipt_sha256 EXACT original FINAL receipt hash; metadata_repair_verdicts.M3 {verdict:satisfied|unsatisfied,evidence:...}; reader_requirement_verdicts EXACT SAME original FINAL R1–R8 object (no rewritten requirements), with rationale that unchanged original current-reader/math bindings are preserved. Arrays required_repairs/required_mathematical_repairs/required_metadata_repairs/required_blocking_reader_repairs. Do not attest later native acceptance/publication or whole chapter/Goal completion. Return real report/receipt SHA.
''')
# No RUN log wrapper: freezing its own parent output would invalidate a binding.
paths = [x['path'] for x in load(RUN/'final-reader-inputs-v1.json')['rows']]
paths += [x['path'] for x in old['reviewed_files']]
paths += [p.as_posix() for p in sorted(RUN.rglob('*')) if p.is_file()]
paths = list(dict.fromkeys(paths))
write(RUN/'final-metadata-repair-inputs-v2.json', dict(stage='FINAL-M3-repair', rows=[dict(path=p,sha256=sha(p)) for p in paths], fixed_input_count=len(paths), original_FINAL_fixed_rows=557, original_FINAL_rejected_retained=True, mathematical_version=1, original_R1_R8_unchanged=True, chapter_complete=False, goal_complete=False))
fixed(proving=True, integrated=True)
print('Separate M3 repair frozen:', len(paths), 'raw input bindings; review pending.')
