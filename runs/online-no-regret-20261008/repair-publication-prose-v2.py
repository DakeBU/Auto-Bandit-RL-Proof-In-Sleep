from common_accepted_v1 import *
accepted_fixed()
r=load(RUN/'publication-receipt-v1.json')
assert r['verdict']=='rejected' and r['actor']['task']=='/root/source_reviewer'
assert sha(r['report'])==r['report_sha256']
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for row in load(RUN/'publication-review-inputs-v1.json')['rows']:
    assert sha(row['path'])==row['sha256']==reviewed[row['path']]
old=(RUN/'PR-body-v1.md').read_text(encoding='utf8')
before='A single fixed affine loss stream on `[0,1]`, with a feasible constant-zero causal learner, telescopes to signed regret and gives normalized regret `-1` on positive even horizons and `0` on odd horizons. It satisfies the upper condition and has no ordinary real limit.'
after='A single fixed affine loss stream on `[0,1]`, with a feasible constant-zero causal learner, telescopes to signed regret. Upper control holds for every feasible comparator. At the fixed feasible comparator **`u=1`**, normalized regret is `-1` on positive even horizons and `0` on odd horizons, so it has no ordinary real limit at that comparator.'
assert old.count(before)==1
write(RUN/'PR-body-v2.md',old.replace(before,after))
payload=load(RUN/'pr-payload-v1.json')
payload['body_file']=(RUN/'PR-body-v2.md').as_posix();payload['body_sha256']=sha(RUN/'PR-body-v2.md')
write(RUN/'pr-payload-v2.json',payload)
write(RUN/'publication-prose-repair-v2.json',dict(
    rejected_receipt_sha256=sha(RUN/'publication-receipt-v1.json'),
    original_PR_body_sha256=sha(RUN/'PR-body-v1.md'),corrected_PR_body_sha256=sha(RUN/'PR-body-v2.md'),
    exact_old_paragraph=before,exact_new_paragraph=after,
    repair='Only identify u=1 for the exact -1/0 values and nonconvergence; upper control remains for all feasible comparators.',
    prior_source_FINAL_unchanged=True,mathematical_or_reader_change=False,new_mathematical_progress=0,
    chapter_complete=False,goal_complete=False))
native('publication-prose-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(reason='Distinct publication reviewer rejected omitted fixed comparator u=1 in PR prose',evidence=(RUN/'publication-receipt-v1.json').as_posix(),source_terminals_unchanged=True)))
native('publication-prose-recandidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(reason='PR-body-v2 quantifies upper for all feasible comparators and exact obstruction at u=1',evidence=(RUN/'publication-prose-repair-v2.json').as_posix(),source_terminals_unchanged=True)))
publisher=(RUN/'publish-reviewed-v1.py').read_text(encoding='utf8')
publisher=publisher.replace("payload=load(RUN/'pr-payload-v1.json')", """receipt=load(RUN/'publication-receipt-v2.json')
assert receipt['actor']['task']=='/root/source_reviewer' and receipt['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not receipt['required_repairs'] and sha(receipt['report'])==receipt['report_sha256']
reviewed={x['path']:x['sha256'] for x in receipt['reviewed_files']}
for row in load(RUN/'publication-review-inputs-v2.json')['rows']:
    assert sha(row['path'])==row['sha256']==reviewed[row['path']]
write(RUN/'publication-repair-accepted-v2.json',dict(status='accepted prospective PR-prose repair',review_receipt_sha256=sha(RUN/'publication-receipt-v2.json'),original_FINAL_unchanged=True,source_subobligation='C1-NOREGRET',new_mathematical_progress=0,chapter_complete=False,goal_complete=False,PR_delivery_pending=True))
native('publication-prose-accepted-event-v2','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',json.dumps(dict(reason='Distinct corrected PR prose review accepted',evidence=(RUN/'publication-receipt-v2.json').as_posix(),accepted_source_scope_only='C1-NOREGRET',new_mathematical_progress=0,chapter_complete=False,goal_complete=False)))
gate('source-scope-pre-push-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','pre-push-v2')
gate('scoped-diff-pre-push-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v5.py','pre-push-v5')
payload=load(RUN/'pr-payload-v2.json')""")
write(RUN/'publish-reviewed-v2.py',publisher)
paths=[Path(x['path']) for x in load(RUN/'publication-review-inputs-v1.json')['rows']]
paths += [RUN/n for n in ['publication-review-inputs-v1.json','publication-review-v1.md','publication-receipt-v1.json',
 'PR-body-v2.md','pr-payload-v2.json','publication-prose-repair-v2.json','repair-publication-prose-v2.py',
 'publish-reviewed-v2.py','audit-committed-raw-v1.py','publication-prose-repair-event-v2.log','publication-prose-repair-event-v2-exit.json',
 'publication-prose-recandidate-event-v2.log','publication-prose-recandidate-event-v2-exit.json']]
rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in paths]
write(RUN/'publication-review-inputs-v2.json',dict(stage='exact u=1 PR prose repair',rows=rows,fixed_input_count=len(rows),
    source_FINAL_561_rows_unchanged=True,chapter_complete=False,goal_complete=False))
write(RUN/'publication-review-packet-v2.md','''# Mandatory distinct repair review of exact prospective PR prose

Reuse same source reviewer, GPT-6 Astra/medium. Preserve original rejected v1 receipt and accepted original FINAL561 rows. Rehash every v2 raw row; exact only PR sentence repair now distinguishes all-comparator upper from u=1 positive even -1/odd0 and nonconvergence. Other prose, mathematical statements/proofs/source/reader untouched. Review publisher v2 actual receipt guard and native repair->candidate->accepted metadata-only sequence, no new mathematical progress. Actual audit helper checks owned raw evidence/source/root/reader Git blobs. Inherited Asymptotic is EXPLICITLY two representations: original worktree1407bytes with33CRLFs, original Git prefix1374bytes with0CRLFs; current working snapshot+exact677byteaddition and current Git BASEblob+SAMEexactaddition each bound independently. Never normalize independent raw receipts, never claim these distinct raw hashes equal. Delivery is planned draft/OPENunmergedPR191stack, no main/merge/deploy/retirement.

Write ONLY publication-review-v2.md and publication-receipt-v2.json. Same schema as v1: actor.task, verdict, report/report_sha256,fixed_input_count, reviewed_files every row+manifest+report, required_repairs/required_mathematical_repairs/required_metadata_repairs. Before/after raw rehash. Explicit no chapter/Goal or delivered PR claim. No other edits.
''')
accepted_fixed()
print('Exact prospective u=1 prose repair',len(rows),'raw inputs frozen; distinct repair review pending.')
