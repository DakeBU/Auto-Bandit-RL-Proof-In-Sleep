from common_accepted_v1 import *
accepted_fixed()
names=['PR-body-v1.md','pr-payload-v1.json','proposed-publication-v1.md',
 'final-reader-inputs-v1.json','final-reader-review-v1.md','final-reader-receipt-v1.json',
 'accepted-decision-v1.json','accepted-binding-audit-v1.json','accepted-reader-discharge-v1.json',
 'native-acceptance-overlay-v1.json','integrated-gates-v3.json','registry-v1.json','pixel-review-v1.json',
 'prepare-publication-v1.py','publish-reviewed-v1.py','close-delivery-v1.py',
 'record-acceptance-v1.py','repair-acceptance-metadata-v2.py','acceptance-metadata-repair-v2.json','resume-acceptance-metadata-v2.py',
 'publication-live-refresh-v1.json','common_accepted_v1.py','common_integrated_v2.py',
 'diff-raw-evidence-exceptions-v5.json','check-scoped-diff-v5.py']
for label in ['accepted-reviewer-trial-v1','accepted-lifecycle-v1','accepted-frontier-shadow-v1',
 'contributor-publication-v1','scoped-diff-publication-v5','source-scope-publication-v1']:
    names += [label+'.log',label+'-exit.json']
paths=[RUN/n for n in names]+[PUBLIC,CANARY,MANIFEST]
rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in paths]
write(RUN/'publication-review-inputs-v1.json',dict(stage='prospective exact PR prose and scoped delivery',rows=rows,fixed_input_count=len(rows),
    source_FINAL_561_rows_unchanged=True, chapter_complete=False,goal_complete=False))
write(RUN/'publication-review-packet-v1.md','''# Distinct prospective publication review

Reuse /root/source_reviewer, requested GPT-6 Astra / medium. Original FINAL561 rows/receipt remains immutable; actual native acceptance followed and only the unexecuted metadata tail repaired a nonexistent source-card delta key. All six native commands already succeeded once and were not replayed. Verify exact PR-body-v1 and payload preserve source ordinary limit versus upper, actual finite convergence prerequisite, negative limits, one signed unbounded affine stream and no squared/bounded/mean nonconvergence claim, nine derived rather than printed results, decoder reconstruction versus reviewer acceptance, applicable actual gates, five failed/unwaived main modules and active total Goal. Generic bridges do not produce algorithms/minimizers. Confirm stacked OPENdraft/unmergedPR191 exacthead and per-command credential helper; no merge/deploy/retirement/global account/config change.

Read bounded actual native/metadata repair and proposed publish/close scripts. Future only owned acceptance/delivery metadata/journal updates use exact FINAL snapshots; mathematical/source/reader bytes remain frozen. Raw evidence/checker exception scope is exact9 immutable paths, not production waiver. Prospective audit script additions remain allowed evidence only and need no new math approval. Do not certify push or PR already happened.

Write ONLY publication-review-v1.md and publication-receipt-v1.json: actor.task=/root/source_reviewer; verdict accepted|accepted-with-explicit-delta|rejected; report/report_sha256; fixed_input_count; reviewed_files every input row+manifest+report; required_repairs/required_mathematical_repairs/required_metadata_repairs arrays; chapter_complete=false,goal_complete=false. Rehash before/after. Return raw hashes. No other edits or original FINAL rewrites.
''')
print('Publication exact prospective inputs',len(rows),'frozen; distinct prose review pending.')
