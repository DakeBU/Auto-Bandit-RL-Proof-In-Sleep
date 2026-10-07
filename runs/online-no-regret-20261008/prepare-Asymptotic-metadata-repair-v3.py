from common_integrated_v1 import *
fixed_integrated();assert load(RUN/'contributor-committed-exact-base-v2-exit.json')['exit_code']==1
old=Path('BanditRLProof/OnlineLearningAsymptotic.lean');snapshot=RUN/'snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw'
assert old.read_bytes()==snapshot.read_bytes()
addition='''

/-!
Source boundary: Orabona, arXiv:1912.13213v10 (21 June 2026), printed page 2 /
PDF page 14, and Theorem 1.3 on printed page 4 / PDF page 16.

`meanPredict_noRegret` is a producer of the shared comparator-wise eventual
upper-epsilon property. It uses the actual strict-past mean predictor, its
regret bound and the same empirical-mean loss minimum. It does not prove
existence of an ordinary real limit of normalized regret. The printed ordinary
limit display and this upper interpretation are separately reconciled by
`OnlineNoRegretSemantics`; equivalence retains actual per-comparator finite
real convergence. Negative signed regret and negative limits are allowed.
-/
'''
write(RUN/'Asymptotic-source-comment-addition-v3.txt',addition)
write(RUN/'Asymptotic-source-qualified-proposal-v3.lean',old.read_bytes()+addition.encode('utf8'))
write(RUN/'Asymptotic-metadata-repair-proposal-v3.json',dict(actual_failed_gate='contributor-committed-exact-base-v2',reason='Existing Asymptotic production path appears in new affected_files but is unchanged relative to exact stacked base; gate correctly rejects it.',proposed_change='Append source-qualified ordinary-limit boundary comment only. All existing bytes remain a prefix, theorem bodies/types and all definitions/imports unchanged; no source theorem scope change.',live_path=old.as_posix(),original_sha256=sha(old),original_snapshot=snapshot.as_posix(),proposed_path=(RUN/'Asymptotic-source-qualified-proposal-v3.lean').as_posix(),proposed_sha256=sha(RUN/'Asymptotic-source-qualified-proposal-v3.lean'),addition_path=(RUN/'Asymptotic-source-comment-addition-v3.txt').as_posix(),addition_sha256=sha(RUN/'Asymptotic-source-comment-addition-v3.txt'),approved_baseline_exception_pending=True,existing73_and371_original_bindings_must_resolve_to_exact_original_snapshot=True,all_nine_source_targets_unchanged=True,new_public_proof_count=9,new_definition_count=3,chapter_complete=False,goal_complete=False))
write(RUN/'Asymptotic-metadata-repair-packet-v3.md','''# Separate concrete source metadata repair review

Reuse /root/source_reviewer requested Astra/medium and disclosed history. Actual committed contributor gate correctly rejected unchanged affected Asymptotic path. Review ONLY the proposed exact trailing source comment in Asymptotic-source-qualified-proposal-v3.lean; old live file remains unchanged pending review. Check proposed bytes equal original complete byte prefix plus exact comment addition. Re-read existing meanPredict_noRegret body and source printed2/PDF14 ordinary lim paragraph plus printed4/PDF16 Theorem1.3. Comment clarifies actual strict-past mean/the same best empirical-mean losses/upper-epsilon producer and explicitly no ordinary convergence. Original twelve neutral actual proposition identities include that old theorem; no new mathematical goal/type/definition proof change is proposed. This is a genuine attribution/boundary improvement to the shared source module, not a performance proof or metadata-only waiver of contributor rules.

If accepted, authorize ONLY exact source-comment append as an explicit baseline resolution: original frozen Asymptotic bytes in draft-baseline-v1, original73 CONTRACT and371 BODY inputs continue bound by immutable snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw; live file must have exact proposed hash and original prefix. All other old baselines, PUBLIC/CANARY/rawheaders/definitions/R1–R8 unchanged. Future versioned integration verifier must explicitly distinguish this exception, never overwrite original helper/frozen receipt or normalize hashes. Combined root/Tests/fullharness were for old commentless bytes; rerun applicable combined gates after comment addition before claiming new site verified. Six affected production paths are then actually changed against exactBASE; one existing Asymptotic source qualification, five other main-relative modules remain required. Reject if comment overclaims source equality, ordinary limit, causal general algorithm/minimum or changes any body/type.

Write ONLY Asymptotic-metadata-repair-review-v3.md and Asymptotic-metadata-repair-receipt-v3.json. Receipt actor.task=/root/source_reviewer; verdict accepted|accepted-with-explicit-delta|rejected; report/report_sha256; all fixed input rows+manifest+report, fixed_input_count; allowed_source_append live_path/original_sha256/proposed_sha256/addition_sha256/exact_prefix_preserved; required_repairs/mathematical/metadata arrays; original required_reader_corrections EXACT from stabilized-contract-v1. BODY nine proofs remains accepted; no FINAL/integrated/package/chapter/Goal acceptance. Rehash all before/after. No other edits.
''')
paths=[old,PDF,PUBLIC,CANARY,CONTRACT/'targets-v1.json',CONTRACT/'public-context-v1.lean',RUN/'stabilized-contract-v1.json',RUN/'source-contract-inputs-v1.json',RUN/'source-contract-receipt-v1.json',RUN/'source-repair-receipt-v1.json',RUN/'body-review-inputs-v1.json',RUN/'public-body-receipt-v1.json',RUN/'public-body-review-v1.md',RUN/'draft-baseline-v1.json',snapshot,RUN/'body-bindings-v1.json',RUN/'leaves/all-exact-types-v1.lean',RUN/'all-exact-types-v1-exit.json',RUN/'source-pdf14-v1.png',RUN/'source-pdf14-v1.txt',Path('runs/online-log-lower-20261008/source-pdf16-v1.png'),Path('runs/online-log-lower-20261008/source-pdf16-v1.txt'),MANIFEST,RUN/'contributor-committed-exact-base-v2.log',RUN/'contributor-committed-exact-base-v2-exit.json']
paths += [RUN/n for n in ['Asymptotic-source-comment-addition-v3.txt','Asymptotic-source-qualified-proposal-v3.lean','Asymptotic-metadata-repair-proposal-v3.json','Asymptotic-metadata-repair-packet-v3.md']]
rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in paths]
write(RUN/'Asymptotic-metadata-repair-inputs-v3.json',dict(stage='Concrete source-comment metadata repair',rows=rows,fixed_input_count=len(rows),source_or_terminal_changed=False,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed_integrated();print('Concrete append-only source clarification frozen',len(rows),'rows; distinct repair review required.')
