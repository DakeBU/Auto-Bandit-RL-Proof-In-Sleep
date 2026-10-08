from common_body_v1 import *

fixed_integrated()
frozen = RUN/'common_canary_v1.py'
row = next(x for x in load(RUN/'body-review-inputs-v1.json')['rows'] if x['path'] == frozen.as_posix())
assert sha(frozen) == row['sha256']
old = frozen.read_bytes()
new = old.rstrip(b'\r\n')+b'\n'
assert old == new+b'\n'
write(RUN/'helper-eof-original-v1.py.raw',old)
write(RUN/'helper-eof-proposed-v1.py.raw',new)
mutable = RUN/'commit_owned_v1.py'
original = mutable.read_bytes()
assert all(x['path'] != mutable.as_posix() for x in load(RUN/'body-review-inputs-v1.json')['rows'])
write(RUN/'commit-helper-before-eof-v1.py.raw',original)
mutable.write_bytes(original.rstrip(b'\r\n')+b'\n')
write(RUN/'helper-eof-repair-proposal-v1.json',dict(
    exact_mutable_path=frozen.as_posix(),old_sha256=sha(frozen),
    proposed_new_sha256=sha(RUN/'helper-eof-proposed-v1.py.raw'),
    permitted_diff='Remove exactly one final LF, leaving exactly one LF after final code line; no other bytes',
    old_snapshot=(RUN/'helper-eof-original-v1.py.raw').as_posix(),
    proposed_snapshot=(RUN/'helper-eof-proposed-v1.py.raw').as_posix(),
    original_body350_report_and_receipt_remain_immutable=True,
    guard_followup='Versioned post-BODY guard may allow exactly this separately reviewed old/new RAW transition; original350 before/after claim remains historical',
    production_canary_statements_proofs_and_pins_unchanged=True,
    raw_logs_retained_without_code_whitespace_exemptions=True,
    candidate_commit_failed_before_commit=True,head_unchanged=BASE,chapter_complete=False,goal_complete=False))
write(RUN/'helper-eof-review-packet-v1.md',
    'Separate narrow formatting repair review after favorable BODY350. Verify helper-eof-review-inputs-v1.json actual RAW before/after. Original frozen common_canary_v1.py has exactly two final LF; proposal removes exactly ONE final LF, no code/math/guard behavior change. Every production/Test/pin byte still BODY bound. Original BODY350 remains a truthful historical before/after snapshot, never rewrite it. Original helper byte snapshot and failed full Git whitespace diagnostics retained. The newly authored post-BODY commit_owned_v1.py (not in350) independently had an EOF blank and was corrected with raw original retained. Approve only exact frozen helper old/new transition and a versioned post-BODY guard that checks this repair receipt/report plus original snapshot and exact new SHA when the350 loop sees that one changed file. No terminal/production/Test/pin/reader/global state changes, no code exemption for whitespace gate; actual full Git check failure2 retained. Source-body, combined root9102/Tests9264/fullharness472tests7skips passed separately. No rerun or broader scientific/Goal acceptance. Write ONLY helper-eof-review-v1.md and helper-eof-receipt-v1.json, actual RAWcount before/after, reportSHA/verdict/blockers/precise permitted change. Requested Astra/medium, reused distinct automated actor, no human/external/runtime attestation.\n')
files = [frozen,PUBLIC,CANARY]+[ROOT/n for n in ['lean-toolchain','lakefile.lean','lake-manifest.json']]
files += [RUN/n for n in ['helper-eof-original-v1.py.raw','helper-eof-proposed-v1.py.raw',
    'commit-helper-before-eof-v1.py.raw','commit_owned_v1.py','helper-eof-repair-proposal-v1.json',
    'helper-eof-review-packet-v1.md','prepare-helper-eof-repair-v1.py',
    'public-body-review-v1.md','public-body-receipt-v1.json','body-review-inputs-v1.json',
    'body-review-authority-v1.json','body-bindings-v1.json','body-future-integration-scope-v1.json',
    'candidate-full-diff-v1.log','candidate-full-diff-v1-exit.json','combined-gates-v1.json']]
rows = raw_index(files)
write(RUN/'helper-eof-review-inputs-v1.json',dict(rows=rows,fixed_input_count=len(rows),
    original_body_fixed_input_count=350,goal_complete=False))
fixed_integrated()
print('Separate EOF-only frozen-helper repair proposal',len(rows),'RAW inputs; target helper still unchanged.',flush=True)
