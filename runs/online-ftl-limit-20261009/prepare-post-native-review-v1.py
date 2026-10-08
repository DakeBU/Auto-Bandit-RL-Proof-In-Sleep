from common_accepted_v2 import *

accepted_fixed()
assert load(RUN/'proof-obligations-accepted-v1.json')['derived_obligations_after']==0
for label in ['accepted-reviewer-trial-v1','accepted-lifecycle-v1','accepted-frontier-refresh-v1',
    'accepted-frontier-shadow-v1','accepted-memory-record-v1','accepted-retrieval-record-v1']:
    assert load(RUN/(label+'-exit.json'))['actual_exit']==0
for label,base in [('contributor-accepted-stack-v1',BASE),('contributor-accepted-main-v1','origin/main')]:
    gate(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    text=(RUN/(label+'.log')).read_text(encoding='utf8')
    assert 'Contributor contract passed.' in text and ' - covered: '+PUBLIC.relative_to(ROOT).as_posix() in text
indexed={}
def add(p):
    p=Path(p).resolve();assert p.is_file()
    indexed[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for x in load(RUN/'FINAL-review-inputs-v2.json')['rows']:add(x['path'])
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:add(p)
for p in [CONTRIBUTION,ROOT/'runs/lifecycle_sessions.jsonl']+APPEND_METADATA:add(p)
write(RUN/'post-native-review-inputs-v1.json',dict(rows=sorted(indexed.values(),key=lambda x:x['path']),
    fixed_input_count=len(indexed),exact_metadata_bindings=load(RUN/'accepted-metadata-bindings-v1.json'),
    actual_new_production_proofs=5,original_source_objects=16,unknown_required_proof_total=None,
    allowed_outputs=['post-native-review-v1.md','post-native-receipt-v1.json'],chapter_complete=False,goal_complete=False))
write(RUN/'post-native-review-packet-v1.md',
    'Independent post-native audit. Hash EVERY current indexed RAW input before/after. Verify final-reader-v2 favorable and original FINAL-v1 rejected retained with M1 explicit nonempty HEAD coverage repair. Original five proof/canary/header/pin/root/Test/reader/site bytes unchanged. Audit accepted-metadata-bindings-v1 exact six own-manifest field changes, three identical append-only task suffixes and only this TASK lifecycle accepted suffix against original FINAL snapshots; no old source record/method/version weakening.\n\n'
    'Inspect actual native reviewer record in NEW accepted-scoped-trials-v1.jsonl (six original compiled attempts plus exactly one accepted reviewer5->0), preserve original BODY-bound trials.jsonl and global trials. Actual lifecycle accepted/frontier-refresh/frontier-shadow/memory-record/retrieval-record all real0, owned output only; globalSGB frontier/lifecycle_memory/six retrieval indexes unchanged. New memory/retrieval references exactly five actual public targets and canary build. Native acceptance is only five derived hinges, not source/chapter/Goal completion. Accepted ledger preserves original16/null/historical overlays and required concrete boundedoscillation/all-comparatorconverse/otherC1C2/C3-16/appendices. No main/live change.\n\n'
    'Check actual after-metadata contributor logs: both bases explicitly cover new public module (no N/A). Whole root/Tests/harness-v2/axioms/fences/local site and twelve actual images remain applicable by exact source hashes; no rerun or fresh pixel claim implied. Four retained RAW compiler-log whitespace exceptions are exact SHA-bound; production/Test/readers/contracts have none. PR title/body exact prospective-v1 and stacked PR200 exact BASE still open draft/unmerged. Scope commit/push/create draft+official app attachment only, no force/merge/deploy/retire. Reject any unsupported claim.\n\n'
    'Write ONLY post-native-review-v1.md and post-native-receipt-v1.json: verdict, fixed_input_count, reviewed_files(include index hash), raw_input_checks(path,before_sha256,after_sha256,unchanged), inputs_unchanged, report_sha256, required_blocking_repairs, authorized_delivery_scope(exact reviewed PR title/body hashes, branch/base and scoped commit/push/draft/app attachment/no merge or deploy if favorable). Distinct reused automated reviewer requested Astra/medium, no human/external/runtime attestation. No input/native/git/site mutations.\n')
print('Post-native fixed current RAW count:',len(indexed),flush=True)
