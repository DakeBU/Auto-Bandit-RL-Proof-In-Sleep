from common_body_v1 import *
integrated_fixed()
old=load(RUN/'FINAL-review-inputs-v1.json')
assert all(sha(x['path'])==x['sha256'] for x in old['rows'])
repair=load(RUN/'contributor-repair-gates-v2.json')
assert repair['both_nonempty_bases_cover_new_production_module']
indexed={x['path']:x for x in old['rows']}
for p in RUN.rglob('*'):
    if p.is_file() and '__pycache__' not in p.parts:
        indexed[p.resolve().as_posix()]=dict(path=p.resolve().as_posix(),sha256=sha(p))
write(RUN/'FINAL-review-inputs-v2.json',dict(rows=sorted(indexed.values(),key=lambda x:x['path']),
    fixed_input_count=len(indexed),original414_unchanged=True,
    original_final_rejected=True,repair=repair,mathematical_contract_version=1,
    original_R1_R7=load(CONTRACT/'reader-requirements-v1.json'),
    future_metadata_scope=load(RUN/'FINAL-future-metadata-scope-v1.json'),
    allowed_outputs=['final-reader-review-v2.md','final-reader-receipt-v2.json'],chapter_complete=False,goal_complete=False))
write(RUN/'FINAL-review-packet-v2.md',
    'Separate FINAL M1 repair review. Original FINAL414/rejected receipt remains immutable; verify all414 current RAW bytes still equal original input hashes and independently hash EVERY current v2 indexed input before/after. Original five types/bodies/twelve canaries/readers/12original images/pins/site and reviewer R1-R7 findings unchanged. Original source/reader pixel inspection may be reused only with explicit current same-SHA confirmation; do not claim a fresh view if not done.\n\n'
    'Inspect FINAL-M1-repair-v2.json and actual candidate HEAD703b901fecd725e63e6613f5a6e18a5ea50b13a9 logs candidate-contributor-stack-v2 and main-v2. Both MUST be nonempty, passed and explicitly cover BanditRLProof/OnlineFTLLimitSemantics.lean. Old precommit stackN/A and main missing module are failed evidence, not successes. Candidate-other-gates-v1 historical boolean is not operative contributor evidence; operative repair-gates-v2 references exact new logs. Original gate0 summary was incorrect for this package and is superseded explicitly. No source/theorem/pin/harness weakening.\n\n'
    'Inspect new common_accepted_v2.py and record-acceptance-v2.py as future scoped metadata/native operations. Original BODY-bound trials.jsonl remains immutable; native reviewer adds one record to a NEW owned accepted-scoped-trials file copied from six actual attempts, no global trials changes. Metadata scope remains original exact six own-manifest fields/three own task appendices/own lifecycle suffix, accepted ledger keeps16/null and boundedoscillation/allcomparatorconverse REQUIRED, globalSGB/retrieval unchanged. Native actions must wait for this favorable receipt and separate post-native audit. Verify original prospective PR title/body now supported by actual HEAD contributor gates; no merge/deploy or Goal closure.\n\n'
    'Retain all previous mathematical/R1-R7/pixel conclusions only if justified by unchanged inputs. Search anew for unsupported gate/coverage/repair/current-state assertions. Outputs ONLY final-reader-review-v2.md and final-reader-receipt-v2.json with same full schema as v1: current fixed_input_count/reviewed_files including v2index/raw_input_checks/inputs_unchanged/report_sha256/verdict/required_blocking_repairs; exact R1-R7 requirement/verdict/evidence; actual_pixel_review all12(path,sha256,actually_viewed, reuse disclosure if appropriate); permitted_future_metadata exactly FINAL-future-metadata-scope-v1.json if favorable. Requested Astra/medium; distinct reused automated actor, no human/external/runtime attestation.\n')
print('Current repair FINAL RAW count:',len(indexed),flush=True)
