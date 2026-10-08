from common_proving_v1 import *
import re
contract_bindings_fixed()
a=load(RUN/'actual-kernel-value-audit-v1.json')
assert a['canary_sha256']==sha(CANARY) and not a['sorryAx']
assert a['public_files_sha256']=={p.as_posix():sha(p) for p in MODULES}
rows=load(CONTRACT/'targets-v2.json')['targets']
for version in [1,2]:
    native('canary-failed-trial-v'+str(version),'trial-log','--task',TASK,'--role','lower',
        '--kind','build','--status','failed','--run-id',RUN.name,'--lean',CANARY,
        '--attempt-id','CORE-CANARY-V'+str(version),'--progress-class','diagnostic',
        '--verifier-evidence',RUN/('canary-focused-build-v'+str(version)+'-exit.json'),
        '--error-signature','test-only normalization/API mismatch; headers unchanged',
        '--notes','Actual failed focused canary build retained, same frozen public targets and test conclusions; no source audit closed or production proof growth.')
args=['trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
    '--run-id',RUN.name,'--lean',CANARY,'--attempt-id','CORE-CANARY-V3','--progress-class','retrieval-reuse',
    '--obligations-before','5','--obligations-after','5','--verifier-evidence',RUN/'actual-kernel-value-audit-v1.json',
    '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--notes',
    'Actual twelve reused public proof values and whole-type identities, original seven Foundation canaries, clipped infinite-IID and non-identical-law test canaries; standard axioms and actual VALUE deps. Five source audits still pending BODY/combined/readers/FINAL/native; zero new production proofs.']
for r in rows: args+=['--reused-declaration',r['name']]
native('canary-compiled-trial-v3',*args)
write(RUN/'body-bindings-v1.json',dict(public_files_sha256=a['public_files_sha256'],canary_sha256=sha(CANARY),
    frozen_targets_sha256=sha(CONTRACT/'targets-v2.json'),kernel_value_audit_sha256=sha(RUN/'actual-kernel-value-audit-v1.json'),
    source_review_receipt_sha256=RECEIPT_SHA,exact_comment_plan_sha256=sha(CONTRACT/'exact-comment-plan-v1.json'),
    twelve_original_headers_proof_bytes_unchanged=True,new_proofs=0,source_audits_pending=5,
    BODY_accepted=False,chapter_complete=False,goal_complete=False))
status=('Actual five old core modules and own canary focused build pass. Twelve complete public proofVALUE instantiations/wholeProp identities and complete meanPredict Def identity; '
    'actual compiled TYPE/VALUE graph and direct required canary/public consumer pairs, standard axioms only. Original seven Foundation proofs reused unchanged. '
    'Test-only globally clipped infinite fair IID coordinates remain independent/same-law, AE equal to original real coordinates, mean1/2/variance1/4. Off-null path2 modifies to1 explicitly. '
    'Outside legal comparator2 gives loss5/2; independent genuinely random coordinate pair gives loss1/2; actual unknown-law strict-past initial-half mean gives two-round excess1/4. '
    'Global all-tuple clipped last-policy produces actual history independence/loss>=currentvariance and one-round loss1/2. Independent heterogenous process first coordinate constant0 versus later variance1/4 proves non-same-law yet current variance lower. '
    'Positive scalar normalized identity and T0 discrepancy explicit. No convergence claim or arbitrary-strategy representation. '
    'Two canary failed builds preserved; four proof-only normalization/API fixes, no conclusion/header change. All five production original bytes outside exact reviewed comment inserts unchanged. '
    'Twelve existing proofs, zero new production proofs; five source-audit obligations pending BODY/combined/FINAL/native. Historical Foundation source revalidation remains preserved. '
    'Original16 C1 source objects/null total/full universal-model/completion/AE-factorization/C1/C2/C3-16/appendices remain required; Goal active, PR196 stacked/unmerged/main/live unchanged.')
write(RUN/'33_lower-body-candidate-v1.md',status)
write(RUN/'memory-digest-candidate-v1.md',status)
write(RUN/'proof-obligations-candidate-v1.json',dict(contract_version=2,existing_public_proofs=12,new_public_proofs=0,
    old_source_audit_obligations=5,accepted_source_audits=0,
    focused_and_kernel_and_VALUE='actual passed',BODY='pending',remaining_required_gates=[
    'BODY actual canary/comments','combinedroot/Tests/fullharness','stacked AND main contributor',
    'ownshadow/globalSGBunchanged','oldregistry/reader/currentsiteDOM/pixels','FINAL','native acceptance','scoped draft PR delivery'],
    original_source_objects=16,required_C1proof_total=None,chapter_complete=False,goal_complete=False))
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate',
    '--payload-json',json.dumps(dict(contract_version=2,run_id=RUN.name,body_bindings=(RUN/'body-bindings-v1.json').as_posix(),
    existing_proofs=12,new_proofs=0,source_audits_pending=5,chapter_complete=False,goal_complete=False)))
write(RUN/'body-future-integration-scope-v1.json',dict(
    immutable_math= [p.as_posix() for p in MODULES]+[CANARY.as_posix()],
    allowed_future_changes=dict(Tests='append exactly import Tests.OnlineLearningCoreAuditCanary; preserve original bytes',
    public_root='no change, old five already public',
    readers='one own source card; correct only existing lemma_1_2/iid_meanPredict_excess notes; append TEN missing notes; own boundary additions, preserve every other old card/note/ID/link/status',
    manifest='own schema2 only, covers exact five reviewed changed comment paths plus owned reader files; no blanket unchanged file coverage',
    native='own exactTASK rows/metadata/frontier/trials only; append-only history and globalSGB preserved',
    own_contract_RUN='new exact evidence/status records only; preserve frozen indexed files and raw snapshots'),
    receipt_bound_mutation_resolution='stabilized-contract-v2.json + approved-comment-insertions-v1.json + immutable nine raw baselines; no claim live changed source files equal old hashes',
    twelve_proof_headers_and_bodies_immutable=True,original16_null_universal_required=True,chapter_complete=False,goal_complete=False))
write(RUN/'body-review-packet-v1.md',
    'Distinct anti-anchored BODY audit after CONTRACT stabilization v2. Read actual twelve old public proof bodies and exact approved comments, own new canary actual proofs/definitions and all v1/v2/v3 attempt values/errors, current whole-type/publicVALUE/kernel/compiled TYPE_VALUE graph and twelve fences. '
    'Source original PDF13-16 / actual pixels, restricted blind report and CONTRACT accepted-with-explicit-delta are bound. '
    'All raw old receipt-bound mutable live inputs have immutable baseline snapshots in stabilized-contract-v2; current public whole-file hashes legitimately changed ONLY by reviewed comment inserts. Guard verifies every original proof byte/header and every current field; do not claim original whole-files unchanged. '
    'Check actual nondegenerate fair infinite IID, globally bounded clipping with explicit non-pointwise identity offnull, all-real comparator2, actual meanPredict excess1/4, true composed all-tuple bounded strict-past history loss1/2, independent heterogeneous non-same-law current-variance lower, T0 discrepancy. No new production proof/wrapper; new counts only tests, five source audit obligations still pending. '
    'Retain exact R1-R8 verbatim; assess body-future-integration-scope-v1 precise permitted future reader/Testroot/manifest/native changes. Future full root/Tests/harness, contributor stacked ANDoriginmain, registry/site/pixels/FINAL/native/delivery are NOT accepted at BODY. '
    'Write ONLY public-body-review-v1.md/public-body-receipt-v1.json here. Hash every current indexed row pre/post, state actual count, reportSHA, seven slots/deltas for all12 and actual fixture/proof checks, required_blocking_repairs, verdict accepted|accepted-with-explicit-delta|rejected. '
    'Do not edit inputs or waive full16/null/universalmodel/C1/C2/C3-16/appendix required obligations. Requested Astra/medium, reused distinct automated history disclosed; no absolute blind/human/external/runtime attestation. User authorizes scoped draft delivery, not merge/deploy.')
paths=[Path(x['path']) for x in load(RUN/'source-contract-review-inputs-v1.json')['rows']]
paths += [CANARY] + list(RUN.glob('*.json')) + list(RUN.glob('*.md')) + list(RUN.glob('*.lean'))
paths += list(RUN.glob('*.py')) + list(RUN.glob('*build*.log')) + list(RUN.glob('*kernel*.log'))
paths += list((RUN/'leaves').glob('*')) + [Path(r['snapshot']) for r in MUTABLE.values()]
paths += [RUN/'export-compiled-body-graph-v1.log']
paths=list(dict.fromkeys(p.resolve() for p in paths if p.is_file()))
write(RUN/'body-review-inputs-v1.json',dict(schema='abrl.review-inputs.v1',phase='BODY-v1',
    rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in paths],fixed_input_count=len(paths),
    allowed_writes=['public-body-review-v1.md','public-body-receipt-v1.json'],
    source_audits_pending=5,new_public_proofs=0,chapter_complete=False,goal_complete=False))
contract_bindings_fixed()
print('Actual BODY packet and bounded current inputs prepared, five audited source obligations still pending; no full acceptance.')
