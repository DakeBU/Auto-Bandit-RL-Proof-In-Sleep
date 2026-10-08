from common_proving_v1 import *

s=proving_fixed();audit=load(RUN/'actual-kernel-value-audit-v1.json')
assert audit['four_whole_public_type_VALUE_checks'] and not audit['sorryAx']
assert sha(PUBLIC)==audit['public_sha256'] and sha(CANARY)==audit['canary_sha256']
assert audit['actual_named_canary_proofs']==11 and audit['actual_required_VALUE_pairs']==18
scope=dict(phase='After favorable BODY only: combined root/Test/reader/shared Book integration',
    immutable=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'lean-toolchain','lakefile.lean','lake-manifest.json'],
    exact_root_additions={'BanditRLProof.lean':'\nimport BanditRLProof.OnlineGuessingCompletedCausal\n',
        'Tests.lean':'\nimport Tests.OnlineGuessingCompletedCausalCanary\n'},
    reader_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],
    reader_delta='Append exactly one source-qualified derived completion card and four exact public mathematical proof notes on online-foundations; append precise remaining boundary to that chapter gaps/blockers and exactly BanditRLProof/OnlineGuessingCompletedCausal.lean to its module_globs. Preserve all prior entries/labels/statuses/links and old Book registry IDs/URLs/hashes.',
    external_mathlib_dependency_links='Mathlib APIs in explicit reader prose and actual compiled VALUE audit; registry dependency links only to actual ABRL public declarations. Core may have no ABRL parent link; do not fabricate one.',
    own_schema2_manifest='Exactly four target names/source-version/reuse decision, actual-contract/BODY review, reader requirements, truthful graph/source boundary and subsequent gate evidence pending',
    native_scope='Only own task/session exact suffixes and logs/versioned candidates; do not replace global SGB frontier. Actual shadow/combined/fullharness/source/axiom/site/FINAL gates separately required.',
    no_generated_site_edit=True,no_old_module_statement_or_body_change=True,
    only_derived_obligations=4,original_source_objects=16,unknown_required_proof_total=None,
    general_causal_kernel_required=True,chapter_complete=False,goal_complete=False)
write(RUN/'body-future-integration-scope-v1.json',scope)
status='Four frozen public bodies actually Built3390 and11canary bodies Built3439. Core constructs real F-measurable version from actual ambient augmented measurability. All three adapters genuinely consume it before immutable AE parents. Actual full four proposition proof VALUE checks,56unique named axiom records with standard axioms only,52selected nodes2614coalesced TYPE_VALUE edges18required VALUE pairs, four native fences/safe checks. First core failure/typed-printer failure retained; repair proof-local only. Candidate only; accepted obligations0/4, fullroot/Tests/harness/reader/site/FINAL/native/draft gates pending. Source4derived, not4printed; original16/null/kernel/fullremaining/wholeGoal active.'
write(RUN/'33_lower-body-candidate-v1.md',status)
write(RUN/'memory-digest-candidate-v1.md',status)
write(RUN/'proof-obligations-candidate-v1.json',dict(compiled_body_targets=[t['name'] for t in s['targets']],
    accepted_obligations=0,pending_acceptance_obligations=4,core_version_producer_actual=True,
    full_gate_pending=True,original_source16_unchanged=True,unknown_total=None,general_causal_kernel_required=True,
    chapter_complete=False,goal_complete=False))
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=1,actual_bodies=4,actual_canary_proofs=11,
        public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),accepted_obligations=0,pending=4,
        combined_and_reader_gate_pending=True,chapter_complete=False,goal_complete=False)))
write(RUN/'body-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    contract_receipt_sha256=s['receipt_sha256'],four_frozen_statement_hashes=[t['statement_hash'] for t in s['targets']],
    reader_requirements=load(CONTRACT/'reader-requirements-v1.json')))
rows={}
def add(p):
    p=Path(p).resolve();assert p.is_file();rows[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for row in load(RUN/'source-contract-review-inputs-v1.json')['rows']:add(row['path'])
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:add(p)
for p in [PUBLIC,CANARY]:add(p)
write(RUN/'body-review-inputs-v1.json',dict(phase='Actual four complete public bodies and genuine augmented-information canary review',
    rows=sorted(rows.values(),key=lambda r:r['path']),fixed_input_count=len(rows),original_contract_count=175,
    required_reader_corrections=load(CONTRACT/'reader-requirements-v1.json'),approved_future_exact_scope=scope,
    accepted_obligations=0,chapter_complete=False,goal_complete=False))
write(RUN/'body-review-packet-v1.md',
    'Distinct staged anti-anchored BODY reviewer: independently RAW-check every current row before/after; resolve original CONTRACT175 only via exact seven mutable snapshots in stabilized-contract-v1, not by asserting changed live journals match old RAW. Inspect actual complete four public proof bodies,11canary proofs and genuine nonempty-null off-causal original process, source/decoder/CONTRACT, full four Q/value witnesses,56standard-only named axioms,52selected compiled nodes2614coalesced TYPE_VALUE edges18required VALUE pairs and four exact native fences. These are actual source-backed compilation artifacts, not command0-only claims.\n\n'
    'Core: choose F-measurable coordinate representatives under ambientAE, one countable AE equality of real Bool codes, measurable embedding inverse on every code with original equality AE. Inspect all typeclass instances, real regularity and no F<=ambient/probability/space-countability assumption. Three adapters obtain AEstrong from actual core, then invoke actual immutable original AE parents. Preserve single all-time event/one family/allinputsunit and originalAEunit, original current independence/whole-stream seed, original-P fixed expected min outside expectation, allNatT/T0/no convergence.\n\n'
    'First L1failed exact F instance/Bool preimage normalization, actual v2sameheader Built; type-printer invalid import v2 retained then v3onlyoptionposition passes. No terminal weakened. Whole source objects16/null and kernel/othercompletion/remainingchapters/appendices remain required. Full root/Test/harness/reader/site/FINAL/native/delivery are future, not certified BODY. Evaluate exact future scope including explicit one module_globs owning path to avoid ambiguous Book ownership, external mathlib dependency text versus real local registry links, root imports and four proof notes. Source4derived, not4printed.\n\n'
    'Return ONLY public-body-review-v1.md / public-body-receipt-v1.json, actual count/RAWbeforeafter/reportSHA, seven slots per target, verdict/blockers, original R1-R7 copied exactly in required_reader_corrections and exact approved_future_exact_scope if favorable. No input/native/publication edits; distinct reused automated history, requested Astra/medium, no human/external/absolute blindness/runtime attestation. Whole Goal ACTIVE.\n')
print('Actual BODY current fixed RAW input count:',len(rows),'four bodies compiled, four accepted obligations still pending.',flush=True)
