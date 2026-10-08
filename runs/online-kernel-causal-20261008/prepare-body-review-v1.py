from common_canary_v1 import *

canary_fixed()
s = proving_fixed()
audit = load(RUN/'actual-kernel-value-audit-v1.json')
assert audit['five_whole_public_type_VALUE_checks'] and not audit['sorryAx']
assert sha(PUBLIC) == audit['public_sha256'] and sha(CANARY) == audit['canary_sha256']
assert audit['actual_named_canary_proofs'] == 13
assert load(RUN/'canary-blind-receipt-v2.json')['inputs_unchanged']
write(RUN/'neutral-canary-context-disclosure-v3.json',dict(
    previous_bindings_sha256=sha(RUN/'neutral-canary-bindings-v2.json'),
    correction='proof_bodies_excluded means the twelve c2-c13 terminal bodies; the neutral context retains a Markov infer_instance body',
    decoder_message_clarification_received=True,decoder_disclosure_in_receipt=True,
    canary_target_proof_bodies_supplied=False,source_identity_supplied=False,
    frozen_input_bytes_unchanged=True,no_absolute_blind_claim=True))
status = ('Five frozen kernel-realization bodies compiled, thirteen public stochastic/history-feedback canary proofs compiled. '
    'Actual one family, empty-start finite recursion, same-process prefix/nonanticipation, derived fresh-draw joint law, conditional AE law and all-natural-horizon expected-fixed excess. '
    'Whole five public proposition VALUE witnesses, named standard-only axioms, selected direct TYPE/VALUE graph and five native fences/safe-verify passed. '
    'K2/K3/K5 first failures and three canary failures retained; all repairs normalization/API/decidability only, frozen headers unchanged. '
    'Candidate only: zero accepted of five until source BODY/full combined/root/Tests/harness/site/FINAL/native/delivery. '
    'Given behavioral kernels, exogenous independent observation stream; no every-arbitrary-protocol reduction or action-dependent adversary. '
    'Original16/null, other C1/C2/C3-16/appendix obligations and active whole Goal preserved.')
write(RUN/'33_lower-body-candidate-v1.md',status)
write(RUN/'memory-digest-candidate-v1.md',status)
write(RUN/'retrieval-index-candidate-v1.md',
    'Actual compiled named #check/#print axioms and selected VALUE graph in whole-public-types-axioms-v1/export-compiled-body-graph-v1.lean plus actual-kernel-value-audit-v1.json. Shared scanner indexes preserved during frozen contract/proving. Proposed future reviewed refresh may add only these five public declarations and generated timestamps, old records/order retained. Core pinned representation, actual local independence helper and canonical IID producer reused; no new dependencies/toolchain. Global lifecycle memory/SGB frontier unchanged; candidate digest is not accepted shared memory.\n')
write(RUN/'proof-obligations-candidate-v1.json',dict(
    compiled_body_targets=[t['name'] for t in s['targets']],
    dependency_frontier_closed_to_same_process_terminal=True,accepted_obligations=0,pending_acceptance_obligations=5,
    actual_named_canary_proofs=13,one_selected_family=True,
    source_objects16_preserved=True,required_proof_leaf_total=None,
    arbitrary_protocol_reduction_required=True,chapter_complete=False,goal_complete=False))
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=2,actual_bodies=5,actual_canary_proofs=13,
      public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),accepted_obligations=0,pending=5,
      source_body_combined_reader_final_pending=True,chapter_complete=False,goal_complete=False)))
write(RUN/'body-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    contract_receipt_sha256=s['receipt_sha256'],contract_retrieval_supplement_receipt_sha256=sha(RUN/'retrieval-supplement-receipt-v1.json'),
    five_frozen_statement_hashes=[t['statement_hash'] for t in s['targets']],
    canary_headers_sha256=sha(RUN/'canary-frozen-targets-v2.json'),
    reader_requirements=load(CONTRACT/'reader-requirements-v1.json'),
    reader_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),
    future_scope_sha256=sha(RUN/'body-future-integration-scope-v1.json')))
write(RUN/'body-review-packet-v1.md',
    'Distinct anti-anchored staged BODY review. Read body-review-inputs-v1.json; independently verify all fixed RAW bytes before/after. Review actual complete five public proof bodies and thirteen public canary bodies, pinned source texts and original cached PNG13/15 personally. Compare both source-blind reconstructions and seven slots. Resolve original CONTRACT104 changed journals only by approved exact snapshots and parsed own suffixes in stabilized-contract-v1; original104 report retained, retrieval supplement independently verified16. No scanner mutation during proving.\n\n'
    'Actual K1 chooses one infinite jointly measurable representing family before ALL laws/horizons. K2 proves finite recursion measurable, EVERY prefix entry equals SAME infinite process, and pointwise tape<=t/observation<t nonanticipation. K3 derives fresh-coordinate independence from infinitePi/disjoint blocks/product-law regrouping and actual generated history; product-map proof gives actual joint compProd. No desired law/current independence hypothesis. K4 derives only history-marginal AE condDistrib uniqueness. K5 reuses canonical feasible history producer with IID/same-law/AE unit observations transferred through product snd; no supplied regret bound, fixed mean analysis-only, minimum expected fixed losses outsideE, all naturalT/T0. Given behavioral kernels and independent exogenous observations; arbitrary temporal dependence for realization does not represent action-dependent environments or all-protocol reduction. Five derived adapters, not five printed results.\n\n'
    'Canary selects ONE K5 family and uses it in all endpoints and every horizon. Low/high binary laws probability1=1/4 or3/4 depend on last generated action plus last observation>1; empty-start low. Three legal binary histories show both dependencies, every history has both atoms positive. Actual joint law yields actual binary prediction AE. Existing Bernoulli(1/2) observations have positive variance1/4; same process exact excessT/4, zero0, two-roundpositive1/2. Determine whether sufficient nondegenerate feedback evidence; do not infer history-event positivity unless actually proved. Canary frozen13 headers before first Test gate; v1-v3 failures retained, v4actual Built. K2/K3/K5 failures retained, repaired normalization only. Failed compiler-inserted placeholders are never accepted proof. Neutral c terminal bodies absent; context-only Markov infer_instance disclosure is explicit.\n\n'
    'Inspect full five Q VALUE witnesses, standard-only axiom outputs, selected actual TYPE/VALUE direct pairs and five native fences/safe checks. These focused gates do not certify root/Tests/fullharness/site/FINAL/native/delivery. Original16/null and all other source/chapter/appendix obligations remain required. Review the concrete reader-proposal-v1.json and exact future integration scope: bound one card/five notes, precise module ownership/root imports/new own schema2 manifest; old entries/labels/statuses/URLs preserved. Current readers immutable until favorable separate BODY. No pins/globalSGB/frontier/lifecycle-memory/private-paper/anonymous changes. Future retrieval refresh ONLY timestamps and exact five additions with original records/order and actual independent delta audit.\n\n'
    'Return ONLY public-body-review-v1.md and public-body-receipt-v1.json, actual fixed count/RAWbeforeafter/reportSHA/verdict/blocking repairs, seven slots per public target and canary assessment, original R1-R7 copied exactly as required_reader_corrections, approved_future_exact_scope copied exactly from bound file if favorable. Candidate only, no package/source/chapter/Goal acceptance. Distinct reused automated actor, requested Astra/medium, no human/external/absolute blind/runtime attestation. Do not mutate inputs/native/reader/Git or run broad gates.\n')
files = [Path(r['path']) for r in load(RUN/'source-contract-review-inputs-v1.json')['rows']]
for folder in [RUN,CONTRACT]:
    files += [p for p in folder.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
files += [PUBLIC,CANARY,ROOT/'Tests/OnlineGuessingIIDBenchmarkCanary.lean']
rows = raw_index(files)
write(RUN/'body-review-inputs-v1.json',dict(phase='Five actual causal-kernel bodies and stochastic same-process canary BODY review',
    rows=rows,fixed_input_count=len(rows),original_contract_count=104,
    required_reader_corrections=load(CONTRACT/'reader-requirements-v1.json'),
    approved_future_exact_scope=load(RUN/'body-future-integration-scope-v1.json'),
    accepted_obligations=0,chapter_complete=False,goal_complete=False))
canary_fixed()
print('Current fixed RAW BODY input count',len(rows),'five compiled bodies; five acceptance obligations pending.',flush=True)
