from common_accepted_v3 import *

final = accepted_fixed()
scope = ('Independent private tape and subordinate strict-past information finite IID producer only: '
    'whole-process tape independence, jointly IID measurable a.s.unit targets, same-law expected fixed benchmark, '
    'derived current independence and L2, real jointly measurable policy feasible for every seed only on legal histories. '
    'Seven derived proofs and one information definition; same-prefix excess identity and nonnegativity, not a new rate or seven printed results.')
remaining = ('Universal-kernel/completed-information/AE-factorization full-source coverage audit and source asymptotic-success equivalence REQUIRED; '
    'original16 C1 source items/proof-totalnull/five old main-relative source-module audits unwaived/C1C2open/3-16unenumerated/necessaryappendicesrequired/GoalACTIVE. '
    'OPENdraft/unmerged PR194 exact b08 stack; no main/live/merge/deploy/retirement.')
boundary = dict(source_package_accepted=True, chapter_complete=False, goal_complete=False,
    merged=False, live=False, new_public_proofs=7, new_public_definitions=1,
    bounded_subobligation_closures=1, whole_source_items_closed=0)
write(RUN/'accepted-reader-discharge-v3.json', dict(status='passed',
    original_requirements=load(CONTRACT/'reader-requirements-v2.json'),
    actual_FINAL_verdicts=final['reader_requirement_verdicts'],
    final_receipt_sha256=sha(RUN/'final-reader-receipt-v3.json')))
write(RUN/'accepted-decision-v3.json', dict(status=final['verdict'], scope=scope, remaining_required=remaining,
    public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY), contract_version=2, exact_base_PR=194, exact_base_head=BASE,
    body_bindings=load(RUN/'body-bindings-v2.json'), combined_gates=load(RUN/'combined-gates-v3.json'),
    actual_current_contributor=load(RUN/'current-reader-gate-bindings-v3.json'),
    applicable_site_commit=load(RUN/'registry-v3.json')['source_commit'],
    registry_sha256=sha(RUN/'registry-v3.json'), pixel_record_sha256=sha(RUN/'pixel-review-v3.json'),
    final_receipt_sha256=sha(RUN/'final-reader-receipt-v3.json'), native_acceptance_pending=True,
    PR_delivery_pending=True, **boundary))

ledger_path = CONTRACT/'chapter-one-source-ledger-draft-v2.json'
ledger = load(ledger_path)
assert len(ledger['maintext_items']) == 16 and ledger['chapter_mandatory_proof_total'] is None
original_items = ledger['maintext_items']
ledger['version'] = 3
ledger['prior_current_draft_ledger'] = dict(path=ledger_path.as_posix(), sha256=sha(ledger_path))
ledger['enumeration_status'] = 'Original16 source objects unchanged; required proof-leaf total null. Accepted bounded private-tape subobligation, whole C1 open.'
ledger['current_package_only'] = scope
ledger['current_planned_new_proofs'] = ledger['current_compiled_new_proofs'] = 7
ledger['current_planned_new_definitions'] = ledger['current_compiled_new_definitions'] = 1
ledger['accepted_private_seed_subobligation'] = dict(source_ids=['C1-IID-LOWER', 'C1-EQ1.1-1.2'],
    printed_pages=[1,2], pdf_pages=[13,14], declarations=[x['name'] for x in load(CONTRACT/'targets-v2.json')['rows']],
    evidence=(RUN/'accepted-decision-v3.json').as_posix(), scope=scope, remaining_required=remaining,
    whole_source_item_complete=False)
ledger['current_randomized_IID_package'] = dict(status='bounded-semantic-accepted; native/draft PR still separate',
    exact_base_PR=194, exact_base_head=BASE, terminal_ids=[x['id'] for x in load(CONTRACT/'targets-v2.json')['rows']], **boundary)
ledger['remaining_randomized_or_abstract_filtration_causal_benchmark'] = 'Bounded private-tape/subordinate-information producer accepted; universal kernel/completed-information/AE-factorization source coverage audit REQUIRED.'
ledger['remaining_source_asymptotic_success_equivalence'] = 'REQUIRED separately; no convergence/rate proof in this package.'
ledger['chapter_complete'] = ledger['goal_complete'] = False
assert ledger['maintext_items'] == original_items
write(CONTRACT/'chapter-one-source-ledger-accepted-v3.json', ledger)

digest = (TASK+' '+scope+' '+remaining+' Actual55kernel/42theorem13definition/26VALUEpairs/36nativeguards, '
    '29namedcanaries9fixtures2probabilityproofs2anonymousclassvalues; arbitrary-universe exact public/canary/whole-definition types. '
    'Root9098/Tests9255/fullharness472skip7/currentcommittedcontributor5productionpaths1contract. '
    'Clean f8c25ea9e5e43841410c0449cb226650cdb057cb v3localLeanverifiedsite;10923oldregistryIDsURLsHashes+8newnodes;13currentoriginalimages viewed by ROOT and distinct FINAL reviewer. '
    'Distinct staged decoder/CONTRACT1143/BODY1582/FINAL1822 accepted with exactR1-R7; no human/external/absolute-blind/model-runtime attestation. '
    'Only frozen seven terminals progress7->0. Raw failed attempts/tracking-only/parser/weak historical guessed-hash OR-prefix guard/reader corrections retained. '
    'Fullunexcluded whitespaceexit2/scopedpass/exactfiveSHA-boundRAWstdoutexceptions/noexecutablehelper exemption. '
    'Actual native acceptance and PR delivery remain separate, performed below with versioned evidence.')
write(RUN/'memory-digest-accepted-v3.md', digest)
write(RUN/'retrieval-index-accepted-v3.md', digest)
statement = load(RUN/'full-header-fences-v2/public-randomized_history_policy_expectedFixed_excess.json')
terminal = PRE+'randomized_history_policy_expectedFixed_excess'
native('accepted-reviewer-trial-v3', 'trial-log', '--task', TASK, '--role', 'reviewer', '--kind', 'review', '--status', 'accepted',
    '--run-id', RUN.name, '--attempt-id', 'PRIVATE-IID-V2', '--statement-hash', statement['statement_hash'],
    '--new-declaration', terminal, '--verifier-evidence', RUN/'final-reader-receipt-v3.json',
    '--harness', 'hierarchical', '--progress-class', 'terminal', '--reviewer-validated',
    '--obligations-before', '7', '--obligations-after', '0', '--notes', digest)
own = [json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines()
    if line.strip() and json.loads(line).get('task') == TASK]
assert sum(x.get('status') == 'accepted' and x.get('role') == 'reviewer' for x in own) == 1
write(RUN/'accepted-scoped-trials-v3.jsonl', '\n'.join(json.dumps(x, ensure_ascii=False) for x in own))
native('accepted-lifecycle-v3', 'lifecycle-event', '--session', TASK, '--event', 'accepted', '--payload-json',
    json.dumps(dict(run_id=RUN.name, contract_version=2, accepted_decision=(RUN/'accepted-decision-v3.json').as_posix(),
        scope_only='bounded-independent-private-tape', **boundary)))
native('accepted-frontier-refresh-v3', 'frontier-refresh', '--root-objective',
    'Persistent Orabona Chapters1-16; bounded independent-private-tape finite IID producer only',
    '--leaf', TASK, '--kind', 'lean', '--statement', statement['statement'], '--declaration', terminal,
    '--file', PUBLIC, '--source-status', 'source-reviewed', '--leaf-status', 'accepted',
    '--dependency', 'lean:'+PRE+'private_seed_past_independent:compiled',
    '--dependency', 'lean:'+PRE+'predictable_private_seed_expectedFixed_excess:compiled',
    '--dependency', 'review:source-reader:accepted', '--trials', RUN/'accepted-scoped-trials-v3.jsonl',
    '--output', RUN/'accepted-frontier-v3.json', '--shadow-status', 'pending')
native('accepted-frontier-shadow-v3', 'frontier-shadow', '--trials', RUN/'accepted-scoped-trials-v3.jsonl',
    '--memory-digest', RUN/'memory-digest-accepted-v3.md', '--frontier', RUN/'accepted-frontier-v3.json')
shadow = json.loads((RUN/'accepted-frontier-shadow-v3.log').read_text(encoding='utf8'))
assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v3', 'memory-record', '--type', 'verified_lemma', '--task', TASK,
    '--provenance-kind', 'source-reviewed-compiled-private-tape-IID', '--provenance', RUN/'accepted-decision-v3.json',
    '--declaration', terminal, '--file', PUBLIC, '--status', 'accepted', '--verifier', RUN/'final-reader-receipt-v3.json',
    '--role', 'reviewer', '--details-json', json.dumps(dict(scope=scope, remaining_required=remaining, **boundary)),
    '--output', RUN/'accepted-memory-record-v3.json')
native('accepted-retrieval-record-v3', 'retrieval-record', '--task', TASK,
    '--query', 'Produce actual independent private tape/strict-past expected-fixed IID excess',
    '--candidate', PRE+'private_seed_past_independent', '--candidate', terminal, '--compiled-scratch', CANARY,
    '--provenance', RUN/'canary-XOR-focused-build-v3-exit.json', '--output', RUN/'accepted-retrieval-record-v3.json')
m = load(MANIFEST)
m['semantic_roundtrip']['remaining_semantic_delta'] += ' Separate actual FINAL accepted; exactR1-R7 satisfied for bounded private-tape producer only. Native acceptance records are separate; full source/kernel/asymptotic/chapter/program obligations remain required.'
m['verification']['independent_review'] = 'Distinct staged CONTRACT1143/BODY1582/FINAL1822 accepted-with-explicit-delta; exactR1-R7 satisfied. FINAL receipt '+sha(RUN/'final-reader-receipt-v3.json')+'; no human/external/runtime attestation.'
m['verification']['bandit_check'] = 'Actual shared root9098/Tests9255/fullharness472tests7skips/current committed contributor5productionpaths1contract and scoped shadow pass; oldmain5moduleaudits unwaived.'
m['verification']['site_build'] = 'Applicable clean f8c25ea9e5e43841410c0449cb226650cdb057cb v3local source, dirtyfalse/Leanverifiedtrue; unchanged Lean/pin hashes covered by actual combined gates, no deployment.'
m['verification']['site_check'] = 'Actual10923oldregistry IDs/URLs/statementhashes preserved+8newpublicnodes;13current ROOT and distinct FINAL original pixel reviews, seven exact notes/fourwrapped catalogue types.'
m['graph_contribution']['visual_review'] = '55selected compiled constants/42theorem13definition/26directVALUEpairs;8newsharedregistry nodes; current DOM/pixels/distinct FINAL accepted.'
MANIFEST.write_bytes((json.dumps(m, ensure_ascii=False, indent=2)+'\n').encode('utf8'))
for p in OWN_METADATA:
    p.write_bytes(p.read_bytes()+('\n\n## Bounded private-tape producer accepted; draft PR pending\n\n'+digest+'\n').encode('utf8'))
write(RUN/'40_reviewer-decision-v3.md', 'Distinct actual FINAL source/reader verdict bound by receipt; formalizer records separate actual native acceptance. '+digest)
write(RUN/'proof-obligations-accepted-v3.json', dict(contract_version=2, frozen_targets=7, compiled_targets=7,
    accepted_targets=7, remaining_mathematical_terminals=0, obligation_count_scope='Only seven frozen v2 derived terminals',
    chapter1_source_items=16, chapter_mandatory_proof_total=None, remaining_required=remaining,
    PR_delivery_pending=True, **boundary))
write(RUN/'native-acceptance-overlay-v3.json', dict(status='passed', one_accepted_reviewer_trial=True,
    obligations_before=7, obligations_after=0, obligation_count_scope='Only seven frozen v2 derived terminals',
    globalSGB_unchanged=True, PR_delivery_pending=True, **boundary))
accepted_fixed()
print('Actual bounded private-tape package accepted; PR pending; total Goal active.')
