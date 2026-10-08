from common_accepted_v3 import *

final = accepted_fixed()
requirements = load(RUN/'stabilized-contract-v2.json')['original_reader_requirements']
scope = ('Expected FIXED-loss minimum and deterministic finite-history causal IID core only: probability/measurable/a.s.unit targets, '
    'same-law expected square decomposition, actual feasible population mean and IsLeast before real csInf, '
    'joint-IID actual strict-history policy and first1/2 meanPredict excess identity/nonnegativity, known-law mean oracle zero excess, positiveT finite normalization. '
    'Eight derived producer/representation/adapters and two definitions, not eight source theorems or new rate mathematics. '
    'V2 policy feasibility only on legal histories; T0 empty extension without uniqueness.')
remaining = ('Randomized/external-seed/general-filtration cannot-beat source coverage and asymptotic-success equivalence REQUIRED; '
    'original16C1source items/proof-totalnull/fullC1open and five old main-relative Foundations/History/IID/Information/Stochastic audits unwaived. '
    'Chapter2incomplete, Chapters3–16unenumerated/necessaryappendices required, totalGoalACTIVE. '
    'No min/expectation exchange, unknown-law oracle implementation or high-probability claim. OPENdraft/unmerged PR193 exactbf9f896cdfebb2b836dacb01f3d4b209466c2100 stack; no main/live/merge/deploy/retirement.')
boundary = dict(source_package_accepted=True, chapter_complete=False, goal_complete=False, merged=False, live=False,
    new_public_proofs=8, new_public_definitions=2, bounded_subobligation_closures=1,
    whole_source_items_closed=0, new_registry_nodes=10)
write(RUN/'accepted-reader-discharge-v3.json', dict(status='passed', original_requirements=requirements,
    actual_FINAL_verdicts=final['reader_requirement_verdicts'], final_receipt_sha256=sha(RUN/'final-reader-receipt-v3.json')))
write(RUN/'accepted-decision-v3.json', dict(status=final['verdict'], scope=scope, remaining_required=remaining,
    public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY), contract_version=2, exact_base_PR=193, exact_base_head=BASE,
    body_bindings=load(RUN/'body-bindings-v2.json'), applicable_integrated=load(RUN/'integrated-gates-v2.json'),
    applicable_site_commit=load(RUN/'registry-v9.json')['source_commit'], registry_record_sha256=sha(RUN/'registry-v9.json'),
    pixel_record_sha256=sha(RUN/'pixel-review-v9.json'), final_receipt_sha256=sha(RUN/'final-reader-receipt-v3.json'),
    PR_delivery_pending=True, **boundary))
ledger = load(CONTRACT/'chapter-one-source-ledger-draft-v2.json')
assert len(ledger['maintext_items']) == 16 and ledger['chapter_mandatory_proof_total'] is None and ledger['version'] == 3
ledger['version'] = 4
ledger['prior_current_draft_ledger'] = dict(path=(CONTRACT/'chapter-one-source-ledger-draft-v2.json').as_posix(), sha256=sha(CONTRACT/'chapter-one-source-ledger-draft-v2.json'))
ledger['enumeration_status'] = '16 original source items retained; mandatory proof-leaf total null. Bounded expected-fixed/deterministic IID core accepted; full source randomized/filtration/asymptotic coverage and C1 remain open.'
ledger['source_package_accepted'] = True
ledger['current_package_only'] = scope
ledger['accepted_expected_fixed_deterministic_IID_subobligation'] = dict(source_ids=['C1-IID-MEAN', 'C1-IID-LOWER'], printed_pages=[1,2], pdf_pages=[13,14],
    declarations=[x['name'] for x in load(CONTRACT/'targets-v2.json')['rows']], evidence=(RUN/'accepted-decision-v3.json').as_posix(),
    remaining_required=remaining, whole_source_item_complete=False)
ledger['remaining_IID_expected_fixed_minimum_and_causal_cumulative_variance'] = 'Bounded same-law expected-fixed minimum/deterministic finite-history causal core accepted; randomized/general-filtration source-wide assertion REQUIRED next.'
for item in ledger['maintext_items']:
    if item['source_id'] in ['C1-IID-MEAN', 'C1-IID-LOWER']:
        item['current_IID_subobligation'] = scope+' '+remaining
        item['current_IID_evidence'] = (RUN/'accepted-decision-v3.json').as_posix()
ledger['chapter_complete'] = ledger['goal_complete'] = False
write(CONTRACT/'chapter-one-source-ledger-accepted-v4.json', ledger)
digest = (TASK+' '+scope+' '+remaining+' Actual53kernel/36nativeguards/26VALUEpairs,28namedcanaries5fixtures2probability proofs, '
    '8neutral->draft+8draft->actual arbitrary-universe Prop identities/28canaryProps/9wholedefinition identities; '
    'root9097/Tests9253/harness472skip7/actualcommitted5productionpaths1contract. '
    'Clean a15115609562ea163c9b95a3bd111cac2df74edc local v9Leanverifiedsite/10913oldsharedIDsURLsHashes+10newnodes/14currentimages independently viewed; '
    'distinct staged decoder/source reviewer CONTRACT186/BODY583/FINAL846 accepted with exactR1–R9. RequestedAstra-medium/nohuman/external/runtimeattestation. '
    'Frozen8terminal contract progresses8->0 ONLY. Rejected FINALv2/F1/F2 reader inversion and missing t>0 retained; exact reader-only repair/fresh v9/F1F2 distinct review required. Original failures/rawbyte12whitespaceexceptions retained, fullunexcluded diffexit2/scoped pass, two frozenhelperEOFfindings separately reviewed.')
write(RUN/'memory-digest-accepted-v3.md', digest)
write(RUN/'retrieval-index-accepted-v3.md', digest)
terminal = PRE+'history_policy_expectedFixed_excess'
statement = load(RUN/'full-header-fences-v2/public-history_policy_expectedFixed_excess.json')
native('accepted-reviewer-trial-v3', 'trial-log', '--task', TASK, '--role', 'reviewer', '--kind', 'review', '--status', 'accepted',
    '--run-id', RUN.name, '--attempt-id', 'IID-BENCHMARK-V2', '--statement-hash', statement['statement_hash'], '--new-declaration', terminal,
    '--verifier-evidence', RUN/'final-reader-receipt-v3.json', '--harness', 'hierarchical', '--progress-class', 'terminal', '--reviewer-validated',
    '--obligations-before', '8', '--obligations-after', '0', '--notes', digest)
own = [json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if line.strip() and json.loads(line).get('task') == TASK]
assert sum(x.get('status') == 'accepted' and x.get('role') == 'reviewer' for x in own) == 1
write(RUN/'accepted-scoped-trials-v3.jsonl', '\n'.join(json.dumps(x, ensure_ascii=False) for x in own))
native('accepted-lifecycle-v3', 'lifecycle-event', '--session', TASK, '--event', 'accepted', '--payload-json',
    json.dumps(dict(run_id=RUN.name, contract_version=2, accepted_decision=(RUN/'accepted-decision-v3.json').as_posix(), scope_only='bounded-expected-fixed-deterministic-IID', **boundary)))
native('accepted-frontier-refresh-v3', 'frontier-refresh', '--root-objective', 'Persistent Orabona Chapters1–16; bounded deterministic IID expected-fixed core only',
    '--leaf', TASK, '--kind', 'lean', '--statement', statement['statement'], '--declaration', terminal, '--file', PUBLIC,
    '--source-status', 'source-reviewed', '--leaf-status', 'accepted', '--dependency', 'lean:'+PRE+'expectedFixedMinimum_eq_variance:compiled',
    '--dependency', 'review:source-reader:accepted', '--trials', RUN/'accepted-scoped-trials-v3.jsonl', '--output', RUN/'accepted-frontier-v3.json', '--shadow-status', 'pending')
native('accepted-frontier-shadow-v3', 'frontier-shadow', '--trials', RUN/'accepted-scoped-trials-v3.jsonl',
    '--memory-digest', RUN/'memory-digest-accepted-v3.md', '--frontier', RUN/'accepted-frontier-v3.json')
shadow = json.loads((RUN/'accepted-frontier-shadow-v3.log').read_text(encoding='utf8'))
assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v3', 'memory-record', '--type', 'verified_lemma', '--task', TASK,
    '--provenance-kind', 'source-reviewed-compiled-expected-fixed-deterministic-IID', '--provenance', RUN/'accepted-decision-v3.json',
    '--declaration', terminal, '--file', PUBLIC, '--status', 'accepted', '--verifier', RUN/'final-reader-receipt-v3.json',
    '--role', 'reviewer', '--details-json', json.dumps(dict(scope=scope, remaining_required=remaining, **boundary)), '--output', RUN/'accepted-memory-record-v3.json')
native('accepted-retrieval-record-v3', 'retrieval-record', '--task', TASK, '--query', 'Produce expected fixed interval minimum and actual a.s.-supported strict-past IID excess',
    '--candidate', PRE+'expectedFixedMinimum_eq_variance', '--candidate', terminal, '--compiled-scratch', CANARY,
    '--provenance', RUN/'causal-canary-focused-build-v6-exit.json', '--output', RUN/'accepted-retrieval-record-v3.json')
m = load(MANIFEST)
m['semantic_roundtrip']['remaining_semantic_delta'] += ' Separate actual FINAL accepted; exactR1–R9 satisfied for bounded deterministic core only. Randomized/filtration/asymptotic source and whole chapter/program remain required.'
m['verification']['independent_review'] = 'Actual distinct staged CONTRACT186/BODY583/FINAL846 accepted-with-explicit-delta; FINAL receipt '+sha(RUN/'final-reader-receipt-v3.json')+'; exactR1–R9 satisfied. No human/external/runtime attestation.'
m['verification']['bandit_check'] = 'Actual shared root9097/Tests9253/fullharness472tests7skips and committed contributor5productionpaths1contract pass; inheritedmain5moduleaudits unwaived.'
m['verification']['site_build'] = 'Applicable clean a15115609562ea163c9b95a3bd111cac2df74edc local v9source, dirtyfalse/Leanverifiedtrue; unchanged Lean hashes covered by actual combined gates, no deployment.'
m['verification']['site_check'] = 'Actual10913oldshared IDs/URLs/statementhashes preserved+10newpublicnodes;14current ROOT and distinct FINAL original pixel reviews, eight exact notes/fourwrapped catalogue types.'
m['graph_contribution']['visual_review'] = 'Actual53selected compiled constants/44theoremkind/9definitions and26VALUEpairs;10newsharedregistry nodes; current DOM/pixels/distinct FINAL accepted.'
MANIFEST.write_bytes((json.dumps(m, ensure_ascii=False, indent=2)+'\n').encode('utf8'))
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    p = Path(folder)/(TASK+'.md')
    p.write_bytes(p.read_bytes()+('\n\n## Bounded deterministic IID package accepted; draft PR pending\n\n'+digest+'\n').encode('utf8'))
write(RUN/'40_reviewer_decision-v3.md', 'Distinct actual source/reader FINAL verdict bound by receipt; formalizer rehashes and records separate native acceptance, without replacing the reviewer. '+digest)
write(RUN/'native-acceptance-overlay-v3.json', dict(status='passed', one_accepted_reviewer_trial=True, obligations_before=8, obligations_after=0,
    obligation_count_scope='Only eight frozen v2 derived expected-fixed/deterministic-IID terminals', globalSGB_unchanged=True, PR_delivery_pending=True, **boundary))
accepted_fixed()
print('Only bounded deterministic IID package accepted; PR pending; whole-book Goal ACTIVE.')
