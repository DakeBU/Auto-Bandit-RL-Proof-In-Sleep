from common_accepted_v1 import *

final = accepted_fixed()
requirements = load(RUN / 'stabilized-contract-v1.json')['original_reader_requirements']
scope = ('C1 pathwise square-minimum hinge only: actual empirical-mean feasibility/minimization and attained real interval infimum; '
    'signed same-process best-fixed/comparator identity and order; existing actual first1/2 strict-past FTL log and sharp-quarter-tail guarantees expressed against that minimum. '
    'Six derived producer/representation/adapters and one definition, not six printed source theorems or new rate mathematics. '
    'T0 empty extension without uniqueness; positiveT performance restrictions; arbitrary supplied traces algebra only.')
remaining = ('Original16C1source items/proof-totalnull/fullC1open, expected FIXED-loss minimum and causal IID cumulative variance REQUIRED next; '
    'five older main-relative Foundations/History/IID/Information/Stochastic audits unwaived. Chapter2incomplete, Chapters3–16unenumerated, necessaryappendices required, totalGoalACTIVE. '
    'No min/expectation interchange or generic causal learner; exact OPENdraft/unmergedPR192base2aa08b9e1f5da4d0c7d7dcbe9ddeadd1fbfc34e3 stack, no main/live/merge/deploy/retirement.')
boundary = dict(source_package_accepted=True, chapter_complete=False, goal_complete=False, merged=False, live=False,
    new_public_proofs=6, new_public_definitions=1, source_subobligation_closures=1, new_registry_nodes=7)
write(RUN / 'accepted-reader-discharge-v1.json', dict(status='passed', original_requirements=requirements,
    actual_FINAL_verdicts=final['reader_requirement_verdicts'], final_receipt_sha256=sha(RUN / 'final-reader-receipt-v1.json')))
write(RUN / 'accepted-decision-v1.json', dict(status=final['verdict'], scope=scope, remaining_required=remaining,
    public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY), contract_version=1,
    exact_base_PR=192, exact_base_head=BASE, body_bindings=load(RUN / 'body-bindings-v1.json'),
    applicable_integrated=load(RUN / 'integrated-gates-v2.json'), applicable_site_commit=load(RUN / 'registry-v1.json')['source_commit'],
    registry_record_sha256=sha(RUN / 'registry-v1.json'), pixel_record_sha256=sha(RUN / 'pixel-review-v1.json'),
    final_receipt_sha256=sha(RUN / 'final-reader-receipt-v1.json'), PR_delivery_pending=True, **boundary))
ledger = load(CONTRACT / 'chapter-one-source-ledger-draft-v1.json')
assert len(ledger['maintext_items']) == 16 and ledger['chapter_mandatory_proof_total'] is None
ledger['version'] = 2
ledger['prior_current_draft_ledger'] = dict(path=(CONTRACT / 'chapter-one-source-ledger-draft-v1.json').as_posix(), sha256=sha(CONTRACT / 'chapter-one-source-ledger-draft-v1.json'))
ledger['enumeration_status'] = '16 original source items retained; mandatory proof-leaf total null. Only bounded pathwise square-minimum hinge accepted; full C1 remains open.'
ledger['source_package_accepted'] = True
ledger['current_package_only'] = scope
ledger['accepted_square_minimum_subobligation'] = dict(source_id='C1-REGRET', printed_pages=[2,3,4,5], pdf_pages=[14,15,16,17],
    declarations=[x['name'] for x in load(CONTRACT / 'targets-v1.json')['rows']],
    evidence=(RUN / 'accepted-decision-v1.json').as_posix(), remaining_required=remaining, whole_source_item_complete=False)
ledger['remaining_IID_expected_fixed_minimum_and_causal_cumulative_variance'] = 'REQUIRED next printed1–2/PDF13–14, no min/expectation exchange.'
ledger['chapter_complete'] = ledger['goal_complete'] = False
write(CONTRACT / 'chapter-one-source-ledger-accepted-v2.json', ledger)
digest = (TASK + ' ' + scope + ' ' + remaining + ' Actual38kernel/26nativeguards/16VALUEpairs,20namedcanaries2fixtures, '
    '6neutral->draft+6draft->actual+20canary types and6wholedefinition identities. Root9096/Tests9251/harness472skip7; '
    'actual committed5productionpaths1contract gate supersedes initialvacuous0/0. Clean47c6a03 localLeanverifiedsite/10906oldsharedIDsURLsHashes+7newnodes/12currentimages independently viewed. '
    'Distinct reused staged decoder/source reviewer CONTRACT/BODY/FINAL accepted with exact R1–R8; requestedAstra-medium/no human/external/runtime attestation. '
    'Frozen6terminal contract progresses6->0 only; original helper/ownership/whitespace/clean-tail failures retained and rawbytes preserved.')
write(RUN / 'memory-digest-accepted-v1.md', digest)
write(RUN / 'retrieval-index-accepted-v1.md', digest)
terminal = PRE + 'meanPredict_bestRegret_refined'
statement = load(RUN / 'full-header-fences-v1/public-meanPredict_bestRegret_refined.json')
native('accepted-reviewer-trial-v1', 'trial-log', '--task', TASK, '--role', 'reviewer', '--kind', 'review', '--status', 'accepted',
    '--run-id', RUN.name, '--attempt-id', 'SQUARE-MINIMUM-V1', '--statement-hash', statement['statement_hash'], '--new-declaration', terminal,
    '--verifier-evidence', RUN / 'final-reader-receipt-v1.json', '--harness', 'hierarchical', '--progress-class', 'terminal', '--reviewer-validated',
    '--obligations-before', '6', '--obligations-after', '0', '--notes', digest)
own = [json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if line.strip() and json.loads(line).get('task') == TASK]
assert sum(x.get('status') == 'accepted' and x.get('role') == 'reviewer' for x in own) == 1
write(RUN / 'accepted-scoped-trials-v1.jsonl', '\n'.join(json.dumps(x, ensure_ascii=False) for x in own))
native('accepted-lifecycle-v1', 'lifecycle-event', '--session', TASK, '--event', 'accepted', '--payload-json',
    json.dumps(dict(run_id=RUN.name, contract_version=1, accepted_decision=(RUN / 'accepted-decision-v1.json').as_posix(), scope_only='C1-pathwise-square-minimum', **boundary)))
native('accepted-frontier-refresh-v1', 'frontier-refresh', '--root-objective', 'Persistent Orabona Chapters1–16; only actual pathwise-square-minimum hinge accepted',
    '--leaf', TASK, '--kind', 'lean', '--statement', statement['statement'], '--declaration', terminal, '--file', PUBLIC,
    '--source-status', 'source-reviewed', '--leaf-status', 'accepted', '--dependency', 'lean:' + PRE + 'squaredLoss_minimum_eq:compiled',
    '--dependency', 'review:source-reader:accepted', '--trials', RUN / 'accepted-scoped-trials-v1.jsonl', '--output', RUN / 'accepted-frontier-v1.json', '--shadow-status', 'pending')
native('accepted-frontier-shadow-v1', 'frontier-shadow', '--trials', RUN / 'accepted-scoped-trials-v1.jsonl',
    '--memory-digest', RUN / 'memory-digest-accepted-v1.md', '--frontier', RUN / 'accepted-frontier-v1.json')
shadow = json.loads((RUN / 'accepted-frontier-shadow-v1.log').read_text(encoding='utf8'))
assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1', 'memory-record', '--type', 'verified_lemma', '--task', TASK,
    '--provenance-kind', 'source-reviewed-compiled-square-minimum', '--provenance', RUN / 'accepted-decision-v1.json',
    '--declaration', terminal, '--file', PUBLIC, '--status', 'accepted', '--verifier', RUN / 'final-reader-receipt-v1.json',
    '--role', 'reviewer', '--details-json', json.dumps(dict(scope=scope, remaining_required=remaining, **boundary)),
    '--output', RUN / 'accepted-memory-record-v1.json')
native('accepted-retrieval-record-v1', 'retrieval-record', '--task', TASK, '--query',
    'Produce the attained interval squared-loss minimum and same actual strict-past FTL best-fixed regret',
    '--candidate', PRE + 'squaredLoss_minimum_eq', '--candidate', terminal, '--compiled-scratch', CANARY,
    '--provenance', RUN / 'public-canary-focused-build-v1-exit.json', '--output', RUN / 'accepted-retrieval-record-v1.json')
m = load(MANIFEST)
m['semantic_roundtrip']['remaining_semantic_delta'] += ' Actual separate FINAL accepted; exact R1–R8 satisfied; no chapter/program acceptance.'
m['verification']['independent_review'] = 'Actual distinct staged CONTRACT/BODY/FINAL accepted-with-explicit-delta; FINAL receipt ' + sha(RUN / 'final-reader-receipt-v1.json') + '; exact R1–R8 satisfied. Decoder reconstructs only; no human/external/runtime attestation.'
m['verification']['bandit_check'] = 'Actual shared root9096/Tests9251/full harness472tests7skips and committed contributor5productionpaths1contract; initial vacuous0/0 superseded.'
m['verification']['site_build'] = 'Applicable clean47c6a03f4cb810d0704379ebadb67528633f9244 local source, dirtyfalse/Leanverifiedtrue; site-build/check-v1 only, not deployed.'
m['verification']['site_check'] = 'Actual10906old shared IDs/URLs/statementhashes preserved+7newnodes;12current ROOT and separate FINAL pixel reviews, six exact note/catalogue headers.'
m['graph_contribution']['visual_review'] = 'Actual38selected compiled nodes/32proofs6definitions/16VALUEpairs;7new shared registry nodes; current DOM/pixels/FINAL accepted.'
MANIFEST.write_bytes((json.dumps(m, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    p = Path(folder) / (TASK + '.md')
    p.write_bytes(p.read_bytes() + ('\n\n## Actual bounded package accepted; draft PR delivery pending\n\n' + digest + '\n').encode('utf8'))
write(RUN / '40_reviewer_decision-v1.md', 'Distinct actual source/reader FINAL verdict bound by receipt; formalizer rehashes and records native acceptance, without replacing that reviewer. ' + digest)
write(RUN / 'native-acceptance-overlay-v1.json', dict(status='passed', one_accepted_reviewer_trial=True, obligations_before=6, obligations_after=0,
    obligation_count_scope='Only six frozen derived square-minimum terminals', globalSGB_unchanged=True, PR_delivery_pending=True, **boundary))
accepted_fixed()
print('Only bounded square-minimum source/native package accepted; PR delivery pending; whole-book Goal ACTIVE.')
