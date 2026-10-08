from common_v1 import *

fixed()
blind = load(RUN / 'blind-receipt-v2.json')
assert blind['state'] == 'reconstructed' and blind['inputs_unchanged'] and not blind['blocked']
assert sha(RUN / 'blind-reconstruction-v2.md') == blind['report_sha256']
for row in load(RUN / 'neutral-inputs-v2.json')['rows']:
    assert sha(row['path']) == row['sha256']
assert load(RUN / 'draft-type-verification-v2.json')['arbitrary_universe_prop_identities'] == 7
declarations = load('research-wiki/retrieval-index/local_lean_declarations.json')['declarations']
old = json.loads(subprocess.check_output(['git','show',BASE + ':research-wiki/retrieval-index/local_lean_declarations.json']))['declarations']
assert old == declarations
card_audit=[]
for filename in ['bandit_paper_cards.json', 'bandit_scenario_cards.json', 'bandit_textbook_cards.json',
        'proof_weapon_cards.json']:
    p=Path('research-wiki/retrieval-index') / filename
    prior=json.loads(subprocess.check_output(['git','show',BASE+':'+p.as_posix()]))
    now=load(p)
    assert prior['cards'] == now['cards'], filename
    card_audit.append(dict(path=p.as_posix(), actual_cards_unchanged=True, generated_time_changed=True))
write(RUN / 'old-registry-draft-preservation-v2.json', dict(actual_old_declaration_rows=len(old),
    all_rows_exact_semantic_equal=True, shared_reference_index_timestamp_changed=True,
    four_source_card_indexes=card_audit, local_leaf_new_task_pending_separate_scope=True))
manifest = dict(id='online-randomized-iid-20261008', contribution_type='new-shared',
    task_id=TASK, source='Orabona1912.13213v10 printed1–2/PDF13–14',
    production_files=[PUBLIC.as_posix(), CANARY.as_posix(), 'BanditRLProof.lean', 'Tests.lean',
        'website/content/readings.json', 'website/content/highlights.json', 'website/content/chapters.json'],
    lean_declarations=[r['name'] for r in load(CONTRACT / 'targets-v2.json')['rows']] + [PRE+'privateSeedPastInformation'],
    status='draft', semantic_roundtrip=dict(required=True, status='blind-reconstructed',
        formalizer='/root', blind_decoder='/root/osd_blind', source_reviewer='/root/source_reviewer',
        verdict='pending', remaining_semantic_delta='Whole-process seed independence/subordinate information formulation explicit; no general kernel or completed-field representation; finite IID only.'),
    truth_boundary='Only prospective private-tape/strict-past IID expected-fixed producer; seven unproved draft terminals/one definition. Original16/null/C1C2open/3–16unenumerated/appendices/oldfive/asymptoticrequired/GoalACTIVE. Exact OPENdraftPR194 b08 stack, no main/live/merge/deploy.',
    verification=dict(focused_checks=['Actual seven arbitrary-universe draft-neutral identities and draft/neutral type definitions exit0; no theorem bodies.'],
        full_checks=['NOT RUN for this package'], runtime_model_attested=False, runtime_effort_attested=False))
manifest_path=Path('research-wiki/contribution-contracts/online-randomized-iid-20261008.json')
write(manifest_path,manifest)
write(RUN / 'source-review-packet-v2.md', '''# Anti-anchored contract review v2 — no theorem bodies yet

Act as distinct source reviewer, search for mismatch rather than confirmation. Read exact indexed inputs and verify raw hashes before/after. Frozen Orabona v10 cached PDF hash, source printed1–2/PDF13–14 freshly extracted and exact page pixels supplied; ROOT read/viewed, reviewer must also view source pages. Read contract/targets/public and neutral contexts, actual arbitrary-universe identities, blind reconstruction/receipt, seven reader requirements, operative source-statement-fingerprint-v2.json and proof-obligations-current-draft-v2.json. Preliminary source-fingerprint-v2.json/proof-obligations-draft-v2.json copied stale v1 per-header hashes; explicitly superseded before review by operative corrected files, not silently promoted. Draft v1 Sigma parser/API errors and concatenation universe error retained; only v2 headers/context matter. Native task/conversion/obligations/blueprint now synchronized with actual scope, not template placeholder contracts.

Seven derived producer/interface targets plus one information definition, not seven source theorems. Required causal source hinge: derive current-target independence from WHOLE-process seed independence and joint IID, actual strict past; no given prediction-current independence and no one-step regret certificate. R001 must establish regrouping from joint seed/(past,current) plus past/current independence; individual pairwise seed independence insufficient. R002 must compose whole process extraction; R003 actual monotone generated comap. R004 arbitrary prediction is measurable in subordinate pre-reveal sigma field; R006 still consumes this supplied information-restricted trace, while R007 must instantiate with real joint policy(seed, finite strict past). Need a.s. and legal-cube support only, ambient measurability/L2 produced, exact minE outside expectation, all private randomness integrated by μ, same stream/horizon. Arbitrary seed space/private tape, no representation theorem for every randomized kernel, AE-measurable factorization or completed/augmented sigma fields. Decide whether these explicit deltas make the private-randomized source extension faithful and which full-source obligations remain; do not rubber-stamp 'all algorithms'.

Frozen seven exact header fingerprints cannot change during bodies. Before-proof source approval only, actual theorem bodies/canaries/kernel/root/Tests/fullharness/site/native acceptance/PR delivery require separate BODY/FINAL review. First lower leaf R001, single route. No public body exists; draft Prop definitions do not prove targets. All old tracked Lean files indexed and must remain byte-identical except public root/Tests can later append own single imports; old task contracts/source item count16/proof-totalnull and activeSGBfrontier remain frozen. Own task five metadata after exact snapshots may later append observed proof/evidence status; no source/header/old-math weakening authority. Shared reference indexes may refresh current timestamps/add new declarations/task metadata while preserving every old registry row. New public/Test bodies confined to own new paths; own runtime evidence and website source-qualified card/notes/module mapping require later exact review. No generated _site writes.

Return accepted|rejected|accepted-with-explicit-delta, seven-slot analysis, exact R1–R7 requirements and any repair. Keep requested GPT-6 Astra/medium; staged reused automated reviewer/decoder history disclosed, no human/external/absolute-blind/runtime setting claim. Original16 C1 items/proof-totalnull/C1C2open, source asymptotic-success equivalence, five old main-relative audits, Chapters3–16unenumerated/appendicesrequired/GoalACTIVE. Exact OPENdraft/unmerged PR194 b08 stack, canonical main clean6847, no merge/live/deploy/retirement. Create ONLY new source-contract-review-v2.md and source-contract-receipt-v2.json; include actual input rows pre/post hashes/report rawhash; no other edits or state promotions.
''')
files = []
tracked = subprocess.check_output(['git','ls-files'],encoding='utf8').splitlines()
files += [Path(p) for p in tracked if (p.startswith('BanditRLProof/') or p.startswith('Tests/')) and p.endswith('.lean')]
files += [Path(p) for p in load(RUN / 'draft-baseline-v1.json')['fixed_files']]
files += [Path(p) for p in ['BanditRLProof.lean','Tests.lean','website/content/readings.json',
    'website/content/highlights.json','website/content/chapters.json']]
files += list(CONTRACT.glob('*'))
files += [p for p in RUN.iterdir() if p.is_file()]
files += [Path(d)/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','proof-blueprints']]
files += [manifest_path, Path('research-wiki/retrieval-index/local_lean_declarations.json')]
rows=[]
for p in sorted(set(files)):
    rows.append(dict(path=p.relative_to(ROOT).as_posix() if p.is_absolute() else p.as_posix(),sha256=sha(p)))
write(RUN / 'source-review-inputs-v2.json', dict(schema='abrl.review-inputs.v1', phase='CONTRACT',
    version=2, rows=rows, fixed_input_count=len(rows), root_goal='ACTIVE Chapters1–16',
    permitted_future_edits=['new own public/Test bodies only matching frozen v2 headers/context',
        'root/Tests own import append preserving raw prefix', 'own five metadata status after versioned raw snapshot',
        'own contribution evidence/status after reviewed exact snapshot', 'shared reference-index refresh preserving every old row',
        'new owned source-qualified reader fields only with separate BODY/FINAL review'],
    mathematical_terminals=len(load(CONTRACT / 'targets-v2.json')['rows']), chapter_complete=False,goal_complete=False))
fixed()
print('CONTRACT packet fixed inputs',len(rows),'old Lean registry rows',len(old),'no body proofs.')
