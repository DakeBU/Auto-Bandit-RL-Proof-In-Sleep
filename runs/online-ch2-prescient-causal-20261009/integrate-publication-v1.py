from common import *
fixed()
rp = RUN / 'canary-BODY-publication-review-v1.json'
r = load(rp)
assert r['BODY_verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert r['materialization_verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert not r['required_repairs'] and sha(r['report']) == r['report_sha256']
for row in load(RUN / 'canary-BODY-publication-review-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
plan = load(CONTRACT / 'exact-publication-plan-v2.json')
assert plan['rows'] == r['approved_five_rows']
assert sha(CONTRACT / 'exact-publication-plan-v2.json') == r['approved_plan_sha256']
write(RUN / 'publication-review-binding-v1.json', dict(
    review_sha256=sha(rp), plan_sha256=sha(CONTRACT / 'exact-publication-plan-v2.json'),
    production_sha256=sha(PUBLIC), Test_sha256=sha(ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'),
    exact_five_rows=plan['rows'], all_old_fields_preserved=True,
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
for row in plan['rows']:
    assert sha(row['path']) == row['before_sha256'] and sha(row['after_snapshot']) == row['after_sha256']
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
from publication_guard_v1 import fixed as published_fixed, CONTRIBUTION, CANARY
published_fixed()
p = load(RUN / 'reader-proposal-v2.json')
d = load(CONTRACT / 'stabilized-v1.json')
names = [t['declaration'] for t in d['targets']] + [t['declaration'] for t in d['definitions']]
tests = [t['declaration'] for t in load(CONTRACT / 'canary-stabilized-v1.json')['targets']]
assert len(names) == 10 and len(tests) == 4
manifest = dict(schema_version='2.0', id=TASK, route='online-learning/chapter-2', frontier_cell='online-ogd', source_facing=True,
    source=dict(kind='book', title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10,2026-06-21; SHA ' + PDF_SHA,
        anchor='Chapter2 forward dependency: Definition6.4 printed63-64/PDF75-76; Algorithm15.8/Theorem15.30 printed265-266/PDF277-278. Eight derived proofs/two partial definitions; full source remains open.',
        url='https://arxiv.org/pdf/1912.13213v10'),
    target='Interior-base ambient-extension locality, actual current-loss partial argmin recursion, and signed comparison from its actual consecutive states. ' + p['boundary'],
    affected_files=[PUBLIC.relative_to(ROOT).as_posix(), 'BanditRLProof.lean',
        'website/content/chapters.json', 'website/content/readings.json', 'website/content/highlights.json'],
    declarations=names,
    reuse_plan=dict(classification='adapt', decision='new_shared',
        searched_existing=['Actual pinned Mathlib and public declaration API retrieval in RUN; exact generic VALUEs, Option bind and accepted extended proximal producer. No dependency/toolchain upgrade.'],
        reused_declarations=['Filter.EventuallyEq.fderiv_eq', 'Classical.choose_spec', 'Option.bind',
            'BanditRL.OnlineBregman.proximal_one_step_extended'],
        new_shared_declarations=names, known_consumers=tests + [names[7]],
        planned_consumers=['Required source X/interior-to-valid-run transport and sharp fixed/variable same-run telescopes, OPEN, including fixed-step main-text exercise.'],
        no_duplicate_wrapper=True,
        decision_reason='The actual classical argmin selector and Option recursion produce minima and causal prefix/definedness facts; signed comparison extracts the minimum from actual consecutive states. Four complete canaries consume the actual new producers. No assumed desired one-step bound or future-dependent algorithm.'),
    reader_contract=dict(source_anchor_visible=True, natural_language_formula_proof=True,
        hidden_assumptions_visible=True, source_vs_lean_delta_visible=True, lean_folded=True,
        dependencies_visible=True, remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True, status='accepted', formalizer='/root',
        blind_decoder='/root/osd_blind', source_reviewer='/root/source_reviewer',
        verdict='accepted-with-explicit-delta',
        remaining_semantic_delta='Distinct staged production CONTRACT/BODY, four exact canary CONTRACT/BODY and reader plan-v2 exact five paths accepted at SHA-bound inputs. The neutral SourceClosed context supplement resolved the decoder gap; reports/failures retained. ' + p['boundary'] +
            ' Reused related automated actor history disclosed; no human/external/absolute-blind/runtime attestation. FINAL/package acceptance pending.'),
    graph_contribution=dict(lean_graph='new-node', overview_graph='updated',
        functor_hypergraph='none-found-with-reason',
        functor_reason='Local representative equality and partial-state definedness within one setting do not certify composition of distinct problem models.',
        focus_targets=names,
        visual_review='Actual selected14nodes:10canonical production(8proofs/2defs) and4publicTests;2027 coalesced direct TYPE_VALUE presences,12 required canary VALUE pairs,6 separately audited production VALUE pairs. Both separately selected numeric tails have Eq.mp heads and actual iterate_one_step constants. Complete registry/site/DOM/pixels pending.',
        edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(
        teaching_route='updated: online-ogd appends one module/goal/completion suffix, one source-qualified card and ten canonical production notes. Every old field/formula/link/ID and other Books preserved.',
        banditrlwiki='no-change-with-reason: deterministic prescient partial recursion does not change Bandit policies/settings.',
        results_ledger='no-change-with-reason: bounded derived package does not accept a full source performance theorem or Chapter2; OWN milestone separate.',
        roadmap='no-change-with-reason: all eight Chapter2 forwards/full source and sharp telescopes remain OPEN; whole16Goal ACTIVE, Ch3-16 unenumerated/null; globalSGB unchanged.',
        website_surfaces=['website/content/chapters.json', 'website/content/readings.json', 'website/content/highlights.json']),
    truth_boundary=p['boundary'],
    verification=dict(
        focused_checks=['Actual production focused3298 cached-inclusive jobs0; final Test focused3311jobs0. Twelve complete public proof VALUEs plus two exact definitions;26 standard-only axiom outputs including definitions;12 frozen theorem headers/native guards. Actual selected14nodes/2027directpresences/12canaryVALUEpairs plus6productionpairs and two selected Eq.mp numeric tails retain actual transition. All failed attempts and audit/discovery repairs retained; frozen terminals unchanged. No own final warnings; dependency warnings replayed.'],
        bandit_check='Pending actual combined root/Tests/full tools/bandit.py check; focused builds remain separate evidence.',
        site_build='Pending applicable full Lean gate and clean isolated site build; generated website/_site untouched.',
        site_check='Pending complete shared registry and actual browser DOM/geometry/original pixels; no deployed/live claim.',
        independent_review='Distinct staged source/CONTRACT/BODY/canary and exact five-path plan-v2 materialization accepted-with-explicit-delta ' + sha(rp) + '. FINAL/native/postnative/concrete delivery pending.',
        owned_test_files=[CANARY.relative_to(ROOT).as_posix()], owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng', role='Formalizer with distinct staged automated decoder and source reviewer'))
write(CONTRIBUTION, manifest)
write(RUN / 'publication-integrated-v1.json', dict(review_sha256=sha(rp),
    plan_sha256=sha(CONTRACT / 'exact-publication-plan-v2.json'), exact_five_old_transitions_only=True,
    all_old_fields_preserved=True, production_sha256=sha(PUBLIC), test_sha256=sha(CANARY),
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
published_fixed()
print('Exact reviewed five paths and OWN contribution materialized; combined gates pending.')
