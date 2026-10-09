from common import *
fixed()
rp = RUN / 'canary-BODY-publication-review-v3.json'
r = load(rp)
assert r['BODY_verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert r['materialization_verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert not r['required_repairs']
assert sha(r['report']) == r['report_sha256']
for row in load(RUN / 'canary-BODY-publication-review-inputs-v3.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
plan = load(CONTRACT / 'exact-publication-plan-v3.json')
assert plan['rows'] == r['approved_five_rows']
write(RUN / 'publication-review-binding-v3.json', dict(
    review_sha256=sha(rp), plan_sha256=sha(CONTRACT / 'exact-publication-plan-v3.json'),
    production_sha256=sha(PUBLIC), Test_sha256=sha(ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'),
    exact_five_rows=plan['rows'], legacy_eight_fields_explicit=True,
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
for row in plan['rows']:
    assert sha(row['path']) == row['before_sha256'] and sha(row['after_snapshot']) == row['after_sha256']
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
from publication_guard_v1 import fixed as published_fixed, CONTRIBUTION, CANARY
published_fixed()
p = load(RUN / 'reader-proposal-v3.json')
d = load(CONTRACT / 'stabilized-v1.json')
names = [t['declaration'] for t in d['targets']]
tests = [t['declaration'] for t in load(CONTRACT / 'canary-stabilized-v1.json')['targets']]
manifest = dict(schema_version='2.0', id=TASK, route='online-learning/chapter-2', frontier_cell='online-ogd', source_facing=True,
    source=dict(kind='book', title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10,2026-06-21; SHA ' + PDF_SHA,
        anchor='Definitions2.18/2.20 and Theorem2.21 printed16–17/PDF28–29; Algorithm15.8/Theorem15.30 proof-step dependency printed265–266/PDF277–278. Derived bridges; full source remains open.',
        url='https://arxiv.org/pdf/1912.13213v10'),
    target='Feasible finite-part convexity, actual EReal proximal minimum equivalence, and signed one-step comparison. ' + p['boundary'],
    affected_files=[PUBLIC.relative_to(ROOT).as_posix(), 'BanditRLProof.lean',
        'website/content/chapters.json', 'website/content/readings.json', 'website/content/highlights.json'],
    declarations=names,
    reuse_plan=dict(classification='adapt', decision='new_shared',
        searched_existing=['Actual pinned API/public declaration retrieval and full generic VALUEs in RUN; accepted shared minimum-order and real nonsmooth proximal APIs. No dependency/toolchain upgrade.'],
        reused_declarations=['BanditRL.OnlineConvex.subgradient_point_finite',
            'BanditRL.OnlineConvex.minOn_finitePart_iff', 'BanditRL.OnlineBregman.proximal_one_step',
            'EReal.coe_toReal', 'EReal.coe_add', 'EReal.toReal_coe'],
        new_shared_declarations=names, known_consumers=tests + [names[2]],
        planned_consumers=['Required attained current-loss causal source producer and same-run sharp fixed/variable telescopes, OPEN.'],
        no_duplicate_wrapper=True,
        decision_reason='Global supports genuinely produce feasible finite-part convexity; the actual EReal objective reuses minimum-order transport and the accepted real proximal theorem. Infinity-domain canaries prove actual minima and consume all three bridges. No assumed desired one-step bound or future-sequence algorithm.'),
    reader_contract=dict(source_anchor_visible=True, natural_language_formula_proof=True,
        hidden_assumptions_visible=True, source_vs_lean_delta_visible=True, lean_folded=True,
        dependencies_visible=True, remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True, status='accepted', formalizer='/root',
        blind_decoder='/root/osd_blind', source_reviewer='/root/source_reviewer',
        verdict='accepted-with-explicit-delta',
        remaining_semantic_delta='Distinct staged CONTRACT/BODY/two exact canary CONTRACT/BODY and version3 reader materialization accepted at SHA-bound inputs. Earlier reader versions rejected and retained; R9/L1 repaired in exact eight legacy fields plus three new notes. ' + p['boundary'] +
            ' Reused related automated actor history disclosed; no human/external/absolute-blind/runtime attestation. FINAL/package acceptance pending.'),
    graph_contribution=dict(lean_graph='new-node', overview_graph='updated',
        functor_hypergraph='none-found-with-reason',
        functor_reason='Finite-part representation and order transport inside one setting, not a newly certified composition of distinct problem models.',
        focus_targets=names,
        visual_review='Actual selected six-node graph: three production proofs, two full canaries and one generated Test auxiliary;1241 coalesced direct TYPE_VALUE presences/12 required VALUE pairs. Two truly selected numeric tails have Eq.mp heads and extended helper VALUE. Complete registry/site/DOM/pixels pending.',
        edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(
        teaching_route='updated: existing online-ogd append one module/goal/completion suffix, one source-qualified card and three production notes; explicit eight legacy minimum/minimizer wording fields corrected. All other fields/IDs/formulas/links and other Books preserved.',
        banditrlwiki='no-change-with-reason: deterministic finite-domain bridges do not change Bandit policies/settings.',
        results_ledger='no-change-with-reason: helper bundle does not accept full source performance or Chapter2; bounded OWN milestone separate.',
        roadmap='no-change-with-reason: all eight Chapter2 forwards/general prescient remain OPEN; whole16Goal ACTIVE, Ch3–16 unenumerated/null; globalSGB unchanged.',
        website_surfaces=['website/content/chapters.json', 'website/content/readings.json', 'website/content/highlights.json']),
    truth_boundary=p['boundary'],
    verification=dict(
        focused_checks=['Actual production focused3297 cached-inclusive jobs0; final Test focused3309jobs0. Five complete generic/public VALUEs, ten standard-only axiom outputs, five frozen headers/native guards. Actual selected6nodes/1241directpresences/12VALUEpairs and two truly selected Eq.mp numeric tails retain public extended helper. Two proof failures/two selector inspection failures and all repairs retained; no type weakening. Four local style warnings plus existing parent warnings retained.'],
        bandit_check='Pending actual combined root/Tests/full tools/bandit.py check; focused builds are separate evidence.',
        site_build='Pending applicable full Lean gate and clean isolated site build; generated website/_site untouched.',
        site_check='Pending complete shared registry and actual browser DOM/geometry/original pixels; no deployed/live claim.',
        independent_review='Distinct staged source/CONTRACT/BODY/canary/reader/exact five-path v3 accepted-with-explicit-delta ' + sha(rp) + '. FINAL/native/postnative/concrete delivery pending.',
        owned_test_files=[CANARY.relative_to(ROOT).as_posix()], owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng', role='Formalizer with distinct staged automated decoder and source reviewer'))
write(CONTRIBUTION, manifest)
write(RUN / 'publication-integrated-v1.json', dict(review_sha256=sha(rp),
    plan_sha256=sha(CONTRACT / 'exact-publication-plan-v3.json'), exact_five_old_transitions_only=True,
    legacy_eight_wording_fields_explicit=True, production_sha256=sha(PUBLIC), test_sha256=sha(CANARY),
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
published_fixed()
print('Exact reviewed five paths and OWN contribution materialized; combined gates pending.')
