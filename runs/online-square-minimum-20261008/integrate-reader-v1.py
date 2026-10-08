from common_integrated_v1 import *

body_fixed()
r = reviewer_receipt('public-body-receipt-v1.json')
write(RUN / 'BODY-binding-audit-v1.json', dict(receipt_sha256=sha(RUN / 'public-body-receipt-v1.json'),
    report_sha256=r['report_sha256'], fixed_rows=362, all_raw_hashes_match=True,
    required_reader_corrections=r['required_reader_corrections'], integration_authorized=True))
for p, addition in [('BanditRLProof.lean', b'\nimport BanditRLProof.OnlineSquareMinimum\n'),
                    ('Tests.lean', b'\nimport Tests.OnlineSquareMinimumCanary\n')]:
    assert Path(p).read_bytes() == (RUN / 'snapshots' / (p + '.raw')).read_bytes()
    Path(p).write_bytes(Path(p).read_bytes() + addition)
boundary = ('Only the pathwise square-minimum representation hinge is supported here. Six actual bodies and BODY review pass; '
    'combined root/Tests/harness, shared registry/site/pixels, FINAL, native acceptance and draft PR remain separate gates. '
    'Chapter1 remains open:16 source items, required proof total unknown(null), minimum of expected fixed loss and causal IID cumulative variance REQUIRED next; '
    'five older main-relative module audits unwaived. Chapter2 incomplete, Chapters3–16 unenumerated, necessary appendices required, total Goal ACTIVE. '
    'Exact OPENdraft unmerged PR192 base2aa08b9e1f5da4d0c7d7dcbe9ddeadd1fbfc34e3 is a stack, not main/live. No merge/deploy/retirement.')
delta = ('Source printed p2/PDF14 defines pathwise square regret with the minimum over [0,1]; printed p3/PDF15 identifies its actual positive-horizon empirical-mean minimizer; '
    'printed p4/PDF16 Theorem1.3 gives4+4lnT; printed p5/PDF17 retains initial1/4 and source rounds2..T. '
    'Four derived producers/representations/order results plus two literal-minimum adapters are not six printed theorems or new regret-rate mathematics. '
    'T0 is only an explicit library empty-prefix extension without uniqueness; arbitrary supplied prediction identities/order are algebraic generalizations.')
model = ('Real targets y_t lie in[0,1] for exactly t<T. Produce the actual empirical mean and its feasible least square loss, '
    'then identify the real sInf of the generally infinite comparator-loss image. No assumed minimizer or totalized-inf shortcut. '
    'Generic prediction trace need not be feasible/causal; both performance endpoints instead use actual meanPredict: first1/2, then the mean of strict past, independent of comparator and future targets.')
index = ('Source rounds1..T are Lean0..T-1. Both actual performance bounds require T>0. '
    'Refined source sum2..T is range(T-1) with denominator (real t)+2; T1 has empty tail. '
    'Positive-horizon uniqueness uses existing empiricalMean_unique separately; it is not asserted at T0.')
signed = ('Signed best-fixed and comparator regret may be negative. The actual fixed time-only alternating0/1 predictor on an independently fixed matching0/1 target stream '
    'has T2 best regret -1/2. This finite pathwise example proves no IID excess-risk claim, nonnegativity, ordinary convergence or rate by itself. '
    'Printed p1–2 minimum of EXPECTED FIXED loss and causal cumulative IID variance benchmark remain required next; never exchange expectation and hindsight minimum.')
proof = ('Existing empiricalMean_mem/minimizes produce feasibility and leastness on the same prefix. M002 proves IsLeast membership and every lower comparison, '
    'then imports mathlib IsLeast.csInf_eq. Unfolding gives exact same-process squaredBestRegret=comparatorRegret at the produced mean. '
    'Subtracting the least comparator loss proves every feasible comparator regret is at most this best-fixed regret. '
    'Apply actual theorem_1_3 and meanPredict_regret_refined to this identity; no supplied stability/regret certificate or arbitrary future-aware algorithm.')
validation = ('Actual6 public bodies/1definition and20named canaries/2time-only fixtures compile. '
    '38kernel checks use standard axioms only;6neutral-to-draft/6draft-to-actual public Prop identities,20actualcanary types and6whole definitions compile separately. '
    '26native header guards and16compiled VALUE occurrences pass; safe-verify itself does not compile. '
    'Varying0/1 targets give mean1/2/minimum1/2 and actual FTL regrets1/4 atT1,3/4 atT2; nonbinary1/4,3/4 data give mean1/2/minimum1/8. '
    'Distinct required decoder reconstructs; source reviewer separately accepts CONTRACT/BODY with explicit delta. Staged history disclosed; no human/external/absolute-blind/runtime attestation. '
    'The full workflow is not enforced by one runtime command.')
math = r'\begin{aligned}m_T&=T^{-1}\sum_{t<T}y_t\in[0,1]\quad(T>0),\\B_T&=\min_{u\in[0,1]}\sum_{t<T}(u-y_t)^2=\sum_{t<T}(m_T-y_t)^2,\\R_T^{\mathrm{best}}(x)&=\sum_{t<T}(x_t-y_t)^2-B_T=R_T(m_T),\\R_T(u)&\le R_T^{\mathrm{best}}(x)\quad(u\in[0,1]),\\x_0&=1/2,\quad x_t=m_t\quad(t>0),\\R_T^{\mathrm{best}}(x)&\le4+4\log T\quad(T>0),\\R_T^{\mathrm{best}}(x)&\le1/4+\sum_{t=0}^{T-2}4/(t+2)\quad(T>0).\end{aligned}'
card = dict(label='The attained square-loss minimum and actual FTL best-fixed regret',
    pages='printed pp.2–5 / PDF pp.14–17: pathwise minimum, actual mean, Theorem1.3 and refined proof bound',
    pdf_page=14, url='https://arxiv.org/pdf/1912.13213v10', math=math, plain=proof, fallback=proof,
    relationship=delta, contract=dict(model=model, assumptions=model, parameters=index, regret=signed,
        guarantee=proof + ' ' + validation + ' ' + boundary),
    local_status=dict(status='compiled', label='Six derived square-minimum bodies locally compiled and BODY reviewed; package gates pending',
        boundary=delta + ' ' + signed + ' ' + boundary))
p = Path('website/content/readings.json'); data = load(p)
row = next(x for x in data['readings'] if x['slug'] == ROUTE)
assert len(row['source_theorems']) == 10
row['source_theorems'].append(card)
p.write_bytes((json.dumps(data, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
notes = [
    ('guessing_prefix_minimum', 'The empirical mean is an actual feasible minimum',
     r'm_T\in[0,1],\quad\sum_{t<T}(m_T-y_t)^2\le\sum_{t<T}(u-y_t)^2\quad(u\in[0,1]).',
     'Use actual mean feasibility and global minimization; split T0 only for the explicit empty prefix.', ['empiricalMean_mem', 'empiricalMean_minimizes']),
    ('squaredLoss_minimum_eq', 'The literal minimum value is produced',
     r'\inf\{\sum_{t<T}(u-y_t)^2:u\in[0,1]\}=\sum_{t<T}(m_T-y_t)^2.',
     'Construct an IsLeast witness including image membership and all lower comparisons before applying mathlib csInf_eq.', ['guessing_prefix_minimum']),
    ('squaredBestRegret_eq_comparatorRegret', 'The same losses have the same best-comparator regret',
     r'R_T^{\mathrm{best}}(x)=R_T(m_T).',
     'Unfold both signed quantities and rewrite the proved attained minimum; arbitrary supplied traces are algebraic inputs.', ['squaredLoss_minimum_eq', 'squaredBestRegret', 'comparatorRegret']),
    ('comparatorRegret_le_squaredBestRegret', 'Every feasible comparator is ordered against that minimum',
     r'R_T(u)\le R_T^{\mathrm{best}}(x)\quad(u\in[0,1]).',
     'The same prediction cost minus a larger comparator loss is at most the cost minus its produced least loss.', ['guessing_prefix_minimum', 'squaredBestRegret_eq_comparatorRegret']),
    ('meanPredict_bestRegret_bound', 'Theorem1.3 uses the literal best-fixed benchmark',
     r'R_T^{\mathrm{best}}(x)\le4+4\log T\quad(T>0).',
     'Transport the existing actual first-half strict-past mean predictor proof through the same-process identity.', ['squaredBestRegret_eq_comparatorRegret', 'theorem_1_3']),
    ('meanPredict_bestRegret_refined', 'The initial quarter and exact later-round tail remain visible',
     r'R_T^{\mathrm{best}}(x)\le1/4+\sum_{t=0}^{T-2}4/(t+2)\quad(T>0).',
     'Transport the actual refined FTL proof; first1/2, positive T and source rounds2..T are unchanged.', ['squaredBestRegret_eq_comparatorRegret', 'meanPredict_regret_refined'])]
p = Path('website/content/highlights.json'); data = load(p)
for order, (name, title, formula, idea, parents) in enumerate(notes, 60):
    full = PRE + name
    assert not any(x['full_name'] == full for x in data['highlights'])
    data['highlights'].append(dict(full_name=full, title=title, chapter=ROUTE, featured=False, teaching_order=order,
        plain=idea, math=formula, intuition='Keep the actual attained minimum and the same finite prediction process together.',
        why='Make the printed best-fixed benchmark explicit instead of assuming a minimizing certificate.', position=delta,
        proof_idea=idea, lean_notes=model + ' ' + index + ' ' + signed + ' ' + proof + ' ' + validation + ' ' + boundary,
        dependencies=[PRE + n for n in parents]))
p.write_bytes((json.dumps(data, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
p = Path('website/content/chapters.json'); data = load(p)
row = next(x for x in data['chapters'] if x['slug'] == ROUTE)
row['module_globs'].append(PUBLIC.as_posix())
row['completion_blockers'] = [boundary, 'The original source cards and old registry links are preserved; this package closes only one pathwise minimum subobligation.']
row['open_gaps'] = [boundary, 'Expected fixed-loss minimum and its causal IID cumulative variance producer remain required; no min/expectation interchange is proved.']
p.write_bytes((json.dumps(data, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
names = [x['name'] for x in load(CONTRACT / 'targets-v1.json')['rows']] + [PRE + 'squaredBestRegret']
m = dict(schema_version='2.0', id=TASK, route='online-learning/chapter-1', frontier_cell=ROUTE, source_facing=True,
    source=dict(kind='book', title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10,2026-06-21; SHA ' + PDF_SHA, anchor=card['pages'], url=card['url']),
    target=delta + ' ' + boundary,
    affected_files=[PUBLIC.as_posix(), 'BanditRLProof.lean', 'website/content/readings.json', 'website/content/highlights.json', 'website/content/chapters.json'],
    declarations=names,
    reuse_plan=dict(classification='missing', decision='new_shared', searched_existing=['Actual native declaration/card/memory retrieval and imported pinned API compilation in RUN.'],
        reused_declarations=[PRE + x for x in ['empiricalMean_mem', 'empiricalMean_minimizes', 'empiricalMean_unique', 'empiricalMean', 'meanPredict', 'meanPredict_prefix', 'comparatorRegret', 'theorem_1_3', 'meanPredict_regret_refined']] + ['IsLeast.csInf_eq'],
        new_shared_declarations=names, known_consumers=[PRE + 'meanPredict_bestRegret_bound', PRE + 'meanPredict_bestRegret_refined', TEST + 'signed_alternating'],
        planned_consumers=[], no_duplicate_wrapper=True,
        decision_reason='Produce the missing literal interval minimum once in the shared library; reuse actual mean/projection-independent FTL and generic IsLeast API. No per-book project or duplicate generic infimum theory.'),
    reader_contract=dict(source_anchor_visible=True, natural_language_formula_proof=True, hidden_assumptions_visible=True,
        source_vs_lean_delta_visible=True, lean_folded=True, dependencies_visible=True, remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True, status='accepted', formalizer='/root', blind_decoder='/root/osd_blind', source_reviewer='/root/source_reviewer',
        verdict=r['verdict'], remaining_semantic_delta=delta + ' ' + signed + ' CONTRACT/BODY accepted; original R1-R8/FINAL pending. Distinct reused staged automated actors, no human/external/runtime attestation.'),
    graph_contribution=dict(lean_graph='new-node', overview_graph='updated', functor_hypergraph='none-found-with-reason',
        functor_reason='Same scalar pathwise process and representation identity, not a certified cross-setting theorem.',
        focus_targets=[PRE + 'squaredLoss_minimum_eq', PRE + 'meanPredict_bestRegret_refined'],
        visual_review='Actual38compiled selected nodes/32proofs/6definitions and16VALUE pairs; current shared registry/site/pixels pending.', edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: append one source-qualified minimum/FTL card and six actual proof notes/module mapping; preserve10old cards, all old notes and curated IDs.',
        banditrlwiki='no-change-with-reason: no new Bandit setting.', results_ledger='updated: six exact pathwise-minimum terminals compile; chapter1 proof total remains unknown and expected benchmark required.',
        roadmap='no-change-with-reason: whole-book order and total Goal remain active; globalSGB unchanged.',
        website_surfaces=['website/content/readings.json', 'website/content/highlights.json', 'website/content/chapters.json']),
    truth_boundary=delta + ' ' + model + ' ' + index + ' ' + signed + ' ' + boundary,
    verification=dict(focused_checks=[validation], bandit_check='New combined root/Tests/full harness required.',
        site_build='Clean applicable Lean-verified local site after actual combined gates required.',
        site_check='Preserve all10906old shared IDs/URLs/statement hashes;7new public nodes expected, current source/reader/pixels checks required.',
        independent_review='Distinct decoder reconstructs; CONTRACT/BODY accepted with explicit delta; FINAL/R1-R8 pending.',
        owned_test_files=[CANARY.as_posix()], owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng', role='Formalizer/shared integration; distinct required automated decoder and source reviewer'))
write(MANIFEST, m)
fixed_integrated()
write(RUN / 'reader-integrated-bindings-v1.json', dict(public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY),
    BODY_receipt_sha256=sha(RUN / 'public-body-receipt-v1.json'), original_source_cards=10, source_cards=11,
    new_source_cards=1, new_proof_notes=6, new_production_nodes=7, preserved_curated_IDs=True,
    required_reader_corrections=r['required_reader_corrections'], chapter_complete=False, goal_complete=False))
print('BODY raw bindings verified; one shared module/root/test, source card and six notes integrated. Combined gates pending.')
