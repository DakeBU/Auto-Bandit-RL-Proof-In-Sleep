from common_integrated_v2 import *
r=body_fixed()
write(RUN/'BODY-binding-audit-v2.json',dict(receipt_sha256=sha(RUN/'public-body-receipt-v2.json'),
    report_sha256=r['report_sha256'],fixed_rows=583,all_raw_hashes_match=True,required_reader_corrections=r['required_reader_corrections'],integration_authorized=True))
for p,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingIIDBenchmark\n'),
                   ('Tests.lean',b'\nimport Tests.OnlineGuessingIIDBenchmarkCanary\n')]:
    assert Path(p).read_bytes()==(RUN/'snapshots'/(p+'.raw')).read_bytes()
    Path(p).write_bytes(Path(p).read_bytes()+addition)
boundary=('Only the expected fixed minimum and deterministic finite-history causal IID core is supported here. '
    'Eight actual bodies and distinct BODY review pass; combined root/Tests/harness, committed contributor, shared registry/site/pixels, FINAL/native/draft PR remain separate gates. '
    'Preceding source cards retain their historical package boundaries; this current package closes that deterministic core, while independent external randomization/general filtration and source asymptotic-success equivalence remain REQUIRED. '
    'Original16Chapter1sourceitems/required proof total unknown(null), five older main-relative module audits unwaived, Chapter1open/Chapter2incomplete/Chapters3–16unenumerated/necessaryappendicesrequired/totalGoalACTIVE. '
    'Exact OPENdraft unmerged PR193basebf9f896cdfebb2b836dacb01f3d4b209466c2100 stack is not main/live. No merge/deploy/retirement.')
delta=('Source printed1–2/PDF13–14 motivates squared loss with IID unit targets, cumulative excess (1.1) and average (1.2), and the minimum of EXPECTED FIXED cumulative loss. '
    'Eight derived producer/representation/adapters are not eight printed theorems or new rates. T0 is an explicit empty extension without uniqueness. '
    'Same-law alone suffices for fixed benchmark; deterministic measurable finite-history feasibility is required only on legal unit tuples. The broader all-strategies source claim is not closed by this package.')
model=('On a probability space, each real observation is measurable, a.s. in[0,1], and identically distributed withY0. Produce L2 and the feasible population mean m=E[Y0], then actual IsLeast and sInf. '
    'The comparator u is chosen outside the expectation: B_T=min_{u∈[0,1]}E[Σ(u−Y_t)^2], not E[min_{u∈[0,1]}Σ(u−Y_t)^2]. Generally infinite comparator image, actual attainment established.')
causal=('For causal performance the targets are jointly independent. A measurable policy consumes ONLY the finite strict-past tuple i<t and is feasible on legal tuples. '
    'A.s. history support produces predictionL2 and strict-history independence produces current-target independence. Both are derived, not supplied terminal certificates. '
    'I004 is a supplied-L2/independence consumer only; I005policy and I006meanPredict are the actual producers. Bare definitions and arbitrary supplied traces do not certify causality or nonnegative excess. '
    'Actual meanPredict starts at1/2 then uses the strict-past empirical mean; the constant population mean is a distribution-known oracle, not a learner discovering an unknown law.')
index=('Source rounds1..T correspond to Lean0..T−1 on the SAME prefix. T0 has empty loss/minimum0 without uniqueness; averages require T>0. '
    'Finite normalization does not establish sublinear/vanishing asymptotic success, expected convergence, high probability, or almost-sure guarantees.')
proof=('First prove fixed square-loss expectation decomposition, using a.s. support and same-law integral/variance equality. '
    'Produce the feasible population mean, IsLeast membership and every lower comparison BEFORE applying mathlib csInf_eq. '
    'Independence decomposes each prediction square into variance plus mean-estimation error. Finite integration/summation and the actual same-prefix benchmark yield E-fixed excess=ΣE[(P_t−m)^2]≥0 for each actual causal producer. '
    'The distribution-known constant mean attains zero; the positive-horizon average is exactly cumulative excess/T. No supplied regret/stability/argmin assumption or min/expectation interchange.')
validation=('Actual8public bodies/2definitions,28named canaries/5whole fixtures/2probability instances compile. 53kernel checks use standard axioms only,44theorem-kind constants including2probability proofs/9definition-kind objects; '
    '8neutral-to-draft+8draft-to-actual arbitrary-universe Prop identities/28canaryProps/9wholedefinitions,36native header guards/26compiled direct VALUEpairs pass separately. Safe-verify itself does not compile. '
    'A genuine fair real-coordinate IID infinite product has variance1/4; illegal offsupport paths exist. lastPolicy is legal-input feasible but unbounded offcube, covered by reviewedv2. '
    'T2expected fixed minimum1/2 versus expected hindsight minimum1/4 proves strict noncommutation; actual first-half strict-past meanPredict excess1/4; knownmeanoracle0; deliberately future-aware supplied trace−1/2 is NOT legal. '
    'Distinct staged automated decoder and source reviewer; no human/external/absolute-blind/runtime attestation. Original failure/repair records retained, and no single runtime enforces every ABRL stage.')
math=r'\begin{aligned}m&=\mathbb E[Y_0]\in[0,1],\\B_T&=\min_{u\in[0,1]}\mathbb E\!\left[\sum_{t<T}(u-Y_t)^2\right]=T\operatorname{Var}(Y_0),\\\mathbb E\!\left[\sum_{t<T}(P_t-Y_t)^2\right]-B_T&=\sum_{t<T}\mathbb E[(P_t-m)^2]\ge0,\\P_t&=\pi_t((Y_i)_{i<t}),\\\frac{\mathbb E[\sum_{t<T}(P_t-Y_t)^2]}{T}-\operatorname{Var}(Y_0)&=\frac{\mathbb E[\sum_{t<T}(P_t-Y_t)^2]-B_T}{T}\quad(T>0).\end{aligned}'
card=dict(label='The expected fixed minimum and actual causal IID excess',pages='printed pp.1–2 / PDF pp.13–14: guessing-game IID square loss, equations(1.1)/(1.2), fixed comparator outside expectation',
    pdf_page=13,url='https://arxiv.org/pdf/1912.13213v10',math=math,plain=proof,fallback=proof,relationship=delta,
    contract=dict(model=model,assumptions=model+' '+causal,parameters=index,regret=causal,guarantee=proof+' '+validation+' '+boundary),
    local_status=dict(status='compiled',label='Eight derived expected-fixed/causal IID bodies locally compiled and BODY reviewed; package gates pending',boundary=delta+' '+boundary))
p=Path('website/content/readings.json');data=load(p)
row=next(x for x in data['readings'] if x['slug']==ROUTE)
assert len(row['source_theorems'])==11
row['source_theorems'].append(card)
p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
notes=[
    ('expected_fixed_prefix_decomposition','Expected fixed loss uses only the common law',r'\mathbb E[\sum_{t<T}(u-Y_t)^2]=T\operatorname{Var}(Y_0)+T(u-m)^2.', 'Produce L2 from a.s. support and use same-law moments before finite summation.',['expected_square_decomposition']),
    ('expected_fixed_prefix_minimum','The population mean actually attains the least expected fixed loss',r'm\in[0,1],\quad\operatorname{IsLeast}\{\mathbb E[\sum_{t<T}(u-Y_t)^2]:u\in[0,1]\}\;(T\operatorname{Var}(Y_0)).','Derive actual mean feasibility, image membership and all lower comparisons.',['expected_fixed_prefix_decomposition']),
    ('expectedFixedMinimum_eq_variance','The infimum has the produced variance value',r'B_T=T\operatorname{Var}(Y_0).','Apply csInf_eq only to the already produced IsLeast certificate.',['expected_fixed_prefix_minimum','expectedFixedMinimum']),
    ('iid_cumulative_prediction_decomposition','An intermediate independent-prediction decomposition',r'\mathbb E[\sum_{t<T}(P_t-Y_t)^2]-T\operatorname{Var}(Y_0)=\sum_{t<T}\mathbb E[(P_t-m)^2].','This consumer assumes L2 and current-target independence; actual causal producers follow.',['independent_prediction_square']),
    ('history_policy_expectedFixed_excess','Actual strict-history policies produce nonnegative excess',r'\mathcal E_T(\pi)=\sum_{t<T}\mathbb E[(\pi_t(Y_{<t})-m)^2]\ge0.','Derive a.s. legal histories/L2 and current-target independence from jointIID and strict history.',['expectedFixedMinimum_eq_variance','iid_cumulative_prediction_decomposition','history_policy_independent']),
    ('meanPredict_expectedFixed_excess','The actual first-half mean predictor satisfies the same benchmark',r'\mathcal E_T(x)=\sum_{t<T}\mathbb E[(x_t-m)^2]\ge0,\quad x_0=1/2,\quad x_t=t^{-1}\sum_{i<t}Y_i.','Use actual a.s. feasibility/measurability/strict-past independence without old pointwise strengthening.',['expectedFixedMinimum_eq_variance','iid_cumulative_prediction_decomposition','meanPredict_independent','meanPredict_measurable','meanPredict_mem']),
    ('constant_mean_expectedFixed_excess_zero','The distribution-known mean has zero expected excess',r'm\in[0,1],\quad\mathcal E_T(m)=0.','This known-law oracle attains the produced fixed benchmark; it is not an unknown-law learning algorithm.',['expected_fixed_prefix_minimum','expected_fixed_prefix_decomposition','expectedFixedMinimum_eq_variance']),
    ('history_policy_normalized_expectedFixed_excess','Positive-horizon average and cumulative excess agree',r'\mathbb E[\sum_{t<T}(P_t-Y_t)^2]/T-\operatorname{Var}(Y_0)=\mathcal E_T(P)/T\quad(T>0).','Preserve positive denominator and actual finite prefix; no asymptotic-success theorem follows here.',['expectedFixedMinimum_eq_variance','normalized_excess'])]
p=Path('website/content/highlights.json');data=load(p)
for order,(name,title,formula,idea,parents) in enumerate(notes,70):
    full=PRE+name
    assert not any(x['full_name']==full for x in data['highlights'])
    data['highlights'].append(dict(full_name=full,title=title,chapter=ROUTE,featured=False,teaching_order=order,
        plain=idea,math=formula,intuition='Keep expectation outside the comparator minimum and derive the actual strict-past information condition.',
        why='Connect the source expected fixed benchmark to genuine causal processes.',position=delta,proof_idea=idea,
        lean_notes=model+' '+causal+' '+index+' '+proof+' '+validation+' '+boundary,dependencies=[PRE+n for n in parents]))
p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
p=Path('website/content/chapters.json');data=load(p);row=next(x for x in data['chapters'] if x['slug']==ROUTE)
row['module_globs'].append(PUBLIC.as_posix())
row['completion_blockers']=[boundary,'This is only the deterministic finite-history expected-fixed/causal IID core; all original chapter obligations remain visible.']
row['open_gaps']=[boundary,'Independent external randomization/general filtration and asymptotic-success equivalence remain REQUIRED; no all-strategies/full Chapter1 closure.']
p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
names=[x['name'] for x in load(CONTRACT/'targets-v2.json')['rows']]+[PRE+'expectedFixedMinimum',PRE+'expectedFixedRegret']
reuse=[PRE+x for x in ['expected_square_decomposition','independent_prediction_square','history_policy_independent','meanPredict_independent','meanPredict_measurable','meanPredict_mem','empiricalMean','meanPredict','normalized_excess']]+['IsLeast.csInf_eq','MeasureTheory.memLp_of_bounded','MeasureTheory.integral_finset_sum']
m=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-1',frontier_cell=ROUTE,source_facing=True,
    source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,anchor=card['pages'],url=card['url']),
    target=delta+' '+boundary,affected_files=[PUBLIC.as_posix(),'BanditRLProof.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],declarations=names,
    reuse_plan=dict(classification='missing',decision='new_shared',searched_existing=['Actual native declaration/card/memory and pinned API retrieval in RUN; actual imported declaration/kernel builds.'],
        reused_declarations=reuse,new_shared_declarations=names,known_consumers=[PRE+'history_policy_expectedFixed_excess',PRE+'meanPredict_expectedFixed_excess',TEST+'min_and_expectation_do_not_commute'],
        planned_consumers=[],no_duplicate_wrapper=True,decision_reason='Produce the missing real expected-fixed minimum and a.s.-supported causal endpoints once in the shared library; reuse actual strict-history/moment APIs and generic IsLeast, no per-book project.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict=r['verdict'],
        remaining_semantic_delta=delta+' CONTRACT/BODY accepted; originalR1-R9/FINAL pending. Distinct reused staged automated actors; no human/external/runtime attestation.'),
    graph_contribution=dict(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='One fixed scalar stochastic game and representation/probability proofs, not arbitrary setting composition.',
        focus_targets=[PRE+'expectedFixedMinimum_eq_variance',PRE+'history_policy_expectedFixed_excess',PRE+'meanPredict_expectedFixed_excess'],
        visual_review='Actual53selected compiled nodes/44theoremkind/9definitions and26VALUEpairs; current shared registry/site/pixels pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: one source-qualified expected-fixed/causal IID card/eightproofnotes/module mapping; all11oldcards/oldnotes/curated IDs preserved.',
        banditrlwiki='no-change-with-reason: no new Bandit setting.',results_ledger='updated: eight frozen terminals compile; source16items/proof totalnull and fullChapter1 remain open.',
        roadmap='no-change-with-reason: whole-book sequential Goal remains active/globalSGB unchanged.',website_surfaces=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']),
    truth_boundary=delta+' '+model+' '+causal+' '+index+' '+boundary,
    verification=dict(focused_checks=[validation],bandit_check='New combined root/Tests/full harness required.',site_build='Clean applicable Lean-verified local site after actual combined gates required.',
        site_check='Preserve all10913oldshared IDs/URLs/statementhashes;10newpublicnodes expected; current source/reader/pixels checks required.',
        independent_review='Distinct decoder/CONTRACT/BODY accepted with explicit delta; FINAL/R1-R9 pending.',owned_test_files=[CANARY.as_posix()],owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer/shared integration; distinct required automated decoder and source reviewer'))
write(MANIFEST,m)
fixed_integrated()
write(RUN/'reader-integrated-bindings-v2.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),BODY_receipt_sha256=sha(RUN/'public-body-receipt-v2.json'),
    original_source_cards=11,source_cards=12,new_source_cards=1,new_proof_notes=8,new_public_nodes=10,old_links_preserved=True,required_reader_corrections=r['required_reader_corrections'],chapter_complete=False,goal_complete=False))
print('Actual BODY raw binding verified; shared module/root/Test/sourcecard/eightnotes integrated. Combined gates pending.')
